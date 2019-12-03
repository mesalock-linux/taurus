use rustc::hir::def_id::DefId;
use rustc::ty::subst::SubstsRef;
use rustc::ty::{Ty, TyCtxt};
use syntax::source_map::SourceMap;
use syntax_pos::Loc;

#[cfg(feature = "use_sqlite")]
use rusqlite::types::ToSql;
#[cfg(feature = "use_sqlite")]
use rusqlite::{Connection, MappedRows, Statement, NO_PARAMS};

#[cfg(feature = "use_sled")]
use sled::Db;

use std::collections::HashMap;
use std::path::Path;
use std::rc::Rc;

extern crate fs2;
extern crate serde;

use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::utils::*;

pub const FNPTR_DEF_NAME_CANONICAL: &'static str = "@fnptr";

pub struct Canonical<'tcx, 'rtcx>
where
    'tcx: 'rtcx,
{
    tcx: &'rtcx TyCtxt<'tcx>,
    source_map: Rc<SourceMap>,
}

impl<'tcx, 'rtcx> Canonical<'tcx, 'rtcx> {
    pub fn new(tcx: &'rtcx TyCtxt<'tcx>, source_map: Rc<SourceMap>) -> Self {
        Self { tcx, source_map }
    }

    pub fn tcx(&self) -> &'rtcx TyCtxt<'tcx> {
        self.tcx
    }

    pub fn source_map(&self) -> &Rc<SourceMap> {
        &self.source_map
    }

    pub fn monoitem_name(&self, def_id: DefId, substs: SubstsRef<'tcx>) -> String {
        let mut def_name = self.def_name(def_id);
        def_name.push('<');
        for ty in substs.types() {
            append_mangled_type(&mut def_name, ty, self.tcx);
            def_name.push(',');
        }
        def_name.push('>');
        def_name
    }

    pub fn normalized_type_name(&self, ty: Ty<'tcx>) -> String {
        let mut ret = String::new();
        append_mangled_type(&mut ret, ty, self.tcx);
        ret
    }

    pub fn def_name(&self, def_id: DefId) -> String {
        qualified_type_name(self.tcx, def_id)
    }
}

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct SourceLocation {
    pub file: String,
    pub line_no: usize,
}

impl std::fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.file, self.line_no)
    }
}

#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Debug)]
pub struct Marking {
    pub require_audit: Option<String>,
    pub audited: Option<String>,
    pub is_entry_point: bool,
}

impl Marking {
    pub fn annotated(&self) -> bool {
        self.is_entry_point || self.require_audit.is_some() || self.audited.is_some()
    }
}

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct MarkedItem {
    pub marking: Marking,
    pub src_loc: SourceLocation,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct DepEdge {
    pub callee_def: String,
    pub is_lang_item: bool,
    pub type_params: Vec<String>,
    pub src_loc: SourceLocation,
}

impl DepEdge {
    pub fn full_callee_name(&self) -> String {
        let mut ret = self.callee_def.clone();
        ret.push('<');
        for ty_param in &self.type_params {
            ret.push_str(&ty_param);
            ret.push(',');
        }
        ret.push('>');
        ret
    }
}

impl From<&Loc> for SourceLocation {
    fn from(loc: &Loc) -> Self {
        Self {
            file: loc.file.name.to_string(),
            line_no: loc.line,
        }
    }
}

#[cfg(feature = "use_sqlite")]
pub struct PersistentSummaryStore<V>
where
    V: Serialize + DeserializeOwned,
{
    persist_store: Connection,
    inmem_store: HashMap<String, V>,
}

#[cfg(feature = "use_sqlite")]
impl<V> PersistentSummaryStore<V>
where
    V: Serialize + DeserializeOwned,
{
    pub fn new(persist_db_path: &Path) -> rusqlite::Result<Self> {
        if !persist_db_path.exists() {
            std::fs::create_dir_all(persist_db_path)
                .map_err(|_| rusqlite::Error::InvalidPath(persist_db_path.to_owned()))?;
        }

        let persist_store = Connection::open(&persist_db_path.join("db"))?;

        persist_store.execute(
            "CREATE TABLE IF NOT EXISTS data (
                  key              TEXT NOT NULL PRIMARY KEY,
                  value            BLOB NOT NULL
             ) WITHOUT ROWID",
            NO_PARAMS,
        )?;

        Ok(Self {
            persist_store,
            inmem_store: HashMap::new(),
        })
    }

    pub fn insert(&mut self, k: String, v: V) -> Option<V> {
        let persist_val = bincode::serialize(&v).unwrap();
        self.persist_store
            .execute(
                "INSERT OR REPLACE INTO data(key, value) values(?1, ?2)",
                &[&k as &ToSql, &persist_val],
            )
            .unwrap();
        self.inmem_store.insert(k, v)
    }

    pub fn for_each<F: FnMut((String, V)) -> ()>(&self, f: F) {
        let mut stmt = self.persist_store.prepare("SELECT * FROM data").unwrap();
        let iter = stmt
            .query_map(NO_PARAMS, |row| {
                let val: Vec<u8> = row.get(1).unwrap();
                Ok((row.get(0).unwrap(), bincode::deserialize(&val).unwrap()))
            })
            .unwrap();
        iter.for_each(|r| f(r.unwrap()))
    }
}

#[cfg(feature = "use_sled")]
pub struct PersistentSummaryStore<V>
where
    V: Serialize + DeserializeOwned,
{
    persist_store: Db,
    inmem_store: HashMap<String, V>,
}

#[cfg(feature = "use_sled")]
impl<V> PersistentSummaryStore<V>
where
    V: Serialize + DeserializeOwned,
{
    pub fn new(persist_db_path: &Path) -> std::io::Result<Self> {
        if !persist_db_path.exists() {
            std::fs::create_dir_all(persist_db_path).map_err(|_| {
                std::io::Error::new(std::io::ErrorKind::NotFound, "invalid db directory")
            })?;
        }

        // Need a strategy here to avoid sled racing. For now, just make sure
        // cargo is invoked with `-j 1`
        let persist_store = Db::open(persist_db_path.clone()).unwrap();

        Ok(Self {
            persist_store,
            inmem_store: HashMap::new(),
        })
    }

    pub fn insert(&mut self, k: String, v: V) -> Option<V> {
        let persist_val = bincode::serialize(&v).unwrap();
        self.persist_store
            .insert(k.as_bytes(), persist_val)
            .unwrap();
        self.inmem_store.insert(k, v)
    }

    pub fn for_each<F: FnMut((String, V)) -> ()>(&self, f: F) {
        self.persist_store
            .iter()
            .map(|result| {
                let (key, value) = result.unwrap();
                (
                    String::from_utf8(key.to_vec()).unwrap(),
                    bincode::deserialize::<V>(&value).unwrap(),
                )
            })
            .for_each(f);
    }

    pub fn get<T: AsRef<str>>(&self, key: T) -> Option<V> {
        self.persist_store
            .get(key.as_ref())
            .unwrap()
            .map(|bin| bincode::deserialize::<V>(&bin).unwrap())
    }

    pub fn len(&self) -> usize {
        self.persist_store.len()
    }
}
