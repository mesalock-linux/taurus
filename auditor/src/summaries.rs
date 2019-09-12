use rustc::hir::def_id::DefId;
use rustc::hir::map::DefPathData;
use rustc::ty::subst::SubstsRef;
use rustc::ty::TyCtxt;
use syntax::source_map::SourceMap;
use syntax_pos::Loc;

#[cfg(feature = "use_sqlite")]
use rusqlite::types::ToSql;
#[cfg(feature = "use_sqlite")]
use rusqlite::{Connection, MappedRows, Statement, NO_PARAMS};

#[cfg(feature = "use_sled")]
use sled::{ConfigBuilder, Db};

use std::collections::HashMap;
use std::path::Path;
use std::rc::Rc;

extern crate fs2;
extern crate serde;

use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::utils::*;

pub const FNPTR_DEF_NAME_CANONICAL: &'static str = "@fnptr";

pub struct Canonical<'a, 'gcx: 'tcx, 'tcx: 'a, 'rtcx>
where
    'tcx: 'rtcx,
{
    tcx: &'rtcx TyCtxt<'a, 'gcx, 'tcx>,
    source_map: Rc<SourceMap>,
}

impl<'a, 'gcx, 'tcx, 'rtcx> Canonical<'a, 'gcx, 'tcx, 'rtcx> {
    pub fn new(tcx: &'rtcx TyCtxt<'a, 'gcx, 'tcx>, source_map: Rc<SourceMap>) -> Self {
        Self {
            tcx,
            source_map,
        }
    }

    pub fn tcx(&self) -> &'rtcx TyCtxt<'a, 'gcx, 'tcx> {
        self.tcx
    }

    pub fn source_map(&self) -> &Rc<SourceMap> {
        &self.source_map
    }

    pub fn monoitem_name(&self, def_id: DefId, substs: SubstsRef<'tcx>) -> String {
        let mut def_name = self.def_name(def_id);
        append_type_args_name(&mut def_name, self.tcx, substs);
        def_name
    }

    pub fn def_name(&self, def_id: DefId) -> String {
        let mut name = self
            .tcx
            .crate_name(def_id.krate)
            .as_interned_str()
            .as_str()
            .to_string();
        for component in &self.tcx.def_path(def_id).data {
            name.push_str("::");
            use DefPathData::*;
            match &component.data {
                TypeNs(n) | ValueNs(n) | LifetimeNs(n) | MacroNs(n) | GlobalMetaData(n) => {
                    name.push_str(&n.as_str());
                }
                _ => name.push_str(match &component.data {
                    CrateRoot => "crate_root",
                    Impl => "impl",
                    Misc => "misc",
                    ClosureExpr => "closure",
                    Ctor => "ctor",
                    AnonConst => "const",
                    ImplTrait => "impl_trait",
                    _ => unreachable!(),
                }),
            };
            name.push('[');
            name.push_str(component.disambiguator.to_string().as_str());
            name.push(']');
        }
        name
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct SourceLocation {
    pub file: String,
    pub line_no: usize,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct CallEdge {
    pub callee_name: String,
    pub callee_def: String,
    pub is_lang_item: bool,
    pub type_params: Vec<String>,
    pub src_loc: SourceLocation,
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
        let config = ConfigBuilder::new().path(persist_db_path.clone()).build();
        let persist_store = Db::start(config).unwrap();

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
}
