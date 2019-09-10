use rustc::hir::def_id::{DefId, LOCAL_CRATE};
use rustc::hir::map::DefPathData;
use rustc::ty::print::with_crate_prefix;
use rustc::ty::TyCtxt;
use syntax::source_map::SourceMap;
use syntax_pos::Loc;

use rusqlite::types::ToSql;
use rusqlite::{Connection, NO_PARAMS};

use std::collections::HashMap;
use std::path::Path;
use std::rc::Rc;

extern crate fs2;
extern crate serde;

use serde::de::DeserializeOwned;
use serde::Serialize;

pub const FNPTR_DEF_NAME_CANONICAL: &'static str = "@fnptr";

pub struct Canonical<'a, 'gcx: 'tcx, 'tcx: 'a, 'rtcx>
where
    'tcx: 'rtcx,
{
    tcx: &'rtcx TyCtxt<'a, 'gcx, 'tcx>,
    crate_name: String,
    source_map: Rc<SourceMap>,
}

impl<'a, 'gcx, 'tcx, 'rtcx> Canonical<'a, 'gcx, 'tcx, 'rtcx> {
    pub fn new(tcx: &'rtcx TyCtxt<'a, 'gcx, 'tcx>, source_map: Rc<SourceMap>) -> Self {
        let crate_name = tcx
            .crate_name(LOCAL_CRATE)
            .as_interned_str()
            .as_str()
            .to_string();

        Self {
            tcx,
            crate_name,
            source_map,
        }
    }

    pub fn tcx(&self) -> &'rtcx TyCtxt<'a, 'gcx, 'tcx> {
        self.tcx
    }

    pub fn source_map(&self) -> &Rc<SourceMap> {
        &self.source_map
    }

    pub fn monoitem_name<T: std::fmt::Display>(&self, inst: &T) -> String {
        const CRATE_PREFIX: &'static str = "crate::";
        const VALID_RUST_IDENT_CHAR: &'static str =
            "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";

        let plain = with_crate_prefix(|| format!("{}", inst));
        let mut replace_points = plain.match_indices(CRATE_PREFIX).filter(|(idx, _)| {
            let i = *idx;
            i == 0usize
                || VALID_RUST_IDENT_CHAR
                    .find(plain.get(i - 1..i).unwrap())
                    .is_none()
        });

        match replace_points.next() {
            None => plain,
            Some((first, _)) => {
                let crate_prefix_len = CRATE_PREFIX.len();
                let mut ret = String::new();
                ret.push_str(plain.get(..first).unwrap());
                let mut prev = first;
                for (i, _) in replace_points {
                    ret.push_str(&self.crate_name);
                    ret.push_str("::");
                    prev += crate_prefix_len;
                    ret.push_str(plain.get(prev..i).unwrap());
                    prev = i;
                }
                ret.push_str(&self.crate_name);
                ret.push_str("::");
                prev += crate_prefix_len;
                ret.push_str(plain.get(prev..).unwrap());
                ret
            }
        }
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

pub struct PersistentSummaryStore<V>
where
    V: Serialize + DeserializeOwned,
{
    persist_store: Connection,
    inmem_store: HashMap<String, V>,
}

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
        self.persist_store.execute(
            "INSERT OR REPLACE INTO data(key, value) values(?1, ?2)",
            &[&k as &ToSql, &persist_val],
        ).unwrap();
        self.inmem_store.insert(k, v)
    }

    pub fn for_each<F: FnMut((String, V)) -> ()>(&self, mut f: F) {
        let mut stmt = self.persist_store.prepare("SELECT * FROM data").unwrap();
        let iter = stmt.query_map(NO_PARAMS, |row| {
            let val: Vec<u8> = row.get(1).unwrap();
            Ok((
                row.get(0).unwrap(),
                bincode::deserialize(&val).unwrap(),
            ))
        }).unwrap();
        iter.for_each(|r| f(r.unwrap()))
    }
}
