use rustc::hir::def_id::{DefId, LOCAL_CRATE};
use rustc::hir::map::DefPathData;
use rustc::ty::TyCtxt;
use rustc::ty::print::with_crate_prefix;
use syntax::source_map::SourceMap;
use syntax_pos::Loc;

use sled::{ConfigBuilder, Db};

use std::path::Path;
use std::io::{Error, ErrorKind};
use std::collections::HashMap;
use std::rc::Rc;

extern crate fs2;
extern crate serde;

use serde::Serialize;
use serde::de::DeserializeOwned;

pub struct Canonical<'a, 'gcx: 'tcx, 'tcx: 'a, 'rtcx>
where
    'tcx: 'rtcx
{
    tcx: &'rtcx TyCtxt<'a, 'gcx, 'tcx>,
    crate_name: String,
    source_map: Rc<SourceMap>,
}

impl<'a, 'gcx, 'tcx, 'rtcx> Canonical<'a, 'gcx, 'tcx, 'rtcx> {
    pub fn new(tcx: &'rtcx TyCtxt<'a, 'gcx, 'tcx>, source_map: Rc<SourceMap>) -> Self {
        let crate_name = tcx.crate_name(LOCAL_CRATE)
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
        let mut replace_points =
            plain.match_indices(CRATE_PREFIX).filter(|(idx, _)| {
                let i = *idx;
                i == 0usize || VALID_RUST_IDENT_CHAR.find(plain.get(i-1..i).unwrap()).is_none()
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
        let mut name = self.tcx.crate_name(def_id.krate)
            .as_interned_str()
            .as_str()
            .to_string();
        for component in &self.tcx.def_path(def_id).data {
            name.push_str("::");
            use DefPathData::*;
            match &component.data {
                TypeNs(n)
                | ValueNs(n)
                | LifetimeNs(n)
                | MacroNs(n)
                | GlobalMetaData(n) => {
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
    persist_store: Db,
    inmem_store: HashMap<String, V>,
}

impl<V> PersistentSummaryStore<V>
where
    V: Serialize + DeserializeOwned
{
    pub fn new(persist_db_path: &Path) -> std::io::Result<Self> {
        if !persist_db_path.exists() {
            std::fs::create_dir_all(persist_db_path)
                .map_err(|_| Error::new(ErrorKind::NotFound, "invalid db directory"))?;
        }

        let mut lock_file_options = std::fs::OpenOptions::new();
        lock_file_options.create(true).write(true);

        let db_config = lock_file_options.open(&persist_db_path.join("db.lock"))
            .and_then(|file| {
                use fs2::FileExt;
                file.lock_exclusive()?;
                let config = ConfigBuilder::new()
                    .path(persist_db_path.clone())
                    .build();
                file.unlock()?;
                Ok(config)
            })?;

        // initialize the in-mem store at start up
        let persist_store = Db::start(db_config).unwrap();
        let mut inmem_store: HashMap<String, V> = HashMap::new();
        for read_result in persist_store.iter() {
            let db_corrupted = "db corrupted";
            let (key_bin, val_bin) = read_result.expect(db_corrupted);
            let key = std::str::from_utf8(&key_bin).expect(db_corrupted);
            let val = bincode::deserialize(&val_bin).expect(db_corrupted);
            inmem_store.insert(key.to_string(), val);
        }

        Ok(Self {
            persist_store,
            inmem_store,
        })
    }

    pub fn insert(&mut self, k: String, v: V) -> Option<V> {
        let persist_val = bincode::serialize(&v).ok()?;
        self.persist_store.insert(k.as_bytes(), persist_val).ok()?;
        self.inmem_store.insert(k, v)
    }

    pub fn get(&mut self, k: &String) -> Option<&V> {
        if !self.inmem_store.contains_key(k) {
            if let Ok(Some(ser_val)) = self.persist_store.get(k.as_bytes()) {
                let val = bincode::deserialize(&*ser_val).ok()?;
                self.inmem_store.insert(k.clone(), val)?;
            } else {
                return None;
            }
        }
        self.inmem_store.get(k)
    }
}
