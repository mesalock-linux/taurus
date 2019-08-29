use std::path::{Path, PathBuf};

pub struct TaurusAnalyzer {
    db_path: PathBuf,
}

impl TaurusAnalyzer {
    pub fn new(db_path: &Path) -> Self {
        Self {
            db_path: db_path.into(),
        }
    }
}
