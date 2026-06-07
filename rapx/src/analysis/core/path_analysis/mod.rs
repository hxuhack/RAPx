pub mod default;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;

pub type PathSet = Vec<Vec<usize>>;
pub type PathMap = FxHashMap<DefId, PathSet>;
