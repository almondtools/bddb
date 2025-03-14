use std::hash::BuildHasherDefault;
use std::sync::Arc;

use oxidd::bdd::BDDManagerRef;
use oxidd::util::{FxHasher, SatCountCache};

use super::counter::ShiftCounter;
use super::domain::{BDDDomain, Domain};
use super::relation::BDDRelationDef;

pub struct BDDBManager {
  manager: BDDManagerRef,
  count_cache: Option<SatCountCache<ShiftCounter, BuildHasherDefault<FxHasher>>>,
}

impl BDDBManager {
  pub fn new(inodes: usize, apply_cache: usize, threads: u32) -> BDDBManager {
    let manager = oxidd::bdd::new_manager(inodes, apply_cache, threads);
    let count_cache = None;
    BDDBManager { manager, count_cache }
  }

  pub fn manager(&self) -> &BDDManagerRef {
    &self.manager
  }

  pub fn cache_count(&mut self) -> &mut SatCountCache<ShiftCounter, BuildHasherDefault<FxHasher>> {
    self.count_cache.get_or_insert_default()
  }

  pub fn domain(&self, name: Arc<str>, size: u128) -> Domain {
    Domain::new(self.manager.clone(), name, size)
  }

  pub fn relation(&self, name: impl Into<Arc<str>>, domains: Vec<Arc<BDDDomain>>) -> BDDRelationDef {
    let name = name.into();
    let manager = self.manager.clone();
    BDDRelationDef::new(name, manager, domains)
  }
}
