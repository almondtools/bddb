use std::cmp::Ordering;
use std::collections::{BTreeSet, VecDeque};
use std::fmt::{self, Debug};
use std::hash::BuildHasher;
use std::sync::Arc;

use oxidd::bdd::{BDDFunction, BDDManagerRef};
use oxidd::util::{AllocResult, SatCountCache};
use oxidd::{BooleanFunction, BooleanFunctionQuant, Manager, ManagerRef};

use super::counter::ShiftCounter;
pub enum DomainSource {
  Set(BTreeSet<Arc<str>>),
}

impl DomainSource {
  pub fn set_of(args: Vec<impl Into<Arc<str>>>) -> DomainSource {
    let args = args.into_iter().map(|s| s.into()).collect();
    DomainSource::Set(args)
  }

  pub fn size(&self) -> u128 {
    let DomainSource::Set(set) = self;
    set.len() as u128
  }

  pub fn value(&self, val: &str) -> u128 {
    let DomainSource::Set(set) = self;
    let key = Arc::from(val);
    set.range(..key).count() as u128
  }

  pub fn invert(&self, index: u128) -> &str {
    let DomainSource::Set(set) = self;
    let val = set.iter().nth(index as usize).unwrap();
    val.as_ref()
  }
}

#[derive(Clone)]
pub struct Domain {
  manager: BDDManagerRef,
  name: Arc<str>,
  size: u128,
  domains: Vec<Arc<BDDDomain>>,
  uri: Option<Arc<str>>,
}

impl Domain {
  pub fn new(manager: BDDManagerRef, name: Arc<str>, size: u128) -> Domain {
    let domains = Vec::new();
    let uri = None;
    Domain { manager, name, size, domains, uri }
  }

  pub fn loaded_from(mut self, uri: Arc<str>) -> Self {
    self.uri = Some(uri);
    self
  }

  pub fn instance(&mut self, id: u16) -> AllocResult<Arc<BDDDomain>> {
    if let Some(found) = self.domains.iter().find(|domain| domain.id == id) {
      Ok(found.clone())
    } else {
      let domain = Arc::new(BDDDomain::new(self.name.clone(), id, self.size, self.manager.clone())?);
      self.domains.push(domain.clone());
      Ok(domain)
    }
  }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BDDDomain {
  pub name: Arc<str>,
  pub id: u16,
  size: u128,
  range: (u32, u32),
  vars: Vec<BDDFunction>,
  manager: BDDManagerRef,
}

impl Debug for BDDDomain {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("BDDDomain")
      .field("name", &self.name)
      .field("id", &self.id)
      .field("size", &self.size)
      .field("range", &self.range)
      .finish()
  }
}

impl PartialOrd for BDDDomain {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    let (self_start, self_end) = self.range;
    let (other_start, other_end) = other.range;

    if self_start == other_start && self_end == other_end {
      Some(Ordering::Equal)
    } else if self_end < other_start {
      Some(Ordering::Less)
    } else if self_start > other_end {
      Some(Ordering::Greater)
    } else {
      None
    }
  }
}

impl BDDDomain {
  pub fn new(name: Arc<str>, id: u16, size: u128, manager: BDDManagerRef) -> AllocResult<BDDDomain> {
    let (range, vars) = manager.with_manager_exclusive(|manager| {
      let start = manager.num_levels();
      let var_count = size.next_power_of_two().trailing_zeros() as usize;
      let mut vars = Vec::with_capacity(var_count);
      for _ in 0..var_count {
        vars.push(BDDFunction::new_var(manager)?);
      }
      let end = start + vars.len() as u32;
      Ok(((start, end), vars))
    })?;
    Ok(BDDDomain { name, id, size, range, vars, manager })
  }

  pub fn vars(&self) -> &[BDDFunction] {
    &self.vars
  }

  pub fn value(&self, i: u128) -> AllocResult<BDDFunction> {
    let BDDDomain { manager, vars, .. } = self;
    manager.with_manager_shared(|manager| {
      let mut value = i;
      if value >= self.size as u128 {
        return Ok(BDDFunction::f(manager));
      }
      let mut domain = BDDFunction::t(manager);
      for var in vars.iter().rev() {
        if (value & 0b1) == 1 {
          domain = domain.and(&var)?;
        } else {
          domain = domain.and(&var.not()?)?;
        }
        value = value >> 1;
      }
      Ok(domain)
    })
  }

  pub fn value_lt(&self, i: u128) -> AllocResult<BDDFunction> {
    let BDDDomain { manager, vars, .. } = self;
    manager.with_manager_shared(|manager| {
      let mut value = i;
      let mut var_bindings = VecDeque::with_capacity(vars.len());
      for var in vars.iter().rev() {
        let binding = (value & 0b1) == 1;
        var_bindings.push_front((var.clone(), binding));
        value = value >> 1;
      }
      let mut domain = BDDFunction::f(manager);
      let mut prefix = BDDFunction::t(manager);
      for (var, binding) in var_bindings {
        if binding {
          let next = prefix.and(&var.not()?)?;

          domain = domain.or(&next)?;
          prefix = prefix.and(&var)?;
        } else {
          prefix = prefix.and(&var.not()?)?;
        }
      }
      Ok(domain)
    })
  }

  pub fn value_le(&self, i: u128) -> AllocResult<BDDFunction> {
    let BDDDomain { manager, vars, .. } = self;
    manager.with_manager_shared(|manager| {
      let mut value = i;
      let mut var_bindings = VecDeque::with_capacity(vars.len());
      for var in vars.iter().rev() {
        let binding = (value & 0b1) == 1;
        var_bindings.push_front((var.clone(), binding));
        value = value >> 1;
      }
      let mut domain = BDDFunction::f(manager);
      let mut prefix = BDDFunction::t(manager);
      for (var, binding) in var_bindings {
        if binding {
          let next = prefix.and(&var.not()?)?;

          domain = domain.or(&next)?;
          prefix = prefix.and(&var)?;
        } else {
          prefix = prefix.and(&var.not()?)?;
        }
      }
      domain = domain.or(&prefix)?;
      Ok(domain)
    })
  }

  pub fn value_gt(&self, i: u128) -> AllocResult<BDDFunction> {
    self.value_le(i)?.not()
  }

  pub fn value_ge(&self, i: u128) -> AllocResult<BDDFunction> {
    self.value_lt(i)?.not()
  }

  pub fn value_ne(&self, i: u128) -> AllocResult<BDDFunction> {
    self.value(i)?.not()
  }

  pub fn values(&self, is: Vec<u128>) -> AllocResult<BDDFunction> {
    let BDDDomain { manager, vars, .. } = self;
    manager.with_manager_shared(|manager| {
      let mut values = BDDFunction::f(manager);
      for mut i in is {
        if i >= self.size as u128 {
          return Ok(BDDFunction::f(manager));
        }
        let mut value = BDDFunction::t(manager);
        for var in vars.iter().rev() {
          if (i & 0b1) == 1 {
            value = value.and(&var)?;
          } else {
            value = value.and(&var.not()?)?;
          }
          i = i >> 1;
        }
        values = values.or(&value)?;
      }
      Ok(values)
    })
  }

  pub fn domain(&self) -> AllocResult<BDDFunction> {
    let BDDDomain { manager, vars, .. } = self;
    let mut domain = manager.with_manager_shared(|manager| BDDFunction::t(manager));
    let mut value = self.size - 1;
    for var in vars {
      if (value & 0b1) == 1 {
        domain = domain.or(&var.not()?)?;
      } else {
        domain = domain.and(&var.not()?)?;
      }
      value = value >> 1;
    }
    Ok(domain)
  }

  pub fn set(&self) -> AllocResult<BDDFunction> {
    self.manager.with_manager_shared(|manager| {
      let mut bdd = BDDFunction::t(manager);
      for var in &self.vars {
        bdd = bdd.and(var)?;
      }
      Ok(bdd)
    })
  }

  pub fn range(&self) -> (u32, u32) {
    self.range
  }

  pub fn size(&self) -> usize {
    let (from, to) = self.range;
    (to - from) as usize
  }

  pub fn sat_count<S: BuildHasher>(&self, bdd: &BDDFunction, cache: &mut SatCountCache<ShiftCounter, S>) -> ShiftCounter {
    let (start, end) = self.range;
    let var_count = end - start;
    if !bdd.exists(&self.set().unwrap()).unwrap().valid() {
      return ShiftCounter::from(0u32);
    }
    bdd.sat_count(var_count, cache)
  }
}

#[cfg(test)]
mod test {
  use std::hash::BuildHasherDefault;

  use crate::expect;
  use crate::testutil::core::{Locatable, expect};
  use crate::testutil::matchers::equal_to::EqualTo;
  use oxidd::util::{FxHasher, SatCountCache};

  use super::*;
  mod bdd_domain {
    use super::*;

    mod values {

      use super::*;

      #[test]
      fn eq() {
        let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);

        let domain = BDDDomain::new(Arc::from("test"), 1, 4, manager_ref.clone()).unwrap();

        let bdd = domain.value(0).unwrap();

        assert!(bdd.eval(vars(&domain, 0)));
        assert!(!bdd.eval(vars(&domain, 1)));
        assert!(!bdd.eval(vars(&domain, 2)));
        assert!(!bdd.eval(vars(&domain, 3)));

        let bdd = domain.value(1).unwrap();

        assert!(!bdd.eval(vars(&domain, 0)));
        assert!(bdd.eval(vars(&domain, 1)));
        assert!(!bdd.eval(vars(&domain, 2)));
        assert!(!bdd.eval(vars(&domain, 3)));

        let bdd = domain.value(2).unwrap();

        assert!(!bdd.eval(vars(&domain, 0)));
        assert!(!bdd.eval(vars(&domain, 1)));
        assert!(bdd.eval(vars(&domain, 2)));
        assert!(!bdd.eval(vars(&domain, 3)));

        let bdd = domain.value(3).unwrap();

        assert!(!bdd.eval(vars(&domain, 0)));
        assert!(!bdd.eval(vars(&domain, 1)));
        assert!(!bdd.eval(vars(&domain, 2)));
        assert!(bdd.eval(vars(&domain, 3)));
      }

      #[test]
      fn lt() {
        let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);

        let domain = BDDDomain::new(Arc::from("test"), 1, 4, manager_ref.clone()).unwrap();

        let bdd = domain.value_lt(0).unwrap();

        assert!(!bdd.eval(vars(&domain, 0)));
        assert!(!bdd.eval(vars(&domain, 1)));
        assert!(!bdd.eval(vars(&domain, 2)));
        assert!(!bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_lt(1).unwrap();

        assert!(bdd.eval(vars(&domain, 0)));
        assert!(!bdd.eval(vars(&domain, 1)));
        assert!(!bdd.eval(vars(&domain, 2)));
        assert!(!bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_lt(2).unwrap();

        assert!(bdd.eval(vars(&domain, 0)));
        assert!(bdd.eval(vars(&domain, 1)));
        assert!(!bdd.eval(vars(&domain, 2)));
        assert!(!bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_lt(3).unwrap();

        assert!(bdd.eval(vars(&domain, 0)));
        assert!(bdd.eval(vars(&domain, 1)));
        assert!(bdd.eval(vars(&domain, 2)));
        assert!(!bdd.eval(vars(&domain, 3)));
      }

      #[test]
      fn le() {
        let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);

        let domain = BDDDomain::new(Arc::from("test"), 1, 4, manager_ref.clone()).unwrap();

        let bdd = domain.value_le(0).unwrap();

        assert!(bdd.eval(vars(&domain, 0)));
        assert!(!bdd.eval(vars(&domain, 1)));
        assert!(!bdd.eval(vars(&domain, 2)));
        assert!(!bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_le(1).unwrap();

        assert!(bdd.eval(vars(&domain, 0)));
        assert!(bdd.eval(vars(&domain, 1)));
        assert!(!bdd.eval(vars(&domain, 2)));
        assert!(!bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_le(2).unwrap();

        assert!(bdd.eval(vars(&domain, 0)));
        assert!(bdd.eval(vars(&domain, 1)));
        assert!(bdd.eval(vars(&domain, 2)));
        assert!(!bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_le(3).unwrap();

        assert!(bdd.eval(vars(&domain, 0)));
        assert!(bdd.eval(vars(&domain, 1)));
        assert!(bdd.eval(vars(&domain, 2)));
        assert!(bdd.eval(vars(&domain, 3)));
      }

      #[test]
      fn gt() {
        let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);

        let domain = BDDDomain::new(Arc::from("test"), 1, 4, manager_ref.clone()).unwrap();

        let bdd = domain.value_gt(0).unwrap();

        assert!(!bdd.eval(vars(&domain, 0)));
        assert!(bdd.eval(vars(&domain, 1)));
        assert!(bdd.eval(vars(&domain, 2)));
        assert!(bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_gt(1).unwrap();

        assert!(!bdd.eval(vars(&domain, 0)));
        assert!(!bdd.eval(vars(&domain, 1)));
        assert!(bdd.eval(vars(&domain, 2)));
        assert!(bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_gt(2).unwrap();

        assert!(!bdd.eval(vars(&domain, 0)));
        assert!(!bdd.eval(vars(&domain, 1)));
        assert!(!bdd.eval(vars(&domain, 2)));
        assert!(bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_gt(3).unwrap();

        assert!(!bdd.eval(vars(&domain, 0)));
        assert!(!bdd.eval(vars(&domain, 1)));
        assert!(!bdd.eval(vars(&domain, 2)));
        assert!(!bdd.eval(vars(&domain, 3)));
      }

      #[test]
      fn ge() {
        let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);

        let domain = BDDDomain::new(Arc::from("test"), 1, 4, manager_ref.clone()).unwrap();

        let bdd = domain.value_ge(0).unwrap();

        assert!(bdd.eval(vars(&domain, 0)));
        assert!(bdd.eval(vars(&domain, 1)));
        assert!(bdd.eval(vars(&domain, 2)));
        assert!(bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_ge(1).unwrap();

        assert!(!bdd.eval(vars(&domain, 0)));
        assert!(bdd.eval(vars(&domain, 1)));
        assert!(bdd.eval(vars(&domain, 2)));
        assert!(bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_ge(2).unwrap();

        assert!(!bdd.eval(vars(&domain, 0)));
        assert!(!bdd.eval(vars(&domain, 1)));
        assert!(bdd.eval(vars(&domain, 2)));
        assert!(bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_ge(3).unwrap();

        assert!(!bdd.eval(vars(&domain, 0)));
        assert!(!bdd.eval(vars(&domain, 1)));
        assert!(!bdd.eval(vars(&domain, 2)));
        assert!(bdd.eval(vars(&domain, 3)));
      }

      #[test]
      fn ne() {
        let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);

        let domain = BDDDomain::new(Arc::from("test"), 1, 4, manager_ref.clone()).unwrap();

        let bdd = domain.value_ne(0).unwrap();

        assert!(!bdd.eval(vars(&domain, 0)));
        assert!(bdd.eval(vars(&domain, 1)));
        assert!(bdd.eval(vars(&domain, 2)));
        assert!(bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_ne(1).unwrap();

        assert!(bdd.eval(vars(&domain, 0)));
        assert!(!bdd.eval(vars(&domain, 1)));
        assert!(bdd.eval(vars(&domain, 2)));
        assert!(bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_ne(2).unwrap();

        assert!(bdd.eval(vars(&domain, 0)));
        assert!(bdd.eval(vars(&domain, 1)));
        assert!(!bdd.eval(vars(&domain, 2)));
        assert!(bdd.eval(vars(&domain, 3)));

        let bdd = domain.value_ne(3).unwrap();

        assert!(bdd.eval(vars(&domain, 0)));
        assert!(bdd.eval(vars(&domain, 1)));
        assert!(bdd.eval(vars(&domain, 2)));
        assert!(!bdd.eval(vars(&domain, 3)));
      }

      fn vars(domain: &BDDDomain, mut i: u128) -> Vec<(&BDDFunction, bool)> {
        let mut vars = Vec::new();
        for var in domain.vars().iter().rev() {
          if i & 0b1 == 1 {
            vars.push((var, true));
          } else {
            vars.push((var, false));
          }
          i = i >> 1;
        }
        vars
      }
    }
    mod sat_count {
      use super::*;

      #[test]
      fn all_in_domain_exaustive() {
        let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);
        let mut count_cache: SatCountCache<ShiftCounter, BuildHasherDefault<FxHasher>> = SatCountCache::default();

        let domain = BDDDomain::new(Arc::from("test"), 1, 4, manager_ref.clone()).unwrap();

        let all = domain.domain().unwrap();
        let sat = domain.sat_count(&all, &mut count_cache).solutions().unwrap();
        expect!(sat).to_equal(4);
      }

      #[test]
      fn all_in_domain_partial() {
        let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);
        let mut count_cache: SatCountCache<ShiftCounter, BuildHasherDefault<FxHasher>> = SatCountCache::default();

        let domain = BDDDomain::new(Arc::from("test"), 1, 3, manager_ref.clone()).unwrap();

        let all = domain.domain().unwrap();
        let sat = domain.sat_count(&all, &mut count_cache).solutions().unwrap();
        expect!(sat).to_equal(3);
      }

      mod subsets {
        use super::*;

        #[test]
        fn maximum() {
          let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);
          let mut count_cache: SatCountCache<ShiftCounter, BuildHasherDefault<FxHasher>> = SatCountCache::default();

          let domain = BDDDomain::new(Arc::from("test"), 1, 4, manager_ref.clone()).unwrap();

          let v0 = domain.value(0).unwrap();
          let v1 = domain.value(1).unwrap();
          let v2 = domain.value(2).unwrap();
          let v3 = domain.value(3).unwrap();
          let v0123 = v0.or(&v1).unwrap().or(&v2).unwrap().or(&v3).unwrap();
          let sat = domain.sat_count(&v0123, &mut count_cache).solutions().unwrap();
          expect!(sat).to_equal(4);
        }

        #[test]
        fn single() {
          let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);
          let mut count_cache: SatCountCache<ShiftCounter, BuildHasherDefault<FxHasher>> = SatCountCache::default();

          let domain = BDDDomain::new(Arc::from("test"), 1, 8, manager_ref.clone()).unwrap();

          let v0 = domain.value(0).unwrap();

          let sat = domain.sat_count(&v0, &mut count_cache).solutions().unwrap();
          expect!(sat).to_equal(1);
        }

        #[test]
        fn multiple() {
          let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);
          let mut count_cache: SatCountCache<ShiftCounter, BuildHasherDefault<FxHasher>> = SatCountCache::default();

          let domain = BDDDomain::new(Arc::from("test"), 1, 8, manager_ref.clone()).unwrap();

          let v0 = domain.value(0).unwrap();
          let v4 = domain.value(4).unwrap();

          let v04 = v0.or(&v4).unwrap();

          let sat = domain.sat_count(&v04, &mut count_cache).solutions().unwrap();
          expect!(sat).to_equal(2);
        }

        #[test]
        fn undefined() {
          let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);
          let mut count_cache: SatCountCache<ShiftCounter, BuildHasherDefault<FxHasher>> = SatCountCache::default();

          let domain = BDDDomain::new(Arc::from("test"), 1, 7, manager_ref.clone()).unwrap();

          let v1 = domain.value(7).unwrap();

          let sat = domain.sat_count(&v1, &mut count_cache).solutions().unwrap();
          expect!(sat).to_equal(0);
        }
      }

      mod multiple_domains {

        use super::*;

        #[test]
        fn matching_domain() {
          let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);
          let mut count_cache: SatCountCache<ShiftCounter, BuildHasherDefault<FxHasher>> = SatCountCache::default();

          let d1 = BDDDomain::new(Arc::from("test"), 1, 4, manager_ref.clone()).unwrap();
          let d1_0 = d1.value(0).unwrap();

          let d2 = BDDDomain::new(Arc::from("test"), 2, 4, manager_ref.clone()).unwrap();
          let d2_1 = d2.value(1).unwrap();

          let d3 = BDDDomain::new(Arc::from("test"), 3, 4, manager_ref.clone()).unwrap();
          let d3_2 = d3.value(2).unwrap();

          let sat1 = d1.sat_count(&d1_0, &mut count_cache).solutions().unwrap();
          expect!(sat1).to_equal(1);
          let sat2 = d2.sat_count(&d2_1, &mut count_cache).solutions().unwrap();
          expect!(sat2).to_equal(1);
          let sat3 = d3.sat_count(&d3_2, &mut count_cache).solutions().unwrap();
          expect!(sat3).to_equal(1);
        }

        #[test]
        fn values_from_higher_domain() {
          let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);
          let mut count_cache: SatCountCache<ShiftCounter, BuildHasherDefault<FxHasher>> = SatCountCache::default();

          let d1 = BDDDomain::new(Arc::from("test"), 1, 4, manager_ref.clone()).unwrap();

          let d2 = BDDDomain::new(Arc::from("test"), 2, 4, manager_ref.clone()).unwrap();
          let d2_1 = d2.value(1).unwrap();

          let d3 = BDDDomain::new(Arc::from("test"), 3, 4, manager_ref.clone()).unwrap();
          let d3_2 = d3.value(2).unwrap();

          let sat1 = d1.sat_count(&d2_1, &mut count_cache).solutions().unwrap();
          let sat2 = d2.sat_count(&d3_2, &mut count_cache).solutions().unwrap();
          expect!(sat1).to_equal(0);
          expect!(sat2).to_equal(0);
        }

        #[test]
        fn values_from_lower_domain() {
          let manager_ref = oxidd::bdd::new_manager(1024, 1024, 1);
          let mut count_cache: SatCountCache<ShiftCounter, BuildHasherDefault<FxHasher>> = SatCountCache::default();

          let d1 = BDDDomain::new(Arc::from("test"), 1, 4, manager_ref.clone()).unwrap();
          let d1_0 = d1.value(0).unwrap();

          let d2 = BDDDomain::new(Arc::from("test"), 2, 4, manager_ref.clone()).unwrap();
          let d2_1 = d2.value(1).unwrap();

          let d3 = BDDDomain::new(Arc::from("test"), 3, 4, manager_ref.clone()).unwrap();

          let sat2 = d2.sat_count(&d1_0, &mut count_cache).solutions().unwrap();
          let sat3 = d3.sat_count(&d2_1, &mut count_cache).solutions().unwrap();
          expect!(sat2).to_equal(0);
          expect!(sat3).to_equal(0);
        }
      }
    }
  }
}
