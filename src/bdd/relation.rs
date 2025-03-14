use std::collections::{BTreeSet, VecDeque};
use std::fmt::Debug;
use std::hash::BuildHasher;
use std::sync::{Arc, Mutex};

use oxidd::bdd::{BDDFunction, BDDManagerRef};
use oxidd::util::{AllocResult, SatCountCache};
use oxidd::{BooleanFunction, BooleanFunctionQuant, Function, FunctionSubst, Manager, ManagerRef, Subst};

use super::counter::ShiftCounter;
use super::domain::{BDDDomain, DomainSource};

pub enum TupleSource {
  Set(BTreeSet<Vec<Arc<str>>>),
}

impl TupleSource {
  pub fn tuples(&self) -> impl Iterator<Item = Vec<Arc<str>>> {
    let TupleSource::Set(set) = self;
    set.into_iter().cloned()
  }
}

pub enum TupleStore {
  Set(Arc<Mutex<BTreeSet<Vec<Arc<str>>>>>),
}

impl TupleStore {
  pub fn store<S: Into<Arc<str>>>(&self, tuple: Vec<S>) {
    let TupleStore::Set(set) = &self;
    set.lock().unwrap().insert(tuple.into_iter().map(|item| item.into()).collect());
  }
}

pub struct RelationIn {
  domains: Vec<Arc<DomainSource>>,
  src: TupleSource,
}

impl RelationIn {
  pub fn new(domains: Vec<Arc<DomainSource>>, src: TupleSource) -> RelationIn {
    RelationIn { domains, src }
  }

  pub fn load(&self) -> impl Iterator<Item = Vec<u128>> {
    let tuples = self.src.tuples();
    tuples.map(|t| self.domains.iter().zip(t.iter()).map(|(domain, val)| domain.value(val.as_ref())).collect::<Vec<u128>>())
  }
}

pub struct RelationOut {
  domains: Vec<Arc<DomainSource>>,
  store: TupleStore,
}
impl RelationOut {
  pub fn new(domains: Vec<Arc<DomainSource>>, store: TupleStore) -> RelationOut {
    RelationOut { domains, store }
  }

  pub fn store(&self, tuple: &[u128]) {
    let tuple = self.domains.iter().zip(tuple.into_iter().copied()).map(|(domain, val)| domain.invert(val)).collect::<Vec<_>>();
    self.store.store(tuple);
  }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BDDUnnamedRelation {
  manager: BDDManagerRef,
  domains: Vec<Arc<BDDDomain>>,
  bdd: BDDFunction,
}

impl BDDUnnamedRelation {
  pub fn into(self, name: impl Into<Arc<str>>) -> BDDRelation {
    let name = name.into();
    let BDDUnnamedRelation { manager, domains, bdd } = self;
    BDDRelation { name, manager, domains, bdd }
  }
}

pub struct BDDRelationDef {
  pub name: Arc<str>,
  manager: BDDManagerRef,
  domains: Vec<Arc<BDDDomain>>,
}

impl BDDRelationDef {
  pub fn new(name: Arc<str>, manager: BDDManagerRef, domains: Vec<Arc<BDDDomain>>) -> BDDRelationDef {
    BDDRelationDef { name, manager, domains }
  }

  pub fn from_src(self, values: impl FnOnce(&[Arc<BDDDomain>]) -> AllocResult<BDDFunction>) -> AllocResult<BDDRelation> {
    let BDDRelationDef { name, manager, domains } = self;
    let bdd = values(&domains)?;
    Ok(BDDRelation { name, manager, domains, bdd })
  }

  pub fn init_empty(self) -> AllocResult<BDDRelation> {
    let BDDRelationDef { name, manager, domains } = self;
    let bdd = manager.with_manager_shared(|manager| BDDFunction::f(manager));
    Ok(BDDRelation { name, manager, domains, bdd })
  }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BDDRelation {
  pub name: Arc<str>,
  manager: BDDManagerRef,
  domains: Vec<Arc<BDDDomain>>,
  bdd: BDDFunction,
}

impl BDDRelation {
  pub fn domains(&self) -> &[Arc<BDDDomain>] {
    &self.domains
  }

  pub fn size(&self) -> usize {
    self.domains.iter().map(|domain| domain.size()).sum()
  }

  pub fn bdd(&self) -> &BDDFunction {
    &self.bdd
  }

  pub fn sat_count<S: BuildHasher>(&self, cache: &mut SatCountCache<ShiftCounter, S>) -> ShiftCounter {
    let bdd = &self.bdd;
    let var_count = self.domains.iter().map(|domain| domain.range().1 - domain.range().0).sum();
    bdd.sat_count(var_count, cache)
  }

  pub fn unify_variable(&self, from: &Arc<BDDDomain>, to: &Arc<BDDDomain>) -> AllocResult<BDDRelation> {
    let name = self.name.clone();
    let mut domains = self.domains.clone();
    if let Some(found) = domains.iter_mut().find(|domain| *domain == from) {
      *found = to.clone();
    }
    let substitution = Subst::new(from.vars(), to.vars());

    let bdd = self.bdd().substitute(&substitution)?;
    let manager = self.manager.clone();
    Ok(BDDRelation { name, manager, domains, bdd })
  }

  pub fn unify(&self, from: &[Arc<BDDDomain>], to: &[Arc<BDDDomain>]) -> AllocResult<BDDRelation> {
    let name = self.name.clone();
    let from_vars = from.iter().flat_map(|domain| domain.vars()).cloned().collect::<Vec<_>>();
    let to_vars = to.iter().flat_map(|domain| domain.vars()).cloned().collect::<Vec<_>>();

    let substitution = Subst::new(from_vars, to_vars);

    let bdd = self.bdd().substitute(&substitution)?;
    let manager = self.manager.clone();
    let domains = to.to_vec();
    Ok(BDDRelation { name, manager, domains, bdd })
  }

  pub fn project(&self, vars: &[Arc<BDDDomain>]) -> AllocResult<BDDUnnamedRelation> {
    let manager = self.manager.clone();
    let domains = vars.to_vec();
    let mut bdd = self.bdd.clone();

    for domain in &self.domains {
      if vars.contains(domain) {
        continue;
      }
      for var in domain.vars() {
        bdd = bdd.exists(var)?;
      }
    }
    Ok(BDDUnnamedRelation { manager, domains, bdd })
  }

  pub fn join(&self, right: &BDDRelation) -> AllocResult<BDDUnnamedRelation> {
    let mut domains = Vec::new();
    for domain in self.domains().iter().chain(right.domains().iter()) {
      if !domains.contains(domain) {
        domains.push(domain.clone());
      }
    }
    let manager = self.manager.clone();
    let bdd = self.bdd.and(right.bdd())?;
    Ok(BDDUnnamedRelation { manager, domains, bdd })
  }

  pub fn union(&self, next: &BDDRelation) -> AllocResult<BDDUnnamedRelation> {
    let mut domains = Vec::new();
    for domain in self.domains().iter().chain(next.domains().iter()) {
      if !domains.contains(domain) {
        domains.push(domain.clone());
      }
    }
    let manager = self.manager.clone();
    let bdd = self.bdd.or(next.bdd())?;
    Ok(BDDUnnamedRelation { manager, domains, bdd })
  }

  pub fn solutions(&self) -> SolutionIter {
    SolutionIter::new(self)
  }
}

struct DomainDecisions {
  domain: Arc<BDDDomain>,
  decisions: Vec<Decision>,
}

impl Debug for DomainDecisions {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("DomainDecisions")
      .field("domain", &format!("{} {:?}", &self.domain.name, &self.domain.range()))
      .field("decisions", &self.decisions)
      .finish()
  }
}

impl DomainDecisions {
  pub fn for_domain(domain: Arc<BDDDomain>) -> DomainDecisions {
    let decisions = Vec::with_capacity(domain.size());
    DomainDecisions { domain, decisions }
  }

  pub fn insert(&mut self, decision: Decision) {
    if self.contains(decision.level()) {
      self.decisions.push(decision);
    }
  }

  pub fn fill(&mut self, decision: impl Fn(u32) -> Decision) {
    while self.decisions.len() < self.domain.size() {
      let decision = decision(self.next_level());
      self.decisions.push(decision);
    }
  }

  pub fn unassigned(&self) -> bool {
    self.decisions.len() < self.domain.size()
  }

  pub fn contains(&self, level: u32) -> bool {
    let (start, end) = self.domain.range();
    start <= level && level < end
  }

  pub fn next_level(&self) -> u32 {
    let base_level = self.domain.range().0;
    let next_level = base_level + self.decisions.len() as u32;
    next_level
  }

  pub fn last_level(&self) -> u32 {
    self.domain.range().1 - 1
  }

  pub fn value(&self) -> u128 {
    self.decisions.iter().map(|decision| decision.assignment()).fold(0, |v, ass| v << 1 | if ass { 1 } else { 0 })
  }

  pub fn clear(&mut self) {
    self.decisions.clear();
  }

  pub fn clear_from(&mut self, i: usize) {
    if i < self.decisions.len() {
      self.decisions.truncate(i);
    }
  }

  pub fn build_from(&mut self, mut current_bdd: BDDFunction, buffer: &mut VecDeque<Decision>) -> Option<BDDFunction> {
    while self.unassigned()
      && let Some(decision) = buffer.pop_front()
    {
      self.insert(decision);
    }
    if current_bdd.valid() {
      self.fill(|level| Decision::Wildcard(level, false));
      return Some(current_bdd);
    } else if !current_bdd.satisfiable() {
      return None;
    }
    let last_level = self.last_level();
    let next_level = self.next_level();
    let current_level = u32::min(current_bdd.level(), last_level);
    for level in next_level..current_level {
      self.insert(Decision::Wildcard(level, false));
    }
    while self.unassigned() {
      let Some((t_bdd, f_bdd)) = current_bdd.cofactors() else { return None };
      if f_bdd.valid() {
        self.insert(Decision::Node(current_bdd, false));
        self.fill(|level| Decision::Wildcard(level, false));
        current_bdd = f_bdd;
      } else if f_bdd.satisfiable() {
        let next_bdd_level = current_bdd.level() + 1;
        let f_bdd_level = f_bdd.level();
        let wildcards = f_bdd_level - next_bdd_level;

        buffer.push_back(Decision::Node(current_bdd, false));

        for i in 0..wildcards {
          buffer.push_back(Decision::Wildcard(next_bdd_level + i, false));
        }

        while self.unassigned()
          && let Some(decision) = buffer.pop_front()
        {
          self.insert(decision);
        }
        current_bdd = f_bdd;
      } else if t_bdd.valid() {
        self.insert(Decision::Node(current_bdd, true));
        self.fill(|level| Decision::Wildcard(level, false));
        current_bdd = t_bdd;
      } else if t_bdd.satisfiable() {
        let next_bdd_level = current_bdd.level() + 1;
        let t_bdd_level = t_bdd.level();
        let wildcards = t_bdd_level - next_bdd_level;

        buffer.push_back(Decision::Node(current_bdd, true));

        for i in 0..wildcards {
          buffer.push_back(Decision::Wildcard(next_bdd_level + i, false));
        }

        while self.unassigned()
          && let Some(decision) = buffer.pop_front()
        {
          self.insert(decision);
        }
        current_bdd = t_bdd;
      } else {
        return None;
      }
    }
    return Some(current_bdd);
  }

  pub fn last_false_wildcard(&self) -> Option<usize> {
    self
      .decisions
      .iter()
      .enumerate()
      .rev()
      .find_map(|(i, decision)| if let Decision::Wildcard(_, false) = decision { Some(i) } else { None })
  }

  pub fn last_false_decision(&self, next_i: usize) -> Option<usize> {
    self
      .decisions
      .iter()
      .enumerate()
      .rev()
      .filter(|(i, _)| *i <= next_i)
      .find_map(|(i, decision)| if let Decision::Node(_, false) = decision { Some(i) } else { None })
  }
}

enum Decision {
  Node(BDDFunction, bool),
  Wildcard(u32, bool),
}

impl Debug for Decision {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Node(_, v) => f.debug_tuple("Node").field(v).finish(),
      Self::Wildcard(level, v) => f.debug_tuple("Wildcard").field(level).field(v).finish(),
    }
  }
}

impl Decision {
  pub fn level(&self) -> u32 {
    match self {
      Decision::Node(bdd, _) => bdd.level(),
      Decision::Wildcard(level, _) => *level,
    }
  }

  pub fn assignment(&self) -> bool {
    match self {
      Decision::Node(_, ass) | Decision::Wildcard(_, ass) => *ass,
    }
  }

  fn wild_flip(&mut self) {
    if let Decision::Wildcard(_, ass) = self {
      *ass = !*ass;
    };
  }
}

pub struct SolutionIter<'a> {
  rel: &'a BDDRelation,
  started: bool,
  domain_stack: Vec<DomainDecisions>,
}

pub trait Variable {
  fn level(&self) -> u32;
}

impl Variable for BDDFunction {
  fn level(&self) -> u32 {
    self.with_manager_shared(|manager, edge| {
      let node = manager.get_node(edge);
      node.level()
    })
  }
}

impl<'a> SolutionIter<'a> {
  pub fn new<'b>(rel: &'b BDDRelation) -> SolutionIter<'b> {
    let started = false;
    let mut domain_stack: Vec<DomainDecisions> = rel.domains.iter().map(|domain| DomainDecisions::for_domain(domain.clone())).collect();
    domain_stack.sort_by(|DomainDecisions { domain: domain_1, .. }, DomainDecisions { domain: domain_2, .. }| domain_1.range().cmp(&domain_2.range()));
    SolutionIter { rel, started, domain_stack }
  }

  fn value(&self) -> Vec<u128> {
    self
      .rel
      .domains
      .iter()
      .flat_map(|domain| self.domain_stack.iter().find_map(|decisions| if &decisions.domain == domain { Some(decisions.value()) } else { None }))
      .collect()
  }

  fn first_solution(&mut self) -> Option<Vec<u128>> {
    let mut current_bdd = self.rel.bdd().clone();
    if !current_bdd.satisfiable() {
      return None;
    }
    let mut buffer = VecDeque::new();
    for domain_decisions in &mut self.domain_stack {
      current_bdd = domain_decisions.build_from(current_bdd, &mut buffer)?;
    }
    Some(self.value())
  }

  fn next_solution(&mut self) -> Option<Vec<u128>> {
    if let Some((mut i, mut j)) = self.last_false_wildcard() {
      while i < self.domain_stack.len() {
        let domain_decisions = &mut self.domain_stack[i].decisions;
        while j < domain_decisions.len() {
          domain_decisions[j].wild_flip();
          j += 1;
        }
        j = 0;
        i += 1;
      }
      return Some(self.value());
    }

    let mut next_i = self.domain_stack.len() - 1;
    let mut next_j = self.domain_stack.last().map(|domain_decisions| domain_decisions.decisions.len() - 1).unwrap_or(0);
    loop {
      let Some((i, j)) = self.last_false_decision(next_i, next_j) else { return None };

      let Decision::Node(current_bdd, v) = &mut self.domain_stack[i].decisions[j] else { return None };
      let Some(t_bdd) = current_bdd.cofactor_true() else { continue };
      if t_bdd.valid() {
        *v = true;
        let mut buffer = VecDeque::new();

        let domain_decisions = &mut self.domain_stack[i];
        domain_decisions.clear_from(j + 1);
        domain_decisions.fill(|level| Decision::Wildcard(level, false));

        let mut current_bdd = t_bdd;
        for domain_decisions in &mut self.domain_stack[(i + 1)..] {
          domain_decisions.clear();
          current_bdd = domain_decisions.build_from(current_bdd, &mut buffer)?;
        }
        return Some(self.value());
      } else if t_bdd.satisfiable() {
        *v = true;
        let mut buffer = VecDeque::new();

        let next_bdd_level = current_bdd.level() + 1;
        let t_bdd_level = t_bdd.level();
        let wildcards = t_bdd_level - next_bdd_level;

        for i in 0..wildcards {
          buffer.push_back(Decision::Wildcard(next_bdd_level + i, false));
        }

        let domain_decisions = &mut self.domain_stack[i];
        domain_decisions.clear_from(j + 1);

        while domain_decisions.unassigned()
          && let Some(decision) = buffer.pop_front()
        {
          domain_decisions.insert(decision);
        }

        let mut current_bdd = t_bdd;

        if domain_decisions.unassigned() {
          current_bdd = domain_decisions.build_from(current_bdd, &mut buffer)?;
        }
        for domain_decisions in &mut self.domain_stack[(i + 1)..] {
          domain_decisions.clear();
          current_bdd = domain_decisions.build_from(current_bdd, &mut buffer)?;
        }
        return Some(self.value());
      }
      next_i = if j > 0 {
        i
      } else if i > 0 {
        i - 1
      } else {
        break;
      };
      next_j = if j > 0 { j - 1 } else { self.domain_stack[i].decisions.len() - 1 };
    }
    None
  }

  fn last_false_wildcard(&self) -> Option<(usize, usize)> {
    self
      .domain_stack
      .iter()
      .enumerate()
      .rev()
      .find_map(|(i, domain_decisions)| domain_decisions.last_false_wildcard().map(|j| (i, j)))
  }

  fn last_false_decision(&self, next_i: usize, next_j: usize) -> Option<(usize, usize)> {
    self.domain_stack.iter().enumerate().filter(|(i, _)| *i <= next_i).rev().find_map(|(i, domain_decisions)| {
      let next_j = if i == next_i { next_j } else { domain_decisions.decisions.len() - 1 };
      domain_decisions.last_false_decision(next_j).map(|j| (i, j))
    })
  }
}

impl<'a> Iterator for SolutionIter<'a> {
  type Item = Vec<u128>;

  fn next(&mut self) -> Option<Vec<u128>> {
    if !self.started {
      let first_solution = self.first_solution();
      self.started = true;
      first_solution
    } else {
      let next_solution = self.next_solution();
      next_solution
    }
  }
}

#[cfg(test)]
mod test {

  use super::*;
  use crate::bdd::database::BDDBManager;
  use crate::bdd::domain::DomainSource;
  use crate::expect;
  use crate::testutil::core::{Locatable, expect};
  use crate::testutil::matchers::contains::Contains;
  use crate::testutil::matchers::empty::Empty;
  use crate::testutil::matchers::equal_to::EqualTo;

  mod bdd_relation {
    use super::*;

    mod solutions {
      use super::*;

      #[test]
      fn one_domain() {
        let mut manager = BDDBManager::new(1024, 1024, 1);

        let num_src = Arc::new(DomainSource::set_of(vec!["1", "2", "3", "4"]));
        let mut num_dom = manager.domain(name("num_dom"), num_src.size());
        let num_dom_1 = num_dom.instance(1).unwrap();

        let exp = manager
          .relation("exp", vec![num_dom_1.clone()])
          .from_src(from(&[num_src.clone()]).tuple(&["1"]).tuple(&["3"]).factory())
          .unwrap();

        let sat = exp.sat_count(manager.cache_count()).solutions().unwrap();
        expect!(sat).to_equal(2);
        expect!(exp.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0], vec![2]]);
      }

      #[test]
      fn two_domains() {
        let mut manager = BDDBManager::new(1024, 1024, 1);

        let char_src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
        let mut char_dom = manager.domain(name("char_dom"), char_src.size());
        let char_dom_1 = char_dom.instance(1).unwrap();
        let num_src = Arc::new(DomainSource::set_of(vec!["1", "2", "3", "4"]));
        let mut num_dom = manager.domain(name("num_dom"), num_src.size());
        let num_dom_1 = num_dom.instance(1).unwrap();

        let rel = manager
          .relation("rel", vec![num_dom_1.clone(), char_dom_1.clone()])
          .from_src(from(&[num_src.clone(), char_src.clone()]).tuple(&["1", "A"]).tuple(&["3", "B"]).factory())
          .unwrap();
        let sat = rel.sat_count(manager.cache_count()).solutions().unwrap();
        expect!(sat).to_equal(2);
        expect!(rel.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0, 0], vec![2, 1]]);
      }
    }

    mod join {
      use super::*;
      mod on_single_attribute {
        use super::*;

        #[test]
        fn minimal() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut dom = manager.domain(name("dom"), src.size());
          let dom1 = dom.instance(1).unwrap();
          let dom2 = dom.instance(2).unwrap();
          let dom3 = dom.instance(3).unwrap();

          let left = manager
            .relation("left", vec![dom1.clone(), dom2.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["A", "B"]).factory())
            .unwrap();
          let right = manager
            .relation("right", vec![dom2.clone(), dom3.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["B", "C"]).factory())
            .unwrap();
          let joint = left.join(&right).unwrap().into("joint");

          let sat = joint.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(1);
          expect!(joint.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0, 1, 2]]);
        }

        #[test]
        fn empty() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut dom = manager.domain(name("dom"), src.size());
          let dom1 = dom.instance(1).unwrap();
          let dom2 = dom.instance(2).unwrap();
          let dom3 = dom.instance(3).unwrap();

          let left = manager
            .relation("left", vec![dom1.clone(), dom2.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["A", "B"]).factory())
            .unwrap();
          let right = manager
            .relation("right", vec![dom2.clone(), dom3.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["C", "D"]).factory())
            .unwrap();
          let joint = left.join(&right).unwrap().into("joint");

          let sat = joint.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(0);
          expect!(joint.solutions().next()).to_be_empty();
        }

        #[test]
        fn more() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut dom = manager.domain(name("dom"), src.size());
          let dom1 = dom.instance(1).unwrap();
          let dom2 = dom.instance(2).unwrap();
          let dom3 = dom.instance(3).unwrap();

          let left = manager
            .relation("left", vec![dom1.clone(), dom2.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["A", "B"]).tuple(&["D", "B"]).factory())
            .unwrap();
          let right = manager
            .relation("right", vec![dom2.clone(), dom3.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["B", "C"]).tuple(&["B", "D"]).factory())
            .unwrap();
          let joint = left.join(&right).unwrap().into("joint");

          let sat = joint.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(4);
          expect!(joint.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0, 1, 2], vec![0, 1, 3], vec![3, 1, 2], vec![3, 1, 3]]);
        }
      }

      mod on_unmatched_attribute {
        use super::*;

        #[test]
        fn unmatched() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut dom = manager.domain(name("dom"), src.size());
          let dom1 = dom.instance(1).unwrap();
          let dom2_1 = dom.instance(21).unwrap();
          let dom2_2 = dom.instance(22).unwrap();
          let dom3 = dom.instance(3).unwrap();

          let left = manager
            .relation("left", vec![dom1.clone(), dom2_1.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["A", "B"]).factory())
            .unwrap();
          let right = manager
            .relation("right", vec![dom2_2.clone(), dom3.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["B", "C"]).tuple(&["C", "D"]).factory())
            .unwrap();
          let joint = left.join(&right).unwrap().into("joint");

          let sat = joint.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(2);
          expect!(joint.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0, 1, 1, 2], vec![0, 1, 2, 3]]);
        }

        #[test]
        fn made_matching() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut dom = manager.domain(name("dom"), src.size());
          let dom1 = dom.instance(1).unwrap();
          let dom2_1 = dom.instance(2).unwrap();
          let dom2_2 = dom.instance(2).unwrap();
          let dom3 = dom.instance(3).unwrap();

          let left = manager
            .relation("left", vec![dom1.clone(), dom2_1.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["A", "B"]).factory())
            .unwrap();
          let old_right = manager
            .relation("right", vec![dom2_2.clone(), dom3.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["B", "C"]).tuple(&["C", "D"]).factory())
            .unwrap();
          let right = old_right.unify_variable(&dom2_2, &dom2_1).unwrap();

          let joint = left.join(&right).unwrap().into("joint");

          let sat = joint.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(1);
          expect!(joint.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0, 1, 2]]);
        }
      }

      mod on_multiple_attributes {
        use super::*;

        #[test]
        fn minimal() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut dom = manager.domain(name("dom"), src.size());
          let dom1 = dom.instance(1).unwrap();
          let dom2 = dom.instance(2).unwrap();
          let dom3 = dom.instance(3).unwrap();
          let dom4 = dom.instance(4).unwrap();

          let left = manager
            .relation("left", vec![dom1.clone(), dom2.clone(), dom3.clone()])
            .from_src(from(&[src.clone(), src.clone(), src.clone()]).tuple(&["A", "B", "C"]).factory())
            .unwrap();
          let right = manager
            .relation("right", vec![dom2.clone(), dom3.clone(), dom4.clone()])
            .from_src(from(&[src.clone(), src.clone(), src.clone()]).tuple(&["B", "C", "D"]).factory())
            .unwrap();
          let joint = left.join(&right).unwrap().into("joint");

          let sat = joint.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(1);
          expect!(joint.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0, 1, 2, 3]]);
        }

        #[test]
        fn empty() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut dom = manager.domain(name("dom"), src.size());
          let dom1 = dom.instance(1).unwrap();
          let dom2 = dom.instance(2).unwrap();
          let dom3 = dom.instance(3).unwrap();
          let dom4 = dom.instance(4).unwrap();

          let left = manager
            .relation("left", vec![dom1.clone(), dom2.clone(), dom3.clone()])
            .from_src(from(&[src.clone(), src.clone(), src.clone()]).tuple(&["A", "B", "C"]).factory())
            .unwrap();
          let right = manager
            .relation("right", vec![dom2.clone(), dom3.clone(), dom4.clone()])
            .from_src(from(&[src.clone(), src.clone(), src.clone()]).tuple(&["A", "C", "D"]).factory())
            .unwrap();
          let joint = left.join(&right).unwrap().into("joint");

          let sat = joint.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(0);
        }

        #[test]
        fn more1() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut dom = manager.domain(name("dom"), src.size());
          let dom1 = dom.instance(1).unwrap();
          let dom2 = dom.instance(2).unwrap();
          let dom3 = dom.instance(3).unwrap();
          let dom4 = dom.instance(4).unwrap();

          let left = manager
            .relation("left", vec![dom1.clone(), dom2.clone(), dom3.clone()])
            .from_src(from(&[src.clone(), src.clone(), src.clone()]).tuple(&["A", "B", "C"]).tuple(&["D", "B", "D"]).factory())
            .unwrap();
          let right = manager
            .relation("right", vec![dom2.clone(), dom3.clone(), dom4.clone()])
            .from_src(from(&[src.clone(), src.clone(), src.clone()]).tuple(&["B", "C", "C"]).tuple(&["B", "D", "D"]).factory())
            .unwrap();
          let joint = left.join(&right).unwrap().into("joint");

          let sat = joint.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(2);
          expect!(joint.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0, 1, 2, 2], vec![3, 1, 3, 3]]);
        }

        #[test]
        fn more2() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut dom = manager.domain(name("dom"), src.size());
          let dom1 = dom.instance(1).unwrap();
          let dom2 = dom.instance(2).unwrap();
          let dom3 = dom.instance(3).unwrap();
          let dom4 = dom.instance(4).unwrap();

          let left = manager
            .relation("left", vec![dom1.clone(), dom2.clone(), dom3.clone()])
            .from_src(from(&[src.clone(), src.clone(), src.clone()]).tuple(&["A", "B", "C"]).tuple(&["D", "C", "D"]).factory())
            .unwrap();
          let right = manager
            .relation("right", vec![dom2.clone(), dom3.clone(), dom4.clone()])
            .from_src(
              from(&[src.clone(), src.clone(), src.clone()])
                .tuple(&["B", "C", "C"])
                .tuple(&["B", "C", "D"])
                .tuple(&["C", "D", "A"])
                .tuple(&["C", "D", "D"])
                .factory(),
            )
            .unwrap();
          let joint = left.join(&right).unwrap().into("joint");

          let sat = joint.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(4);
          expect!(joint.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0, 1, 2, 2], vec![0, 1, 2, 3], vec![3, 2, 3, 0], vec![3, 2, 3, 3]]);
        }
      }

      mod on_multiple_domain_attributes {
        use super::*;

        #[test]
        fn more1() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let char_src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut char_dom = manager.domain(name("char_dom"), char_src.size());
          let char_dom_1 = char_dom.instance(1).unwrap();
          let num_src = Arc::new(DomainSource::set_of(vec!["1", "2", "3", "4"]));
          let mut num_dom = manager.domain(name("num_dom"), char_src.size());
          let num_dom_1 = num_dom.instance(1).unwrap();

          let left = manager
            .relation("left", vec![char_dom_1.clone(), num_dom_1.clone()])
            .from_src(
              from(&[char_src.clone(), num_src.clone()])
                .tuple(&["A", "1"])
                .tuple(&["C", "1"])
                .tuple(&["D", "2"])
                .tuple(&["C", "3"])
                .factory(),
            )
            .unwrap();
          let right = manager.relation("right", vec![num_dom_1.clone()]).from_src(from(&[num_src.clone()]).tuple(&["1"]).factory()).unwrap();
          let joint = left.join(&right).unwrap().into("joint");

          let sat = joint.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(2);
          expect!(joint.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0, 0], vec![2, 0]]);
        }
      }
    }

    mod project {
      use super::*;
      mod on_single_attribute {
        use super::*;

        #[test]
        fn minimal() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut dom = manager.domain(name("dom"), src.size());
          let dom1 = dom.instance(1).unwrap();
          let dom2 = dom.instance(2).unwrap();

          let rel = manager
            .relation("rel", vec![dom1.clone(), dom2.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["A", "B"]).tuple(&["A", "C"]).factory())
            .unwrap();
          let head = rel.project(&[dom1]).unwrap().into("head");

          let sat = head.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(1);
          expect!(head.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0]]);
        }

        #[test]
        fn mixed_0() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let char_src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut char_dom = manager.domain(name("char_dom"), char_src.size());
          let char_dom_1 = char_dom.instance(1).unwrap();
          let num_src = Arc::new(DomainSource::set_of(vec!["1", "2", "3", "4"]));
          let mut num_dom = manager.domain(name("dom2"), num_src.size());
          let num_dom_1 = num_dom.instance(1).unwrap();

          let rel = manager
            .relation("rel", vec![num_dom_1.clone(), char_dom_1.clone()])
            .from_src(from(&[num_src.clone(), char_src.clone()]).tuple(&["1", "A"]).tuple(&["2", "B"]).factory())
            .unwrap();

          let head = rel.project(&[num_dom_1]).unwrap().into("head");

          let sat = head.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(2);
          expect!(head.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0], vec![1]]);
        }

        #[test]
        fn mixed_1() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let char_src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut char_dom = manager.domain(name("char_dom"), char_src.size());
          let char_dom_1 = char_dom.instance(1).unwrap();
          let num_src = Arc::new(DomainSource::set_of(vec!["1", "2", "3", "4"]));
          let mut num_dom = manager.domain(name("num_dom"), num_src.size());
          let num_dom_1 = num_dom.instance(1).unwrap();

          let rel = manager
            .relation("rel", vec![num_dom_1.clone(), char_dom_1.clone()])
            .from_src(from(&[num_src.clone(), char_src.clone()]).tuple(&["1", "A"]).tuple(&["3", "B"]).factory())
            .unwrap();

          let first = rel.project(&[num_dom_1.clone()]).unwrap().into("first");

          let sat = first.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(2);

          expect!(first.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0], vec![2]]);
        }

        #[test]
        fn mixed_2() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let char_src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut char_dom = manager.domain(name("char_dom"), char_src.size());
          let char_dom_1 = char_dom.instance(1).unwrap();
          let num_src = Arc::new(DomainSource::set_of(vec!["1", "2", "3", "4"]));
          let mut num_dom = manager.domain(name("dom2"), num_src.size());
          let num_dom_1 = num_dom.instance(1).unwrap();

          let rel = manager
            .relation("rel", vec![num_dom_1.clone(), char_dom_1.clone()])
            .from_src(from(&[num_src.clone(), char_src.clone()]).tuple(&["1", "A"]).tuple(&["3", "B"]).factory())
            .unwrap();

          let second = rel.project(&[char_dom_1.clone()]).unwrap().into("second");

          let sat = second.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(2);
          expect!(second.solutions().collect::<Vec<Vec<u128>>>()).to_contain(vec![vec![0], vec![1]]);
        }
      }
    }

    mod union {
      use super::*;
      mod on_single_attribute {
        use super::*;

        #[test]
        fn minimal() {
          let mut manager = BDDBManager::new(1024, 1024, 1);

          let src = Arc::new(DomainSource::set_of(vec!["A", "B", "C", "D"]));
          let mut dom = manager.domain(name("dom"), src.size());
          let dom1 = dom.instance(1).unwrap();
          let dom2 = dom.instance(2).unwrap();

          let rel1 = manager
            .relation("rel1", vec![dom1.clone(), dom2.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["A", "B"]).factory())
            .unwrap();
          let rel2 = manager
            .relation("rel2", vec![dom1.clone(), dom2.clone()])
            .from_src(from(&[src.clone(), src.clone()]).tuple(&["B", "C"]).factory())
            .unwrap();
          let rel = rel1.union(&rel2).unwrap().into("rel");

          let sat = rel.sat_count(manager.cache_count()).solutions().unwrap();
          expect!(sat).to_equal(2);
        }
      }
    }
  }

  fn name<T: AsRef<str>>(name: T) -> Arc<str> {
    Arc::from(name.as_ref())
  }

  struct Tuples {
    domains: Vec<Arc<DomainSource>>,
    tuples: Vec<Vec<u128>>,
  }

  impl Tuples {
    fn tuple(mut self, values: &[&'static str]) -> Tuples {
      let tuple = values.into_iter().enumerate().map(|(i, v)| self.domains[i].value(*v)).collect::<Vec<u128>>();
      self.tuples.push(tuple);
      self
    }

    fn factory<'a>(self) -> impl FnOnce(&[Arc<BDDDomain>]) -> AllocResult<BDDFunction> {
      |domains: &[Arc<BDDDomain>]| {
        let bdd = self
          .tuples
          .into_iter()
          .flat_map(|tuple| tuple.into_iter().zip(domains.iter()).map(|(val, domain)| domain.value(val).unwrap()).reduce(|l, r| l.and(&r).unwrap()))
          .reduce(|l, r| l.or(&r).unwrap())
          .unwrap();
        Ok(bdd)
      }
    }
  }

  fn from(domains: &[Arc<DomainSource>]) -> Tuples {
    let tuples = Vec::new();
    let domains = domains.to_vec();
    Tuples { domains, tuples }
  }
}
