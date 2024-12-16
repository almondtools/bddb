use std::collections::HashMap;
use std::sync::Arc;

use oxidd::bdd::{BDDFunction, BDDManagerRef};
use oxidd::util::{AllocResult, OutOfMemory};
use oxidd::{BooleanFunction, ManagerRef};

use crate::lang::graph::{BIRGenerator, BIRProg, BIRVisitor, Location, RuleGraph, Variable};

use super::database::BDDBManager;
use super::domain::DomainSource;
use super::relation::{BDDRelation, RelationIn, RelationOut, TupleSource, TupleStore};

#[derive(Debug)]
pub enum ExecutionError {
  Unexpected(&'static str),
  Memory(&'static str),
}

pub type ExecutionResult = Result<(), ExecutionError>;

#[derive(Default)]
pub struct Evaluator {
  domains: HashMap<Arc<str>, Arc<DomainSource>>,
  ins: HashMap<Arc<str>, RelationIn>,
  outs: HashMap<Arc<str>, RelationOut>,
}

impl Evaluator {
  pub fn new() -> Self {
    Evaluator::default()
  }

  pub fn register_domain(&mut self, key: &str, domain: DomainSource) {
    let key = Arc::from(key);
    self.domains.insert(key, Arc::new(domain));
  }

  pub fn register_in(&mut self, key: &str, domains: &[&str], src: TupleSource) {
    let domains = domains.iter().map(|d| self.domains.get(*d).unwrap()).cloned().collect();
    let src = RelationIn::new(domains, src);
    let key = Arc::from(key);
    self.ins.insert(key, src);
  }

  pub fn register_out(&mut self, key: &str, domains: &[&str], store: TupleStore) {
    let domains = domains.iter().map(|d| self.domains.get(*d).unwrap()).cloned().collect();
    let store = RelationOut::new(domains, store);
    let key = Arc::from(key);
    self.outs.insert(key, store);
  }

  pub fn execute(&self, graph: RuleGraph, manager: BDDBManager) -> ExecutionResult {
    let ir = self.create_bdd_ir(&graph, manager.manager().clone());
    ir.accept(&mut BIRPrinter::new()).map_err(|_| ExecutionError::Unexpected("printing BIR"))?;
    ir.accept(&mut BIRInterpreter::new(self, manager)).map_err(|_| ExecutionError::Memory("out of memory"))?;
    Ok(())
  }

  pub fn create_bdd_ir(&self, graph: &RuleGraph, manager: BDDManagerRef) -> BIRProg {
    let mut ir_generator = BIRGenerator::new(manager);
    graph.accept(&mut ir_generator);
    ir_generator.ir()
  }
}

pub struct BIRInterpreter<'a> {
  evaluator: &'a Evaluator,
  manager: BDDBManager,
  variables: HashMap<Arc<str>, BDDRelation>,
}

impl<'a> BIRInterpreter<'a> {
  pub fn new(evaluator: &Evaluator, manager: BDDBManager) -> BIRInterpreter<'_> {
    let variables = HashMap::new();
    BIRInterpreter { evaluator, manager, variables }
  }
}

impl BIRVisitor<OutOfMemory> for BIRInterpreter<'_> {
  fn load(&mut self, to: &Variable, from: &Location) -> AllocResult<()> {
    let name = to.name.clone();

    let domains = to.domains().to_vec();

    let tuples = self.evaluator.ins.get(&from.uri).expect("compile error");

    let (none, all) = self.manager.manager().with_manager_shared(|manager| (BDDFunction::f(manager), BDDFunction::t(manager)));
    let relation = self.manager.relation(name.clone(), domains).from_src(|domains| {
      let mut bdd = none.clone();
      for tuple in tuples.load() {
        let mut tuple_bdd = all.clone();
        for (v, d) in tuple.into_iter().zip(domains.iter()) {
          let element_bdd = d.value(v)?;
          tuple_bdd = tuple_bdd.and(&element_bdd)?;
        }
        bdd = bdd.or(&tuple_bdd)?;
      }
      Ok(bdd)
    })?;
    self.variables.insert(name, relation);
    Ok(())
  }

  fn store(&mut self, from: &Variable, to: &Location) -> AllocResult<()> {
    let tuples = self.evaluator.outs.get(&to.uri).expect("compile error");

    let relation = self.variables.get(&from.name).expect("compile error");

    for tuple in relation.solutions() {
      tuples.store(&tuple);
    }

    Ok(())
  }

  fn copy(&mut self, to: &Variable, from: &Variable) -> AllocResult<()> {
    let relation = self.variables.get(&from.name).expect("compile error");
    let copied = relation.unify(from.domains(), to.domains())?;

    self.variables.insert(to.name.clone(), copied);
    Ok(())
  }

  fn project(&mut self, to: &Variable, from: &Variable) -> AllocResult<()> {
    let relation = self.variables.get(&from.name).expect("compile error");
    let projected = relation.project(to.domains())?.into(to.name.clone());

    self.variables.insert(to.name.clone(), projected);
    Ok(())
  }

  fn join(&mut self, to: &Variable, left: &Variable, right: &Variable) -> AllocResult<()> {
    let left = self.variables.get(&left.name).expect("compile error");
    let right = self.variables.get(&right.name).expect("compile error");
    let joint = left.join(right)?.into(to.name.clone()).project(to.domains())?.into(to.name.clone());

    self.variables.insert(to.name.clone(), joint);
    Ok(())
  }

  fn union(&mut self, to: &Variable, left: &Variable, right: &Variable) -> Result<(), OutOfMemory> {
    let left = self.variables.get(&left.name).expect("compile_error");
    let right = self.variables.get(&right.name).expect("compile_error");
    let union = left.union(right)?.into(to.name.clone()).project(to.domains())?.into(to.name.clone());

    self.variables.insert(to.name.clone(), union);
    Ok(())
  }
}

pub struct BIRPrinter {}

impl BIRPrinter {
  pub fn new() -> Self {
    BIRPrinter {}
  }
}

impl BIRVisitor<()> for BIRPrinter {
  fn load(&mut self, to: &Variable, from: &Location) -> Result<(), ()> {
    println!("LOAD {} <- {}", &to.name, &from.uri);
    Ok(())
  }

  fn store(&mut self, from: &Variable, to: &Location) -> Result<(), ()> {
    println!("STORE {} -> {}", &from.name, &to.uri);
    Ok(())
  }

  fn copy(&mut self, to: &Variable, from: &Variable) -> Result<(), ()> {
    println!("COPY {} <- {}", &to.name, &from.name);
    Ok(())
  }

  fn project(&mut self, to: &Variable, from: &Variable) -> Result<(), ()> {
    println!("PROJECT {} <- {}", &to.name, &from.name);
    Ok(())
  }

  fn join(&mut self, to: &Variable, left: &Variable, right: &Variable) -> Result<(), ()> {
    println!("JOIN {} <- {} & {}", &to.name, &left.name, &right.name);
    Ok(())
  }

  fn union(&mut self, to: &Variable, left: &Variable, right: &Variable) -> Result<(), ()> {
    println!("UNION {} <- {} | {}", &to.name, &left.name, &right.name);
    Ok(())
  }
}

#[cfg(test)]
mod test {
  use std::sync::Arc;

  use std::sync::Mutex;

  use crate::relation;

  use super::*;

  mod load {

    use super::*;

    #[test]
    fn simple() {
      let mut evaluator = Evaluator::new();
      evaluator.register_domain("dom", DomainSource::set_of(vec!["a", "b"]));
      evaluator.register_in("rel", &["dom", "dom"], TupleSource::Set(relation![("a", "b")]));

      let manager = BDDBManager::new(1024, 1024, 1);
      let mut interpreter = BIRInterpreter::new(&evaluator, manager);
      let mut base_domain = interpreter.manager.domain(2).loaded_from(name("dom"));
      let dom1 = base_domain.instance(name("dom1")).unwrap();
      let dom2 = base_domain.instance(name("dom2")).unwrap();
      let var = Variable::new(name("rel")).with_domains(vec![dom1, dom2]);
      let inp = Location::from("rel");
      interpreter.load(&var, &inp).unwrap();

      let rel = interpreter.variables.get(&name("rel")).unwrap();

      let sat = rel.sat_count(interpreter.manager.cache_count()).solutions().unwrap();
      assert_eq!(sat, 1);
    }

    #[test]
    fn basic() {
      let mut evaluator = Evaluator::new();
      evaluator.register_domain("dom", DomainSource::set_of(vec!["a", "b"]));
      evaluator.register_in("rel", &["dom", "dom"], TupleSource::Set(relation![("a", "a"), ("a", "b")]));

      let manager = BDDBManager::new(1024, 1024, 1);
      let mut interpreter = BIRInterpreter::new(&evaluator, manager);
      let mut base_domain = interpreter.manager.domain(2).loaded_from(name("dom"));
      let dom1 = base_domain.instance(name("dom1")).unwrap();
      let dom2 = base_domain.instance(name("dom2")).unwrap();
      let var = Variable::new(name("rel")).with_domains(vec![dom1, dom2]);
      let inp = Location::from("rel");
      interpreter.load(&var, &inp).unwrap();

      let rel = interpreter.variables.get(&name("rel")).unwrap();

      let sat = rel.sat_count(interpreter.manager.cache_count()).solutions().unwrap();
      assert_eq!(sat, 2);
    }

    #[test]
    fn greater_domain() {
      let mut evaluator = Evaluator::new();
      evaluator.register_domain("dom", DomainSource::set_of(vec!["a", "b", "c", "d"]));
      evaluator.register_in("rel", &["dom", "dom"], TupleSource::Set(relation![("a", "a"), ("c", "d"), ("b", "d")]));

      let manager = BDDBManager::new(1024, 1024, 1);
      let mut interpreter = BIRInterpreter::new(&evaluator, manager);
      let mut base_domain = interpreter.manager.domain(4).loaded_from(name("dom"));
      let dom1 = base_domain.instance(name("dom1")).unwrap();
      let dom2 = base_domain.instance(name("dom2")).unwrap();
      let var = Variable::new(name("rel")).with_domains(vec![dom1, dom2]);
      let inp = Location::from("rel");
      interpreter.load(&var, &inp).unwrap();

      let rel = interpreter.variables.get(&name("rel")).unwrap();

      let sat = rel.sat_count(interpreter.manager.cache_count()).solutions().unwrap();
      assert_eq!(sat, 3);
    }

    #[test]
    fn multiple_domains_non_subsequent() {
      let mut evaluator = Evaluator::new();
      evaluator.register_domain("dom", DomainSource::set_of(vec!["a", "b", "c", "d"]));
      evaluator.register_in("rel", &["dom", "dom"], TupleSource::Set(relation![("a", "a"), ("c", "d"), ("b", "d")]));

      let manager = BDDBManager::new(1024, 1024, 1);
      let mut interpreter = BIRInterpreter::new(&evaluator, manager);
      let mut base_domain = interpreter.manager.domain(4).loaded_from(name("dom"));
      let dom1 = base_domain.instance(name("dom1")).unwrap();
      let _dom2 = base_domain.instance(name("dom2")).unwrap();
      let dom3 = base_domain.instance(name("dom3")).unwrap();
      let var = Variable::new(name("rel")).with_domains(vec![dom3, dom1]);
      let inp = Location::from("rel");
      interpreter.load(&var, &inp).unwrap();

      let rel = interpreter.variables.get(&name("rel")).unwrap();

      let sat = rel.sat_count(interpreter.manager.cache_count()).solutions().unwrap();
      assert_eq!(sat, 3);
    }
  }

  mod store {

    use std::collections::BTreeSet;

    use crate::bdd::database::BDDBManager;
    use crate::bdd::relation::TupleStore;

    use super::*;

    #[test]
    fn simple() {
      let mut evaluator = Evaluator::new();
      evaluator.register_domain("dom", DomainSource::set_of(vec!["a", "b"]));
      let result = Arc::new(Mutex::new(BTreeSet::new()));
      evaluator.register_out("rel", &["dom", "dom"], TupleStore::Set(result.clone()));

      let manager = BDDBManager::new(1024, 1024, 1);
      let mut interpreter = BIRInterpreter::new(&evaluator, manager);
      let mut base_domain = interpreter.manager.domain(2).loaded_from(name("dom"));
      let dom1 = base_domain.instance(name("dom1")).unwrap();
      let dom2 = base_domain.instance(name("dom2")).unwrap();
      let var = Variable::new(name("rel")).with_domains(vec![dom1.clone(), dom2.clone()]);
      let out = Location::from("rel");
      let rel = interpreter
        .manager
        .relation("rel", vec![dom1.clone(), dom2.clone()])
        .from_src(|domains| {
          let a = domains[0].value(0)?;
          let b = domains[1].value(1)?;
          let bdd = a.and(&b)?;
          Ok(bdd)
        })
        .unwrap();
      interpreter.variables.insert(name("rel"), rel);

      interpreter.store(&var, &out).unwrap();

      assert_eq!(&*result.lock().unwrap(), &relation![("a", "b")]);
    }

    #[test]
    fn basic() {
      let mut evaluator = Evaluator::new();
      evaluator.register_domain("dom", DomainSource::set_of(vec!["a", "b"]));
      let result = Arc::new(Mutex::new(BTreeSet::new()));
      evaluator.register_out("rel", &["dom", "dom"], TupleStore::Set(result.clone()));

      let manager = BDDBManager::new(1024, 1024, 1);
      let mut interpreter = BIRInterpreter::new(&evaluator, manager);
      let mut base_domain = interpreter.manager.domain(2).loaded_from(name("dom"));
      let dom1 = base_domain.instance(name("dom1")).unwrap();
      let dom2 = base_domain.instance(name("dom2")).unwrap();
      let var = Variable::new(name("rel")).with_domains(vec![dom1.clone(), dom2.clone()]);
      let out = Location::from("rel");
      let rel = interpreter
        .manager
        .relation("rel", vec![dom1.clone(), dom2.clone()])
        .from_src(|domains| {
          let a = domains[0].value(0)?;
          let a_or_b = domains[1].values(vec![0, 1])?;
          let bdd = a.and(&a_or_b)?;
          Ok(bdd)
        })
        .unwrap();
      interpreter.variables.insert(name("rel"), rel);

      interpreter.store(&var, &out).unwrap();

      assert_eq!(&*result.lock().unwrap(), &relation![("a", "a"), ("a", "b")]);
    }

    #[test]
    fn greater_domain() {
      let mut evaluator = Evaluator::new();
      evaluator.register_domain("dom", DomainSource::set_of(vec!["a", "b", "c", "d"]));
      let result = Arc::new(Mutex::new(BTreeSet::new()));
      evaluator.register_out("rel", &["dom", "dom"], TupleStore::Set(result.clone()));

      let manager = BDDBManager::new(1024, 1024, 1);
      let mut base_domain = manager.domain(4).loaded_from(name("dom"));
      let mut interpreter = BIRInterpreter::new(&evaluator, manager);
      let dom1 = base_domain.instance(name("dom1")).unwrap();
      let dom2 = base_domain.instance(name("dom2")).unwrap();
      let var = Variable::new(name("rel")).with_domains(vec![dom1.clone(), dom2.clone()]);
      let out = Location::from("rel");
      let rel = interpreter
        .manager
        .relation("rel", vec![dom1.clone(), dom2.clone()])
        .from_src(|domains| {
          let a = domains[0].value(0)?;
          let a_or_b = domains[1].values(vec![0, 1])?;

          let c = domains[0].value(2)?;
          let d = domains[1].value(3)?;

          let bdd = (a.and(&a_or_b)?).or(&c.and(&d)?)?;

          Ok(bdd)
        })
        .unwrap();
      interpreter.variables.insert(name("rel"), rel);

      interpreter.store(&var, &out).unwrap();

      assert_eq!(&*result.lock().unwrap(), &relation![("a", "a"), ("a", "b"), ("c", "d")]);
    }

    #[test]
    fn multiple_domains_non_subsequent() {
      let mut evaluator = Evaluator::new();
      evaluator.register_domain("dom", DomainSource::set_of(vec!["a", "b", "c", "d"]));
      let result = Arc::new(Mutex::new(BTreeSet::new()));
      evaluator.register_out("rel", &["dom", "dom"], TupleStore::Set(result.clone()));

      let manager = BDDBManager::new(1024, 1024, 1);
      let mut base_domain = manager.domain(4).loaded_from(name("dom"));
      let mut interpreter = BIRInterpreter::new(&evaluator, manager);
      let dom1 = base_domain.instance(name("dom1")).unwrap();
      let _dom2 = base_domain.instance(name("dom2")).unwrap();
      let dom3 = base_domain.instance(name("dom3")).unwrap();
      let var = Variable::new(name("rel")).with_domains(vec![dom1.clone(), dom3.clone()]);
      let out = Location::from("rel");
      let rel = interpreter
        .manager
        .relation("rel", vec![dom1.clone(), dom3.clone()])
        .from_src(|domains| {
          let a = domains[0].value(0)?;
          let a_or_b = domains[1].values(vec![0, 1])?;

          let c = domains[0].value(2)?;
          let d = domains[1].value(3)?;

          let bdd = (a.and(&a_or_b)?).or(&c.and(&d)?)?;

          Ok(bdd)
        })
        .unwrap();
      interpreter.variables.insert(name("rel"), rel);

      interpreter.store(&var, &out).unwrap();

      assert_eq!(&*result.lock().unwrap(), &relation![("a", "a"), ("a", "b"), ("c", "d")]);
    }
  }

  mod copy {

    use std::collections::BTreeSet;

    use crate::bdd::database::BDDBManager;
    use crate::bdd::relation::TupleStore;

    use super::*;

    #[test]
    fn simple() {
      let mut evaluator = Evaluator::new();
      evaluator.register_domain("dom", DomainSource::set_of(vec!["a", "b", "c", "d"]));
      let result = Arc::new(Mutex::new(BTreeSet::new()));
      evaluator.register_out("rel", &["dom", "dom"], TupleStore::Set(result.clone()));

      let manager = BDDBManager::new(1024, 1024, 1);
      let mut base_domain = manager.domain(4).loaded_from(name("dom"));
      let mut interpreter = BIRInterpreter::new(&evaluator, manager);
      let dom1 = base_domain.instance(name("dom1")).unwrap();
      let dom2 = base_domain.instance(name("dom2")).unwrap();
      let dom3 = base_domain.instance(name("dom3")).unwrap();
      let var1 = Variable::new(name("rel_1")).with_domains(vec![dom1.clone(), dom2.clone()]);
      let var2 = Variable::new(name("rel_2")).with_domains(vec![dom2.clone(), dom3.clone()]);

      let rel_1 = interpreter
        .manager
        .relation("rel", vec![dom1.clone(), dom2.clone()])
        .from_src(|domains| {
          let a = domains[0].value(0)?;
          let b_1 = domains[1].value(1)?;

          let b_0 = domains[0].value(1)?;
          let c = domains[1].value(2)?;

          let bdd = (a.and(&b_1)?).or(&b_0.and(&c)?)?;

          Ok(bdd)
        })
        .unwrap();
      interpreter.variables.insert(name("rel_1"), rel_1);

      interpreter.copy(&var2, &var1).unwrap();

      let rel_1 = interpreter.variables.get(&name("rel_1")).unwrap();
      assert_eq!(rel_1.domains(), vec![dom1.clone(), dom2.clone()]);

      let rel_2 = interpreter.variables.get(&name("rel_2")).unwrap();
      assert_eq!(rel_2.domains(), vec![dom2.clone(), dom3.clone()]);

      let sat = rel_1.sat_count(interpreter.manager.cache_count()).solutions().unwrap();
      assert_eq!(sat, 2);
    }
  }

  fn name<T: AsRef<str>>(name: T) -> Arc<str> {
    Arc::from(name.as_ref())
  }
}
