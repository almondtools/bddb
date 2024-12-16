use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;

use oxidd::bdd::BDDManagerRef;

use crate::bdd::domain::BDDDomain;

use super::datalog_lalr::SemanticError;

use super::ast;

#[derive(PartialEq, Debug, Clone)]
pub struct Domain {
  pub name: Arc<str>,
  pub size: u128,
  pub uri: Arc<str>,
}

impl Domain {
  pub fn new(name: Arc<str>, size: u128, uri: Arc<str>) -> Self {
    Domain { name, size, uri }
  }
}

pub fn local_domain(name: Arc<str>, size: u128, uri: Arc<str>) -> Arc<Domain> {
  Arc::new(Domain::new(name, size, uri))
}

#[derive(PartialEq, Debug)]
pub enum Store {
  From(Arc<str>),
  To(Arc<str>),
  Mem,
}

#[derive(PartialEq, Debug)]
pub enum Term {
  Var(Arc<str>),
  Str(Arc<str>),
  Ord(u128),
  Bool(bool),
  Any,
}

impl Term {
  pub fn from(term: ast::Term) -> Term {
    match term {
      ast::Term::Variable(s) => Term::Var(Arc::from(s.as_ref())),
      ast::Term::BoolVal(s) => Term::Bool(s),
      ast::Term::OrdVal(s) => Term::Ord(s),
      ast::Term::StringVal(s) => Term::Str(Arc::from(s.as_ref())),
      ast::Term::Any => Term::Any,
    }
  }
}

#[derive(PartialEq, Debug)]
pub enum Sign {
  None,
  Not,
}

#[derive(PartialEq, Debug)]
pub struct Atom {
  sign: Sign,
  name: Arc<str>,
  terms: Vec<Term>,
}

impl Atom {
  pub fn new(name: Arc<str>, terms: Vec<Term>) -> Atom {
    let sign = Sign::None;
    Atom { sign, name, terms }
  }

  pub fn neg(name: Arc<str>, terms: Vec<Term>) -> Atom {
    let sign = Sign::Not;
    Atom { sign, name, terms }
  }

  pub fn predicate(&self) -> (Arc<str>, usize) {
    (self.name.clone(), self.terms.len())
  }
}

#[derive(PartialEq, Debug)]
pub struct Node {
  kind: NodeKind,
  depends_on: RefCell<Vec<Arc<Node>>>,
}

impl Node {
  pub fn new(kind: NodeKind) -> Node {
    let depends_on = RefCell::new(Vec::new());
    Node { kind, depends_on }
  }

  pub fn depend_on<I: IntoIterator<Item = Arc<Node>>>(&self, iter: I) {
    self.depends_on.borrow_mut().extend(iter);
  }

  pub fn accept<V: NodeVisitor>(&self, visitor: &mut V) {
    match &self.kind {
      NodeKind::Relation { name, attributes, store } => {
        visitor.visit_relation(name, attributes, store, self.depends_on.borrow().as_ref());
      }
      NodeKind::Rule { head, body } => {
        visitor.visit_rule(head, body, self.depends_on.borrow().as_ref());
      }
    }
  }
}

pub fn relation_node(name: Arc<str>, attributes: Vec<Arc<Domain>>, store: Store) -> Arc<Node> {
  Arc::new(Node::new(NodeKind::Relation { name, attributes, store }))
}

pub fn rule_node(head: Atom, body: Vec<Atom>) -> Arc<Node> {
  Arc::new(Node::new(NodeKind::Rule { head, body }))
}

#[derive(PartialEq, Debug)]
pub enum NodeKind {
  Relation { name: Arc<str>, attributes: Vec<Arc<Domain>>, store: Store },
  Rule { head: Atom, body: Vec<Atom> },
}

pub trait NodeVisitor {
  fn visit_relation(&mut self, name: &Arc<str>, attributes: &Vec<Arc<Domain>>, store: &Store, depends_on: &Vec<Arc<Node>>);
  fn visit_rule(&mut self, head: &Atom, body: &Vec<Atom>, depends_on: &Vec<Arc<Node>>);
}

pub struct RuleGraph {
  names: HashSet<Arc<str>>,
  domains: HashMap<Arc<str>, Arc<Domain>>,
  relations: HashMap<(Arc<str>, usize), Arc<Node>>,
  rules: HashMap<(Arc<str>, usize), Vec<Arc<Node>>>,
  roots: Vec<Arc<Node>>,
}

impl RuleGraph {
  pub fn new() -> RuleGraph {
    let names = HashSet::new();
    let domains = HashMap::new();
    let relations = HashMap::new();
    let rules = HashMap::new();
    let roots = Vec::new();
    RuleGraph {
      names,
      domains,
      relations,
      rules,
      roots,
    }
  }

  fn name<S: Borrow<str>>(&mut self, s: S) -> Arc<str> {
    if let Some(s) = self.names.get(s.borrow()) {
      s.clone()
    } else {
      let s: Arc<str> = Arc::from(s.borrow());
      self.names.insert(s.clone());
      s
    }
  }

  pub fn insert(mut self, spec: ast::Spec) -> Result<Self, SemanticError> {
    self.register_domains(spec.domains)?;
    self.collect_nodes(spec.relations, spec.rules)?;
    Ok(self)
  }

  pub fn register_domains(&mut self, domains: Vec<ast::Domain>) -> Result<(), SemanticError> {
    for domain in domains {
      let name = self.name(domain.name.as_ref());
      let uri = self.name(domain.uri.as_ref());
      let domain = Domain::new(name.clone(), domain.size, uri);
      self.domains.insert(name, Arc::new(domain));
    }
    Ok(())
  }

  pub fn collect_nodes(&mut self, mut relations: Vec<ast::Relation>, mut rules: Vec<ast::Rule>) -> Result<(), SemanticError> {
    let goals = self.fetch_goals(&mut relations)?;

    let mut todo = VecDeque::from(goals);
    while let Some(node) = todo.pop_front() {
      match &node.kind {
        NodeKind::Relation { name, attributes, .. } => {
          let predicate = (name.clone(), attributes.len());
          let known_rules = self.fetch_known_rules(&predicate);
          let new_rules = self.fetch_rules(&predicate, &mut rules)?;

          node.depend_on(known_rules);
          node.depend_on(new_rules.iter().cloned());

          todo.extend(new_rules);
        }
        NodeKind::Rule { body, .. } => {
          let body = body.iter().map(|a| a.predicate()).collect::<Vec<_>>();
          let known_relations = self.fetch_known_relations(&body);
          let new_relations = self.fetch_relations(&body, &mut relations)?;

          self.check_definitions(&body, known_relations.iter().chain(new_relations.iter()))?;

          node.depend_on(known_relations);
          node.depend_on(new_relations.iter().cloned());

          todo.extend(new_relations);
        }
      }
    }
    Ok(())
  }

  fn fetch_goals(&mut self, relations: &mut Vec<ast::Relation>) -> Result<Vec<Arc<Node>>, SemanticError> {
    let mut goals = Vec::new();
    for relation in relations.extract_if(.., |relation| relation.is_stored()) {
      let store = self.name(relation.store().unwrap().as_ref());
      let signature = relation.signature();
      let name = self.name(signature.name.as_ref());
      let attributes = signature.attributes.iter().map(|s| self.name(s.as_ref())).collect::<Vec<_>>();
      let attributes = self.fetch_attributes(&attributes)?;
      let store = Store::To(store);
      let predicate = (name.clone(), attributes.len());
      let goal = relation_node(name, attributes, store);
      self.roots.push(goal.clone());
      self.relations.insert(predicate, goal.clone());

      goals.push(goal);
    }
    Ok(goals)
  }

  fn fetch_known_relations(&self, body: &[(Arc<str>, usize)]) -> Vec<Arc<Node>> {
    let nodes = body.iter().flat_map(|(name, arity)| self.relations.get(&(name.clone(), *arity))).cloned().collect();
    nodes
  }

  fn fetch_relations(&mut self, body: &[(Arc<str>, usize)], relations: &mut Vec<ast::Relation>) -> Result<Vec<Arc<Node>>, SemanticError> {
    let mut nodes = Vec::new();
    for relation in relations.extract_if(.., |relation| body.iter().any(|(name, arity)| relation.signature().matches(name.as_ref(), *arity))) {
      let signature = relation.signature();
      let name = self.name(signature.name.as_ref());
      let attributes = signature.attributes.iter().map(|s| self.name(s.as_ref())).collect::<Vec<_>>();
      let attributes = self.fetch_attributes(&attributes)?;
      let store = match relation {
        ast::Relation::From(_, uri) => Store::From(self.name(uri)),
        ast::Relation::To(_, uri) => Store::To(self.name(uri)),
        ast::Relation::Mem(_) => Store::Mem,
      };
      let predicate = (name.clone(), attributes.len());
      let node = relation_node(name, attributes, store);
      self.relations.insert(predicate, node.clone());
      nodes.push(node);
    }
    Ok(nodes)
  }

  fn fetch_known_rules(&self, predicate: &(Arc<str>, usize)) -> Vec<Arc<Node>> {
    if let Some(nodes) = self.rules.get(predicate) { nodes.clone() } else { Vec::new() }
  }

  fn fetch_rules(&mut self, (name, arity): &(Arc<str>, usize), rules: &mut Vec<ast::Rule>) -> Result<Vec<Arc<Node>>, SemanticError> {
    let mut nodes = Vec::new();
    for rule in rules.extract_if(.., |rule| rule.head.name.as_ref() == name.as_ref() && rule.head.terms.len() == *arity) {
      let predicate = (name.clone(), *arity);

      let head = Atom::new(self.name(rule.head.name), rule.head.terms.into_iter().map(|term| Term::from(term)).collect());
      let body = rule
        .body
        .into_iter()
        .map(|atom| match atom {
          ast::Literal::Positive(atom) => Atom::new(self.name(atom.name), atom.terms.into_iter().map(|term| Term::from(term)).collect()),
          ast::Literal::Negative(atom) => Atom::neg(self.name(atom.name), atom.terms.into_iter().map(|term| Term::from(term)).collect()),
          ast::Literal::Comparative(_) => todo!(),
        })
        .collect();
      let node = rule_node(head, body);
      self.rules.entry(predicate).or_insert_with(Vec::new).push(node.clone());
      nodes.push(node);
    }
    Ok(nodes)
  }

  fn fetch_attributes(&self, attributes: &[Arc<str>]) -> Result<Vec<Arc<Domain>>, SemanticError> {
    let attributes = attributes
      .iter()
      .map(|name| {
        self
          .domains
          .get(name)
          .cloned()
          .ok_or_else(|| SemanticError::UnknownDomain(format!("attribute domain '{}' is not defined", name.to_string())))
      })
      .try_collect()?;
    Ok(attributes)
  }

  fn check_definitions<'a, I: IntoIterator<Item = &'a Arc<Node>>>(&self, body: &[(Arc<str>, usize)], relations: I) -> Result<(), SemanticError> {
    let mut relations = relations.into_iter();
    let mut predicates = Vec::new();
    'next_node: for pred in body {
      if predicates.contains(pred) {
        continue;
      }
      while let Some(node) = relations.next() {
        let NodeKind::Relation { name, attributes, .. } = &node.kind else { continue 'next_node };
        let found_pred = (name.clone(), attributes.len());

        if pred == &found_pred {
          predicates.push(found_pred);
          continue 'next_node;
        } else {
          predicates.push(found_pred);
        }
      }
      return Err(SemanticError::UnknownRelation(format!("relation {}/{} is not defined", pred.0, pred.1)));
    }
    Ok(())
  }

  pub fn accept<V: RuleGraphVisitor>(&self, visitor: &mut V) {
    visitor.visit_graph(self);
  }
}

pub trait RuleGraphVisitor {
  fn visit_graph(&mut self, graph: &RuleGraph);
}

#[derive(PartialEq, Debug, Clone)]
pub enum VariableAttribute {
  Domains(Vec<Arc<BDDDomain>>),
  Predicate(Arc<str>, usize),
}

pub fn union_of<T: Clone + PartialEq>(left: &[T], right: &[T]) -> Vec<T> {
  let mut union = left.to_vec();
  for item in right {
    if !union.contains(item) {
      union.push(item.clone())
    }
  }
  union
}

#[derive(PartialEq, Debug, Clone)]
pub struct Variable {
  pub name: Arc<str>,
  attributes: Vec<VariableAttribute>,
}

impl Variable {
  pub fn new(name: Arc<str>) -> Self {
    Self { name, attributes: Vec::new() }
  }

  pub fn with_predicate(mut self, name: Arc<str>, arity: usize) -> Self {
    self.attributes.push(VariableAttribute::Predicate(name, arity));
    self
  }

  pub fn with_domains(mut self, domains: Vec<Arc<BDDDomain>>) -> Self {
    self.attributes.push(VariableAttribute::Domains(domains));
    self
  }

  pub fn arity(&self) -> usize {
    let (_, arity) = self.predicate();
    arity
  }

  pub fn predicate(&self) -> (&Arc<str>, usize) {
    self
      .attributes
      .iter()
      .find_map(|att| {
        let VariableAttribute::Predicate(name, arity) = att else { return None };
        Some((name, *arity))
      })
      .expect("expected predicate to be defined")
  }

  pub fn domains(&self) -> &[Arc<BDDDomain>] {
    self
      .attributes
      .iter()
      .find_map(|att| {
        let VariableAttribute::Domains(domains) = att else { return None };
        Some(domains)
      })
      .expect("expected domains to be defined")
  }

  pub fn domain_for(&self, binding: &str) -> Option<Arc<BDDDomain>> {
    self
      .attributes
      .iter()
      .find_map(|att| {
        let VariableAttribute::Domains(typ) = att else { return None };
        Some(typ)
      })
      .expect("expected type to be defined")
      .into_iter()
      .find(|domain| domain.name.as_ref() == binding)
      .cloned()
  }
}

#[derive(Debug, Clone)]
pub struct VariableContext {
  relations: HashMap<String, usize>,
  domains: HashMap<Arc<str>, usize>,
}

impl VariableContext {
  pub fn new() -> Self {
    let relations = HashMap::new();
    let domains = HashMap::new();
    VariableContext { relations, domains }
  }

  pub fn domain_variable_for(&mut self, name: &Arc<str>) -> Arc<str> {
    let count = self.domains.entry(name.clone()).or_insert(0);
    *count += 1;
    Arc::from(format!("{}{}", name, count))
  }

  pub fn relation_variable_for(&mut self, name: &str, arity: usize) -> Variable {
    let key = name.to_string();
    let number = self.relations.entry(key).or_insert(0);
    *number += 1;
    let name: Arc<str> = Arc::from(name);
    let variable_name: Arc<str> = Arc::from(format!("{}_{}", &name, number));
    Variable::new(variable_name).with_predicate(name, arity)
  }

  pub fn join_variable_for(&mut self, left: &str, right: &str, arity: usize) -> Variable {
    let key = format!("{}\u{2a1d}{}", left, right);
    let number = self.relations.entry(key.clone()).or_insert(0);
    *number += 1;
    let variable_name: Arc<str> = Arc::from(format!("{}_{}", &key, number));
    let predicate: Arc<str> = Arc::from(key);
    Variable::new(variable_name).with_predicate(predicate, arity)
  }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Location {
  pub uri: Arc<str>,
}

impl Location {
  pub fn from(uri: &str) -> Location {
    let uri = Arc::from(uri);
    Location { uri }
  }
}

pub struct BIRProg {
  instructions: Vec<BIRInst>,
}

impl BIRProg {
  pub fn accept<E, T: BIRVisitor<E>>(&self, visitor: &mut T) -> Result<(), E> {
    for instruction in &self.instructions {
      instruction.accept(visitor)?;
    }
    Ok(())
  }

  pub fn new(instructions: Vec<BIRInst>) -> Self {
    Self { instructions }
  }
}

#[derive(PartialEq, Debug, Clone)]
pub enum BIRInst {
  Load { to: Variable, from: Location },
  Store { from: Variable, to: Location },
  Copy { to: Variable, from: Variable },
  Project { to: Variable, from: Variable },
  Join { to: Variable, left: Variable, right: Variable },
  Union { to: Variable, left: Variable, right: Variable },
}

impl BIRInst {
  pub fn accept<E, T: BIRVisitor<E>>(&self, visitor: &mut T) -> Result<(), E> {
    use BIRInst::*;
    match self {
      Load { to, from } => visitor.load(to, from),
      Store { from, to } => visitor.store(from, to),
      Copy { to, from } => visitor.copy(to, from),
      Project { to, from } => visitor.project(to, from),
      Join { to, left, right } => visitor.join(to, left, right),
      Union { to, left, right } => visitor.union(to, left, right),
    }
  }
}

pub struct BIRGenerator {
  manager: BDDManagerRef,
  domains: HashMap<Arc<str>, crate::bdd::domain::Domain>,
  goals: Vec<Variable>,
  instructions: Vec<BIRInst>,
}

impl BIRGenerator {
  pub fn new(manager: BDDManagerRef) -> BIRGenerator {
    let domains = HashMap::new();
    let goals = Vec::new();
    let instructions = Vec::new();
    BIRGenerator {
      manager,
      domains,
      goals,
      instructions,
    }
  }

  fn current_var(&self) -> Variable {
    self.goals.last().expect("expected variable goal").clone()
  }

  pub fn ir(self) -> BIRProg {
    BIRProg::new(self.instructions)
  }
}

impl RuleGraphVisitor for BIRGenerator {
  fn visit_graph(&mut self, graph: &RuleGraph) {
    self.domains = graph
      .domains
      .iter()
      .map(|(_, domain)| {
        let Domain { name, size, uri } = domain.as_ref();
        let domain = crate::bdd::domain::Domain::new(self.manager.clone(), *size).loaded_from(uri.clone());
        (name.clone(), domain)
      })
      .collect();
    for root in &graph.roots {
      let NodeKind::Relation { name, attributes, .. } = &root.kind else {
        panic!("expected relation as root")
      };
      let mut context = VariableContext::new();
      let domains = attributes
        .iter()
        .map(|domain| {
          let domain_name = &domain.name;
          let domain = self.domains.get_mut(domain_name).expect("domain should be defined");
          let name = context.domain_variable_for(domain_name);
          domain.instance(name).expect("todo")
        })
        .collect();
      let variable = context.relation_variable_for(name.as_ref(), attributes.len()).with_domains(domains);
      self.goals.push(variable);
      root.accept(self);
      self.goals.pop();
    }
  }
}

impl NodeVisitor for BIRGenerator {
  fn visit_relation(&mut self, _name: &Arc<str>, _attributes: &Vec<Arc<Domain>>, store: &Store, depends_on: &Vec<Arc<Node>>) {
    let variable = self.current_var();
    if let Store::From(uri) = store {
      let uri = Location::from(uri.as_ref());
      self.instructions.push(BIRInst::Load { to: variable.clone(), from: uri });
    }
    let mut context = VariableContext::new();
    let mut next_var = variable.clone();
    for node in depends_on {
      self.goals.push(next_var);
      node.accept(self);
      let result_var = self.goals.pop().unwrap();
      if result_var != variable {
        self.instructions.push(BIRInst::Union {
          to: variable.clone(),
          left: variable.clone(),
          right: result_var,
        });
      }
      next_var = context.relation_variable_for(variable.name.as_ref(), variable.arity()).with_domains(variable.domains().to_vec());
    }
    if let Store::To(uri) = store {
      let uri = Location::from(uri.as_ref());
      self.instructions.push(BIRInst::Store { from: variable.clone(), to: uri });
    }
  }

  fn visit_rule(&mut self, head: &Atom, body: &Vec<Atom>, depends_on: &Vec<Arc<Node>>) {
    let mut context = VariableContext::new();
    let variable = self.current_var();

    let mut bindings = HashMap::new();
    for (term, binding) in head
      .terms
      .iter()
      .zip(variable.domains().iter())
      .filter_map(|(term, domain)| if let Term::Var(variable) = term { Some((variable.clone(), domain.name.clone())) } else { None })
    {
      bindings.insert(term, binding);
    }

    let sub_goals = body
      .iter()
      .map(|atom| {
        let (p_name, p_arity) = &atom.predicate();
        let node = depends_on
          .iter()
          .find(|node| {
            let NodeKind::Relation { name, attributes, .. } = &node.kind else {
              return false;
            };
            name == p_name && attributes.len() == *p_arity
          })
          .expect("expected atom matching relation");
        (atom, node)
      })
      .collect::<Vec<_>>();
    let mut variables: HashMap<(Arc<str>, usize), Variable> = HashMap::new();
    let mut join = Vec::new();
    for (atom, node) in sub_goals {
      let predicate = atom.predicate();
      let NodeKind::Relation { name, attributes, .. } = &node.kind else {
        panic!("expected relation as node")
      };
      let mut domains = Vec::new();
      for (i, term) in atom.terms.iter().enumerate() {
        let domain_name = &attributes[i].name;
        let base_domain = self.domains.get_mut(domain_name).expect("domain should be defined");
        if let Term::Var(variable) = term {
          if let Some(name) = bindings.get(variable) {
            domains.push(base_domain.instance(name.clone()).expect("todo"));
          } else {
            let name = context.domain_variable_for(name);
            bindings.insert(variable.clone(), name.clone());
            domains.push(base_domain.instance(name.clone()).expect("todo"));
          }
        } else {
          let name = context.domain_variable_for(name);
          domains.push(base_domain.instance(name.clone()).expect("todo"));
        }
      }

      let new_variable = context.relation_variable_for(name.as_ref(), attributes.len()).with_domains(domains);
      if let Some(variable) = variables.get(&predicate) {
        self.instructions.push(BIRInst::Copy {
          to: new_variable.clone(),
          from: variable.clone(),
        });
      } else {
        self.goals.push(new_variable.clone());
        node.accept(self);
        let variable = self.goals.pop().expect("expected variable to remain on stack");
        variables.insert(predicate, variable);
      }
      join.push(new_variable);
    }
    let (join_instructions, result) = join.into_iter().fold((Vec::new(), None::<Variable>), |(mut instructions, left), right| {
      if let Some(left) = left {
        let domains = union_of(left.domains(), right.domains());
        let arity = domains.len();
        let (left_name, _) = left.predicate();
        let (right_name, _) = right.predicate();
        let result = context.join_variable_for(left_name.as_ref(), right_name.as_ref(), arity).with_domains(domains);
        instructions.push(BIRInst::Join { to: result.clone(), left, right });
        (instructions, Some(result))
      } else {
        (instructions, Some(right))
      }
    });
    self.instructions.extend(join_instructions);
    if let Some(result) = result {
      self.instructions.push(BIRInst::Project { to: variable, from: result });
    }
  }
}

pub trait BIRVisitor<E> {
  fn load(&mut self, to: &Variable, from: &Location) -> Result<(), E>;
  fn store(&mut self, from: &Variable, to: &Location) -> Result<(), E>;
  fn copy(&mut self, to: &Variable, from: &Variable) -> Result<(), E>;
  fn project(&mut self, to: &Variable, from: &Variable) -> Result<(), E>;
  fn join(&mut self, to: &Variable, left: &Variable, right: &Variable) -> Result<(), E>;
  fn union(&mut self, to: &Variable, left: &Variable, right: &Variable) -> Result<(), E>;
}

#[cfg(test)]
mod test {

  use super::*;

  mod rule_graph {
    use super::*;
    mod fetch_goals {

      use super::*;

      #[test]
      fn from_single_out() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![ast::relation("goal", vec!["domain"]).stored_to("out")];
        let goals = graph.fetch_goals(&mut relations).unwrap();
        assert_eq!(goals, vec![relation_node(name("goal"), vec![local_domain(name("domain"), 2, name("out"))], Store::To(name("out")))]);
        assert_eq!(relations.len(), 0);
      }

      #[test]
      fn from_multiple_out() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![ast::relation("goal1", vec!["domain"]).stored_to("out1"), ast::relation("goal2", vec!["domain"]).stored_to("out2")];
        let goals = graph.fetch_goals(&mut relations).unwrap();
        assert_eq!(
          goals,
          vec![
            relation_node(name("goal1"), vec![local_domain(name("domain"), 2, name("out"))], Store::To(name("out1"))),
            relation_node(name("goal2"), vec![local_domain(name("domain"), 2, name("out"))], Store::To(name("out2")))
          ]
        );
        assert_eq!(relations.len(), 0);
      }

      #[test]
      fn from_mixed() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![
          ast::relation("goal1", vec!["domain"]).stored_to("out"),
          ast::relation("goal2", vec!["domain"]).loaded_from("in"),
          ast::relation("goal3", vec!["domain"]),
        ];
        let goals = graph.fetch_goals(&mut relations).unwrap();
        assert_eq!(goals, vec![relation_node(name("goal1"), vec![local_domain(name("domain"), 2, name("out"))], Store::To(name("out")))]);
        assert_eq!(relations.len(), 2);
      }
    }

    mod fetch_relations {
      use super::*;

      #[test]
      fn from_single() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![ast::relation("rel", vec!["domain"])];
        let body = vec![(name("rel"), 1)];
        let nodes = graph.fetch_relations(&body, &mut relations).unwrap();
        assert_eq!(nodes, vec![relation_node(name("rel"), vec![local_domain(name("domain"), 2, name("out"))], Store::Mem)]);
        assert_eq!(relations.len(), 0);
      }

      #[test]
      fn from_single_stored() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![ast::relation("rel", vec!["domain"]).loaded_from("in")];
        let body = vec![(name("rel"), 1)];
        let nodes = graph.fetch_relations(&body, &mut relations).unwrap();
        assert_eq!(nodes, vec![relation_node(name("rel"), vec![local_domain(name("domain"), 2, name("out"))], Store::From(name("in")))]);
        assert_eq!(relations.len(), 0);
      }

      #[test]
      fn from_single_loaded() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![ast::relation("rel", vec!["domain"]).stored_to("out")];
        let body = vec![(name("rel"), 1)];
        let nodes = graph.fetch_relations(&body, &mut relations).unwrap();
        assert_eq!(nodes, vec![relation_node(name("rel"), vec![local_domain(name("domain"), 2, name("out"))], Store::To(name("out")))]);
        assert_eq!(relations.len(), 0);
      }

      #[test]
      fn from_multiple() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![ast::relation("rel1", vec!["domain"]), ast::relation("rel2", vec!["domain"])];
        let body = vec![(name("rel1"), 1)];
        let nodes = graph.fetch_relations(&body, &mut relations).unwrap();
        assert_eq!(nodes, vec![relation_node(name("rel1"), vec![local_domain(name("domain"), 2, name("out"))], Store::Mem,)]);
        assert_eq!(relations.len(), 1);

        let body = vec![(name("rel2"), 1)];
        let nodes = graph.fetch_relations(&body, &mut relations).unwrap();
        assert_eq!(nodes, vec![relation_node(name("rel2"), vec![local_domain(name("domain"), 2, name("out"))], Store::Mem)]);
        assert_eq!(relations.len(), 0);
      }
    }

    mod fetch_known_relations {
      use super::*;

      #[test]
      fn none() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let body = vec![(name("rel"), 1)];

        let nodes = graph.fetch_known_relations(&body);
        assert_eq!(nodes, vec![]);
      }

      #[test]
      fn single() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![ast::relation("rel", vec!["domain"])];
        let body = vec![(name("rel"), 1)];
        graph.fetch_relations(&body, &mut relations).unwrap();

        let nodes = graph.fetch_known_relations(&body);
        assert_eq!(nodes, vec![relation_node(name("rel"), vec![local_domain(name("domain"), 2, name("out"))], Store::Mem)]);
      }

      #[test]
      fn multiple() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![ast::relation("rel1", vec!["domain"]), ast::relation("rel2", vec!["domain"])];
        let body = vec![(name("rel1"), 1), (name("rel2"), 1)];
        graph.fetch_relations(&body, &mut relations).unwrap();

        let nodes = graph.fetch_known_relations(&body);
        assert_eq!(
          nodes,
          vec![
            relation_node(name("rel1"), vec![local_domain(name("domain"), 2, name("out"))], Store::Mem),
            relation_node(name("rel2"), vec![local_domain(name("domain"), 2, name("out"))], Store::Mem)
          ]
        );
      }
    }
    mod fetch_rules {
      use super::*;

      #[test]
      fn from_single() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let pred1 = pred("rel1", 1);

        let head = ast::head("rel1", vec![ast::variable("X")]);
        let body = vec![ast::pos_lit("rel2", vec![ast::variable("X")])];
        let mut rules = vec![ast::Rule { head, body }];

        let nodes = graph.fetch_rules(&pred1, &mut rules).unwrap();
        let head = Atom::new(name("rel1"), vec![Term::Var(name("X"))]);
        let body = vec![Atom::new(name("rel2"), vec![Term::Var(name("X"))])];
        assert_eq!(nodes, vec![rule_node(head, body)]);
        assert_eq!(rules.len(), 0);
      }

      #[test]
      fn from_multiple() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let pred1 = pred("rel1", 1);
        let pred2 = pred("rel2", 1);

        let head = ast::head("rel1", vec![ast::variable("X")]);
        let body = vec![ast::pos_lit("rel2", vec![ast::variable("X")])];
        let rule1 = ast::Rule { head: head, body };
        let head = ast::head("rel2", vec![ast::variable("X")]);
        let body = vec![ast::pos_lit("rel3", vec![ast::variable("X")])];
        let rule2 = ast::Rule { head: head, body };
        let mut rules = vec![rule1, rule2];

        let nodes = graph.fetch_rules(&pred1, &mut rules).unwrap();
        let head = Atom::new(name("rel1"), vec![Term::Var(name("X"))]);
        let body = vec![Atom::new(name("rel2"), vec![Term::Var(name("X"))])];
        assert_eq!(nodes, vec![rule_node(head, body)]);
        assert_eq!(rules.len(), 1);

        let nodes = graph.fetch_rules(&pred2, &mut rules).unwrap();
        let head = Atom::new(name("rel2"), vec![Term::Var(name("X"))]);
        let body = vec![Atom::new(name("rel3"), vec![Term::Var(name("X"))])];
        assert_eq!(nodes, vec![rule_node(head, body)]);
        assert_eq!(rules.len(), 0);
      }
    }

    mod fetch_known_rules {
      use super::*;

      #[test]
      fn none() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let pred1 = pred("rel1", 1);

        let nodes = graph.fetch_known_rules(&pred1);
        assert_eq!(nodes, vec![]);
      }

      #[test]
      fn from_single() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let pred1: (Arc<str>, usize) = pred("rel1", 1);

        let head = ast::head("rel1", vec![ast::variable("X")]);
        let body = vec![ast::pos_lit("rel2", vec![ast::variable("X")])];
        let mut rules = vec![ast::Rule { head, body }];

        graph.fetch_known_rules(&pred1);

        let nodes = graph.fetch_rules(&pred1, &mut rules).unwrap();
        let head = Atom::new(name("rel1"), vec![Term::Var(name("X"))]);
        let body = vec![Atom::new(name("rel2"), vec![Term::Var(name("X"))])];
        assert_eq!(nodes, vec![rule_node(head, body)]);
      }

      #[test]
      fn from_multiple() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let pred1: (Arc<str>, usize) = pred("rel1", 1);

        let head = ast::head("rel1", vec![ast::variable("X")]);
        let body = vec![ast::pos_lit("rel2", vec![ast::variable("X")])];
        let rule1 = ast::Rule { head: head, body };
        let head = ast::head("rel1", vec![ast::variable("X")]);
        let body = vec![ast::pos_lit("rel3", vec![ast::variable("X")])];
        let rule2 = ast::Rule { head: head, body };
        let mut rules = vec![rule1, rule2];

        graph.fetch_rules(&pred1, &mut rules).unwrap();

        let nodes = graph.fetch_known_rules(&pred1);
        let head1 = Atom::new(name("rel1"), vec![Term::Var(name("X"))]);
        let body1 = vec![Atom::new(name("rel2"), vec![Term::Var(name("X"))])];
        let head2 = Atom::new(name("rel1"), vec![Term::Var(name("X"))]);
        let body2 = vec![Atom::new(name("rel3"), vec![Term::Var(name("X"))])];
        assert_eq!(nodes, vec![rule_node(head1, body1), rule_node(head2, body2)]);
      }
    }
  }

  fn pred<T: AsRef<str>>(name: T, arity: usize) -> (Arc<str>, usize) {
    (Arc::from(name.as_ref()), arity)
  }

  fn name<T: AsRef<str>>(name: T) -> Arc<str> {
    Arc::from(name.as_ref())
  }
}
