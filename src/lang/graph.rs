use std::borrow::Borrow;
use std::cell::{Cell, Ref, RefCell};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Display};
use std::fs::File;
use std::io::Write;
use std::mem::replace;
use std::process::Command;
use std::rc::Rc;
use std::sync::Arc;

use super::datalog_lalr::SemanticError;

use super::ast::{self, InfixLiteral, Operator};

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

#[derive(PartialEq, Debug, Clone)]
pub enum Value {
  Str(Arc<str>),
  Ord(u128),
  Bool(bool),
}

impl Display for Value {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Value::Str(s) => write!(f, "\"{}\"", s),
      Value::Ord(o) => write!(f, "{}", o),
      Value::Bool(b) => write!(f, "{}", b),
    }
  }
}

#[derive(PartialEq, Debug, Clone)]
pub enum Term {
  Var(Arc<str>),
  Str(Arc<str>),
  Ord(u128),
  Bool(bool),
  Any,
}

impl Display for Term {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Term::Var(s) => write!(f, "{}", s),
      Term::Str(s) => write!(f, "\"{}\"", s),
      Term::Ord(o) => write!(f, "{}", o),
      Term::Bool(b) => write!(f, "{}", b),
      Term::Any => write!(f, "_"),
    }
  }
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

  pub fn as_value(&self) -> Option<Value> {
    match self {
      Term::Str(s) => Some(Value::Str(s.clone())),
      Term::Ord(o) => Some(Value::Ord(*o)),
      Term::Bool(b) => Some(Value::Bool(*b)),
      _ => None,
    }
  }
}

#[derive(PartialEq, Debug, Clone, Copy)]
pub enum Cmp {
  EQ,
  NE,
  GT,
  GE,
  LT,
  LE,
}

impl Cmp {
  pub fn from(op: Operator) -> Cmp {
    match op {
      Operator::Equal => Cmp::EQ,
      Operator::NotEqual => Cmp::NE,
      Operator::Greater => Cmp::GT,
      Operator::GreaterEqual => Cmp::GE,
      Operator::Less => Cmp::LT,
      Operator::LessEqual => Cmp::LE,
    }
  }
}

impl Display for Cmp {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Cmp::EQ => write!(f, "="),
      Cmp::NE => write!(f, "!="),
      Cmp::GT => write!(f, ">"),
      Cmp::GE => write!(f, ">="),
      Cmp::LT => write!(f, "<"),
      Cmp::LE => write!(f, "<="),
    }
  }
}

#[derive(PartialEq, Debug, Clone)]
pub enum Atom {
  Pos(Arc<str>, Vec<Term>),
  Neg(Arc<str>, Vec<Term>),
  Constraint { left: Term, cmp: Cmp, right: Term },
}

impl Display for Atom {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Atom::Pos(name, terms) => write!(f, "{}({})", name, terms.iter().map(|t| format!("{}", t)).collect::<Vec<_>>().join(", ")),
      Atom::Neg(name, terms) => write!(f, "~{}({})", name, terms.iter().map(|t| format!("{}", t)).collect::<Vec<_>>().join(", ")),
      Atom::Constraint { left, cmp, right } => write!(f, "{} {} {}", left, cmp, right),
    }
  }
}

impl Atom {
  pub fn predicate(&self) -> Option<(Arc<str>, usize)> {
    match self {
      Atom::Pos(name, terms) => Some((name.clone(), terms.len())),
      Atom::Neg(name, terms) => Some((name.clone(), terms.len())),
      _ => None,
    }
  }
}

#[derive(PartialEq, Clone, Debug)]
pub struct NodeAttributes<T: Clone + Debug> {
  store: Vec<Option<T>>,
}

impl<T: Clone + Debug> NodeAttributes<T> {
  pub fn new() -> Self {
    NodeAttributes { store: Vec::new() }
  }

  pub fn with_capacity(capacity: usize) -> Self {
    NodeAttributes { store: Vec::with_capacity(capacity) }
  }

  pub fn set(&mut self, id: u16, value: T) {
    let id = id as usize;
    if self.store.len() <= id {
      self.store.resize(id + 1, None);
    }
    self.store[id] = Some(value);
  }

  pub fn get(&self, id: u16) -> Option<&T> {
    let id = id as usize;
    if self.store.len() <= id {
      return None;
    }
    (&self.store[id]).as_ref()
  }

  pub fn get_mut(&mut self, id: u16) -> Option<&mut T> {
    let id = id as usize;
    if self.store.len() <= id {
      return None;
    }
    (&mut self.store[id]).as_mut()
  }

  pub fn entry(&mut self, id: u16) -> NodeAttribute<'_, T> {
    let id = id as usize;
    if self.store.len() <= id {
      self.store.resize(id + 1, None);
    }
    NodeAttribute { att: &mut self.store[id] }
  }

  pub fn contains(&self, id: u16) -> bool {
    let id = id as usize;
    self.store.len() > id && self.store[id].is_some()
  }

  pub fn clear(&mut self) {
    self.store.clear();
  }
}

impl<T: Clone + Debug> FromIterator<(u16, T)> for NodeAttributes<T> {
  fn from_iter<I: IntoIterator<Item = (u16, T)>>(iter: I) -> Self {
    let iter = iter.into_iter();
    let (min_size, max_size) = iter.size_hint();
    let capacity = max_size.unwrap_or(min_size);

    let mut store = Vec::with_capacity(capacity);
    for (id, value) in iter {
      if store.len() <= (id as usize) {
        store.resize(id as usize + 1, None);
      }
      store[id as usize] = Some(value);
    }
    NodeAttributes { store }
  }
}

pub struct NodeAttribute<'a, T> {
  att: &'a mut Option<T>,
}

impl<'a, T> NodeAttribute<'a, T> {
  pub fn and_modify(self, modify: impl FnOnce(&mut T)) -> NodeAttribute<'a, T> {
    if let Some(value) = self.att {
      modify(value);
    }
    self
  }

  pub fn or_insert_with(self, value: impl FnOnce() -> T) -> &'a mut T {
    if let Some(val) = self.att {
      val
    } else {
      *self.att = Some(value());
      self.att.as_mut().unwrap()
    }
  }
}

pub struct Node {
  pub id: u16,
  pub kind: NodeKind,
  pub depends_on: RefCell<Vec<Rc<Node>>>,
}

impl Node {
  pub fn new(id: u16, kind: NodeKind) -> Node {
    let depends_on = RefCell::new(Vec::new());
    Node { id, kind, depends_on }
  }

  pub fn depend_on<I: IntoIterator<Item = Rc<Node>>>(&self, iter: I) {
    self.depends_on.borrow_mut().extend(iter);
  }

  pub fn accept<E, V: NodeVisitor<E>>(&self, visitor: &mut V) -> Result<(), E> {
    let id = self.id;
    match &self.kind {
      NodeKind::Store(store) => visitor.visit_store(id, store, self.depends_on.borrow().as_ref()),
      NodeKind::Source(store) => visitor.visit_source(id, store, self.depends_on.borrow().as_ref()),
      NodeKind::Relation { name, attributes } => visitor.visit_relation(id, name, attributes, self.depends_on.borrow().as_ref()),
      NodeKind::Rule { head, body } => visitor.visit_rule(id, head, body, self.depends_on.borrow().as_ref()),
      NodeKind::Component { name, attributes } => visitor.visit_component(id, name, attributes, self.depends_on.borrow().as_ref()),
      NodeKind::Prefetch => visitor.visit_prefetch(id, self.depends_on.borrow().as_ref()),
      NodeKind::Init { name, attributes } => visitor.visit_init(id, name, attributes, self.depends_on.borrow().as_ref()),
    }
  }
}

impl PartialEq for Node {
  fn eq(&self, other: &Self) -> bool {
    self.id == other.id && self.kind == other.kind
  }
}

impl Debug for Node {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("Node").field("id", &self.id).field("kind", &self.kind).finish()
  }
}

#[derive(PartialEq, Debug)]
pub enum NodeKind {
  Store(Arc<str>),
  Source(Arc<str>),
  Relation { name: Arc<str>, attributes: Vec<Arc<Domain>> },
  Rule { head: Atom, body: Vec<Atom> },
  Component { name: Arc<str>, attributes: Vec<Arc<Domain>> },
  Prefetch,
  Init { name: Arc<str>, attributes: Vec<Arc<Domain>> },
}
impl NodeKind {
  pub fn is_component_root(&self) -> bool {
    match self {
      NodeKind::Component { .. } => true,
      _ => false,
    }
  }

  pub fn is_component_exit(&self) -> bool {
    match self {
      NodeKind::Prefetch | NodeKind::Init { .. } => true,
      _ => false,
    }
  }
}

pub struct NodeFactory {
  id: Cell<u16>,
  nodes: HashMap<u16, Rc<Node>>,
}

impl NodeFactory {
  pub fn new() -> Self {
    NodeFactory { id: 0.into(), nodes: HashMap::new() }
  }

  pub fn node(&self, id: u16) -> Option<Rc<Node>> {
    self.nodes.get(&id).cloned()
  }

  pub fn store(&mut self, store: Arc<str>) -> Rc<Node> {
    self.next_node(NodeKind::Store(store))
  }

  pub fn source(&mut self, store: Arc<str>) -> Rc<Node> {
    self.next_node(NodeKind::Source(store))
  }

  pub fn relation(&mut self, name: Arc<str>, attributes: Vec<Arc<Domain>>) -> Rc<Node> {
    self.next_node(NodeKind::Relation { name, attributes })
  }

  pub fn rule(&mut self, head: Atom, body: Vec<Atom>) -> Rc<Node> {
    self.next_node(NodeKind::Rule { head, body })
  }

  pub fn component(&mut self, name: Arc<str>, attributes: Vec<Arc<Domain>>, root: Rc<Node>) -> Rc<Node> {
    let component = self.next_node(NodeKind::Component { name, attributes });
    component.depend_on(Some(root));
    component
  }

  pub fn prefetch(&mut self, node: Rc<Node>) -> Rc<Node> {
    let prefetch = self.next_node(NodeKind::Prefetch);
    prefetch.depend_on(Some(node));
    prefetch
  }

  pub fn init(&mut self, name: Arc<str>, attributes: Vec<Arc<Domain>>) -> Rc<Node> {
    self.next_node(NodeKind::Init { name, attributes })
  }

  fn next_node(&mut self, kind: NodeKind) -> Rc<Node> {
    let id = self.id.update(|id| id + 1);
    let node = Rc::new(Node::new(id, kind));
    self.nodes.insert(id, node.clone());
    node
  }
}

pub trait NodeVisitor<E> {
  fn visit_store(&mut self, id: u16, store: &Arc<str>, depends_on: &Vec<Rc<Node>>) -> Result<(), E>;
  fn visit_source(&mut self, id: u16, store: &Arc<str>, depends_on: &Vec<Rc<Node>>) -> Result<(), E>;
  fn visit_relation(&mut self, id: u16, name: &Arc<str>, attributes: &Vec<Arc<Domain>>, depends_on: &Vec<Rc<Node>>) -> Result<(), E>;
  fn visit_rule(&mut self, id: u16, head: &Atom, body: &Vec<Atom>, depends_on: &Vec<Rc<Node>>) -> Result<(), E>;
  fn visit_component(&mut self, id: u16, name: &Arc<str>, attributes: &Vec<Arc<Domain>>, depends_on: &Vec<Rc<Node>>) -> Result<(), E>;
  fn visit_prefetch(&mut self, id: u16, depends_on: &Vec<Rc<Node>>) -> Result<(), E>;
  fn visit_init(&mut self, id: u16, name: &Arc<str>, attributes: &Vec<Arc<Domain>>, depends_on: &Vec<Rc<Node>>) -> Result<(), E>;
}

pub struct RuleGraph {
  names: HashSet<Arc<str>>,
  relations: HashMap<(Arc<str>, usize), Rc<Node>>,
  rules: HashMap<(Arc<str>, usize), Vec<Rc<Node>>>,
  create: NodeFactory,

  pub domains: HashMap<Arc<str>, Arc<Domain>>,
  pub roots: Vec<Rc<Node>>,
}

impl RuleGraph {
  pub fn new() -> RuleGraph {
    let names = HashSet::new();
    let domains = HashMap::new();
    let relations = HashMap::new();
    let rules = HashMap::new();
    let roots = Vec::new();
    let create = NodeFactory::new();
    RuleGraph {
      names,
      domains,
      relations,
      rules,
      roots,
      create,
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
    self.extract_components()?;
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
          let body = body.iter().flat_map(|a| a.predicate()).collect::<Vec<_>>();
          let known_relations = self.fetch_known_relations(&body);
          let new_relations = self.fetch_relations(&body, &mut relations)?;

          self.check_definitions(&body, known_relations.iter().chain(new_relations.iter()))?;

          node.depend_on(known_relations);
          node.depend_on(new_relations.iter().cloned());

          todo.extend(new_relations);
        }
        _ => todo.extend(node.depends_on.borrow().iter().cloned()),
      }
    }
    Ok(())
  }

  fn fetch_goals(&mut self, relations: &mut Vec<ast::Relation>) -> Result<Vec<Rc<Node>>, SemanticError> {
    let mut goals = Vec::new();
    for relation in relations.extract_if(.., |relation| relation.is_stored()) {
      let store = self.name(relation.store().unwrap().as_ref());
      let signature = relation.signature();
      let name = self.name(signature.name.as_ref());
      let attributes = signature.attributes.iter().map(|s| self.name(s.as_ref())).collect::<Vec<_>>();
      let attributes = self.fetch_attributes(&attributes)?;
      let predicate = (name.clone(), attributes.len());
      let relation = self.create.relation(name, attributes);
      let root = self.create.store(store);
      root.depend_on(Some(relation.clone()));
      self.roots.push(root.clone());
      self.relations.insert(predicate, relation);

      goals.push(root);
    }
    Ok(goals)
  }

  fn fetch_known_relations(&self, body: &[(Arc<str>, usize)]) -> Vec<Rc<Node>> {
    let nodes = body.iter().flat_map(|(name, arity)| self.relations.get(&(name.clone(), *arity))).cloned().collect();
    nodes
  }

  fn fetch_relations(&mut self, body: &[(Arc<str>, usize)], relations: &mut Vec<ast::Relation>) -> Result<Vec<Rc<Node>>, SemanticError> {
    let mut nodes = Vec::new();
    for relation in relations.extract_if(.., |relation| body.iter().any(|(name, arity)| relation.signature().matches(name.as_ref(), *arity))) {
      let signature = relation.signature();
      let name = self.name(signature.name.as_ref());
      let attributes = signature.attributes.iter().map(|s| self.name(s.as_ref())).collect::<Vec<_>>();
      let attributes = self.fetch_attributes(&attributes)?;
      let predicate = (name.clone(), attributes.len());
      let node = self.create.relation(name, attributes);
      if let Some(uri) = relation.source() {
        let source = self.name(uri.as_ref());
        let source = self.create.source(source);
        node.depend_on(Some(source));
      }
      self.relations.insert(predicate, node.clone());
      nodes.push(node);
    }
    Ok(nodes)
  }

  fn fetch_known_rules(&self, predicate: &(Arc<str>, usize)) -> Vec<Rc<Node>> {
    if let Some(nodes) = self.rules.get(predicate) { nodes.clone() } else { Vec::new() }
  }

  fn fetch_rules(&mut self, (name, arity): &(Arc<str>, usize), rules: &mut Vec<ast::Rule>) -> Result<Vec<Rc<Node>>, SemanticError> {
    let mut nodes = Vec::new();
    for rule in rules.extract_if(.., |rule| rule.head.name.as_ref() == name.as_ref() && rule.head.terms.len() == *arity) {
      let predicate = (name.clone(), *arity);

      let mut head = Atom::Pos(self.name(rule.head.name), rule.head.terms.into_iter().map(|term| Term::from(term)).collect());
      let mut body = rule
        .body
        .into_iter()
        .map(|atom| match atom {
          ast::Literal::Positive(atom) => Atom::Pos(self.name(atom.name), atom.terms.into_iter().map(|term| Term::from(term)).collect()),
          ast::Literal::Negative(atom) => Atom::Neg(self.name(atom.name), atom.terms.into_iter().map(|term| Term::from(term)).collect()),
          ast::Literal::Comparative(InfixLiteral { left, op, right }) => Atom::Constraint {
            left: Term::from(left),
            cmp: Cmp::from(op),
            right: Term::from(right),
          },
        })
        .collect::<Vec<_>>();

      let mut counter = 0usize;
      let mut constraints = Vec::new();
      normalize_atom(&mut head, &mut constraints, &mut counter);
      for atom in &mut body {
        normalize_atom(atom, &mut constraints, &mut counter);
      }
      body.extend(constraints);

      let node = self.create.rule(head, body);
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

  fn check_definitions<'a, I: IntoIterator<Item = &'a Rc<Node>>>(&self, body: &[(Arc<str>, usize)], relations: I) -> Result<(), SemanticError> {
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

  pub fn extract_components(&mut self) -> Result<(), SemanticError> {
    let nodes = self.roots.clone();

    let mut tarjan_scc = TarjanSCC::new();

    let mut nodes2sccs: HashMap<u16, u16> = tarjan_scc.find_sccs(&nodes);

    let mut back_edges = self.insert_components(&mut nodes2sccs);

    self.insert_prefetches(&nodes2sccs);

    let mut inhibited_edges = Vec::new();
    while let Some(edge) = back_edges.pop() {
      inhibited_edges.push(edge);

      tarjan_scc.inhibit(&inhibited_edges);

      let mut nodes2sccs: HashMap<u16, u16> = tarjan_scc.find_sccs(&nodes);
      back_edges = self.insert_components(&mut nodes2sccs);
      back_edges.retain(|edge| !inhibited_edges.contains(edge));
    }

    let mut printer = RuleGraphPrinter::new();
    self.accept(&mut printer).unwrap();
    printer.dump("graph.dot").unwrap();

    Ok(())
  }

  fn insert_prefetches(&mut self, nodes2sccs: &HashMap<u16, u16>) {
    for (node_id, component_id) in nodes2sccs {
      if let Some(node) = self.create.node(*node_id)
        && let Some(component) = self.create.node(*component_id)
      {
        let mut prefetches = Vec::new();
        let mut inits = HashMap::new();
        for dep in node.depends_on.borrow().iter().cloned() {
          if *component_id == dep.id {
            continue;
          }
          let dep_component_id = nodes2sccs.get(&dep.id);
          if dep_component_id.map_or(true, |dep_component_id: &u16| dep_component_id != component_id) {
            if let NodeKind::Relation { name, attributes } = &node.kind {
              let init = self.create.init(name.clone(), attributes.clone());
              inits.entry(*node_id).or_insert_with(|| init.clone()).depend_on(Some(dep.clone()));
            } else {
              let prefetch = self.create.prefetch(dep.clone());
              prefetches.push(prefetch);
            }
          }
        }
        for prefetch in prefetches {
          component.depend_on(Some(prefetch));
        }
        for (_, init) in inits {
          component.depend_on(Some(init.clone()));

          let deps = init.depends_on.borrow().iter().map(|dep| dep.id).collect::<Vec<_>>();
          node.depends_on.borrow_mut().retain(|dep| !deps.contains(&dep.id));
          node.depend_on(Some(init));
        }
      }
    }
  }

  fn insert_components(&mut self, nodes2sccs: &mut HashMap<u16, u16>) -> Vec<(Rc<Node>, u16)> {
    let mut back_edges = Vec::new();
    let mut components = HashMap::new();
    let mut component_ids = HashMap::new();
    let mut todo = VecDeque::new();
    let mut done = HashSet::new();
    for root in &mut self.roots {
      let root_id = root.id;
      todo.push_back(root.clone());
      if let Some(component_id) = nodes2sccs.get(&root_id) {
        if let NodeKind::Component { .. } = &root.kind {
          components.insert(root_id, root.clone());
          done.insert(root.id);
        } else {
          let NodeKind::Relation { name, attributes, .. } = &root.kind else {
            panic!("component heads only for relations")
          };
          *root = self.create.component(name.clone(), attributes.clone(), root.clone());
          components.insert(root_id, root.clone());
          component_ids.insert(*component_id, root.id);
          done.insert(root.id);
        }
      }
    }
    while let Some(node) = todo.pop_front() {
      let node_id = node.id;
      done.insert(node_id);
      let node_component_id = if let Some(component_id) = nodes2sccs.get(&node_id) { *component_id } else { node_id };
      for dep in &mut *node.depends_on.borrow_mut() {
        let dep_id = dep.id;

        if !done.contains(&dep_id) {
          todo.push_back(dep.clone());
        }
        if let Some(component) = components.get(&dep_id) {
          *dep = component.clone();
          let edge = (node.clone(), dep.id);
          if !back_edges.contains(&edge) {
            back_edges.push(edge);
          }
        } else if let Some(component_id) = nodes2sccs.get(&dep_id) {
          if *component_id != node_component_id {
            if let NodeKind::Component { .. } = &dep.kind {
              components.insert(dep_id, dep.clone());
              done.insert(dep.id);
            } else {
              let NodeKind::Relation { name, attributes, .. } = &dep.kind else {
                panic!("component heads only for relations")
              };
              *dep = self.create.component(name.clone(), attributes.clone(), dep.clone());
              component_ids.insert(*component_id, dep.id);
              components.insert(dep_id, dep.clone());
              done.insert(dep.id);
            }
          }
        }
      }
    }

    for value in nodes2sccs.values_mut() {
      if let Some(component_id) = component_ids.get(value) {
        *value = *component_id;
      }
    }
    back_edges
  }

  pub fn accept<E, V: RuleGraphVisitor<E>>(&self, visitor: &mut V) -> Result<(), E> {
    visitor.visit_graph(self)
  }
}

pub fn normalize_atom(atom: &mut Atom, constraints: &mut Vec<Atom>, counter: &mut usize) {
  let terms = match atom {
    Atom::Pos(_, terms) | Atom::Neg(_, terms) => terms,
    _ => return,
  };
  for term in terms {
    match term {
      term @ Term::Bool(_) | term @ Term::Ord(_) | term @ Term::Str(_) => {
        *counter += 1;
        let var_name: Arc<str> = Arc::from(format!("@{}", counter));
        let var = Term::Var(var_name);
        let val = replace(term, var.clone());

        constraints.push(Atom::Constraint { left: var, cmp: Cmp::EQ, right: val });
      }
      _ => continue,
    }
  }
}

enum ANode<'a> {
  Fix(u16, Ref<'a, Vec<Rc<Node>>>),
  Mod(u16, Vec<Rc<Node>>),
}

impl<'a> ANode<'a> {
  pub fn depends_on<'b: 'a>(&'b self) -> &'a Vec<Rc<Node>> {
    match self {
      ANode::Fix(_, deps) => deps.as_ref(),
      ANode::Mod(_, nodes) => nodes,
    }
  }

  pub fn id(&self) -> u16 {
    match self {
      ANode::Fix(id, _) | ANode::Mod(id, _) => *id,
    }
  }
}

struct TarjanSCC {
  index: usize,
  stack: Vec<u16>,
  indices: NodeAttributes<usize>,
  low_links: NodeAttributes<usize>,
  on_stack: HashSet<u16>,
  overrides: HashMap<u16, Vec<Rc<Node>>>,
  sccs: Vec<Vec<u16>>,
}

impl TarjanSCC {
  pub fn new() -> Self {
    Self {
      index: 0,
      stack: Vec::new(),
      indices: NodeAttributes::new(),
      low_links: NodeAttributes::new(),
      on_stack: HashSet::new(),
      overrides: HashMap::new(),
      sccs: Vec::new(),
    }
  }

  fn inhibit(&mut self, inhibited_edges: &Vec<(Rc<Node>, u16)>) {
    for (node, to) in inhibited_edges {
      self.overrides.insert(node.id, node.depends_on.borrow().iter().filter(|dep| dep.id != *to).cloned().collect());
    }
  }

  pub fn anode<'a>(&self, node: &'a Rc<Node>) -> ANode<'a> {
    if let Some(depends_on) = self.overrides.get(&node.id) {
      ANode::Mod(node.id, depends_on.clone())
    } else {
      ANode::Fix(node.id, node.depends_on.borrow())
    }
  }

  pub fn find_sccs(&mut self, nodes: &Vec<Rc<Node>>) -> HashMap<u16, u16> {
    self.index = 0;
    self.stack.clear();
    self.indices.clear();
    self.low_links.clear();
    self.on_stack.clear();
    self.sccs.clear();

    for node in nodes {
      if !self.indices.contains(node.id) {
        let anode = self.anode(node);
        self.strong_connect(anode);
      }
    }
    self
      .sccs
      .iter()
      .filter(|group| group.len() > 1)
      .flat_map(|group| {
        let group_id = group[0];
        group.iter().map(move |node_id| (*node_id, group_id))
      })
      .collect()
  }

  fn strong_connect(&mut self, node: ANode) {
    let node_id = node.id();

    self.init_node(node_id);
    self.push_node(node_id);

    for dep in node.depends_on() {
      self.handle_dep(node_id, dep);
    }

    if self.low_links.get(node_id) == self.indices.get(node_id) {
      self.build_scc(node_id);
    }
  }

  fn init_node(&mut self, node_id: u16) {
    self.indices.set(node_id, self.index);
    self.low_links.set(node_id, self.index);
    self.index += 1;
  }

  fn push_node(&mut self, node_id: u16) {
    self.stack.push(node_id);
    self.on_stack.insert(node_id);
  }

  fn pop_node(&mut self) -> Option<u16> {
    let node_id = self.stack.pop()?;
    self.on_stack.remove(&node_id);
    Some(node_id)
  }

  fn handle_dep(&mut self, node_id: u16, dep: &Rc<Node>) {
    let dep_id = dep.id;
    if !self.indices.contains(dep_id) {
      let anode = self.anode(dep);
      self.strong_connect(anode);
      let min_low = *self.low_links.get(node_id).unwrap().min(self.low_links.get(dep_id).unwrap());
      self.low_links.set(node_id, min_low);
    } else if self.on_stack.contains(&dep_id) {
      let min_low = *self.low_links.get(node_id).unwrap().min(self.indices.get(dep_id).unwrap());
      self.low_links.set(node_id, min_low);
    }
  }

  fn build_scc(&mut self, node_id: u16) {
    let mut scc = Vec::new();
    while let Some(n_id) = self.pop_node() {
      scc.push(n_id);
      if n_id == node_id {
        break;
      }
    }
    self.sccs.push(scc);
  }
}
pub trait RuleGraphVisitor<E> {
  fn visit_graph(&mut self, graph: &RuleGraph) -> Result<(), E>;
}

struct RuleGraphPrinter {
  buffer: String,
  visited: HashSet<u16>,
}

impl RuleGraphPrinter {
  pub fn new() -> Self {
    RuleGraphPrinter {
      buffer: String::new(),
      visited: HashSet::new(),
    }
  }
  pub fn dump(&self, path: &str) -> std::io::Result<()> {
    let mut file = File::create(path)?;
    writeln!(file, "{}", self.buffer)?;
    drop(file);
    let png_path = path.replace(".dot", ".png");
    Command::new("dot").arg("-Tpng").arg(path).arg("-o").arg(png_path).output()?;
    Ok(())
  }
}

impl RuleGraphVisitor<()> for RuleGraphPrinter {
  fn visit_graph(&mut self, graph: &RuleGraph) -> Result<(), ()> {
    self.buffer.push_str("digraph G {{");
    for root in &graph.roots {
      root.accept(self)?;
    }
    self.buffer.push_str("}}");
    Ok(())
  }
}

impl NodeVisitor<()> for RuleGraphPrinter {
  fn visit_store(&mut self, id: u16, store: &Arc<str>, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }
    self.buffer.push_str(&format!("  {} [label=\"{}: {}\",shape=triangle];\n", id, id, store));

    for dep in depends_on {
      self.buffer.push_str(&format!("  {} -> {};\n", id, dep.id));
      dep.accept(self)?;
    }
    Ok(())
  }

  fn visit_source(&mut self, id: u16, store: &Arc<str>, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }
    self.buffer.push_str(&format!("  {} [label=\"{}: {}\",shape=invtriangle];\n", id, id, store));

    for dep in depends_on {
      self.buffer.push_str(&format!("  {} -> {};\n", id, dep.id));
      dep.accept(self)?;
    }
    Ok(())
  }

  fn visit_relation(&mut self, id: u16, name: &Arc<str>, attributes: &Vec<Arc<Domain>>, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }
    self.buffer.push_str(&format!("  {} [label=\"{}: {}/{}\"];\n", id, id, name, attributes.len()));

    for dep in depends_on {
      self.buffer.push_str(&format!("  {} -> {};\n", id, dep.id));
      dep.accept(self)?;
    }

    Ok(())
  }

  fn visit_rule(&mut self, id: u16, head: &Atom, body: &Vec<Atom>, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }
    self.buffer.push_str(&format!(
      "  {} [label=\"{}: {} <- {}\"];\n",
      id,
      id,
      head,
      body.iter().map(|a| a.to_string()).collect::<Vec<String>>().join(" & ").replace("\"", "\\\"")
    ));

    for dep in depends_on {
      self.buffer.push_str(&format!("  {} -> {};\n", id, dep.id));
      dep.accept(self)?;
    }
    Ok(())
  }

  fn visit_component(&mut self, id: u16, _name: &Arc<str>, _attributes: &Vec<Arc<Domain>>, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }

    for dep in depends_on {
      if dep.kind.is_component_exit() {
        self.buffer.push_str(&format!("  {} -> {}  [style=dashed];\n", id, dep.id));
      } else {
        self.buffer.push_str(&format!("  {} -> {};\n", id, dep.id));
      }
      dep.accept(self)?;
    }
    Ok(())
  }

  fn visit_prefetch(&mut self, id: u16, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }

    self.buffer.push_str(&format!("  {} [label=\"{}: prefetch\"];\n", id, id));

    for dep in depends_on {
      self.buffer.push_str(&format!("  {} -> {} [style=dashed];\n", id, dep.id));
      dep.accept(self)?;
    }
    Ok(())
  }

  fn visit_init(&mut self, id: u16, name: &Arc<str>, attributes: &Vec<Arc<Domain>>, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }
    self.buffer.push_str(&format!("  {} [label=\"{}: init {}/{}\"];\n", id, id, name, attributes.len()));

    for dep in depends_on {
      self.buffer.push_str(&format!("  {} -> {};\n", id, dep.id));
      dep.accept(self)?;
    }

    Ok(())
  }
}

#[cfg(test)]
mod test {

  use super::*;
  use crate::expect;
  use crate::testutil::core::{Locatable, expect};
  use crate::testutil::matchers::Matcher;
  use crate::testutil::matchers::contains::Contains;
  use crate::testutil::matchers::empty::Empty;
  use crate::testutil::matchers::equal_to::EqualTo;

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
        expect!(goals).to_contain(vec![store("out", relation("goal", vec![("domain", 2, "out")]))]);
        expect!(relations.len()).to_equal(0);
      }

      #[test]
      fn from_multiple_out() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![ast::relation("goal1", vec!["domain"]).stored_to("out1"), ast::relation("goal2", vec!["domain"]).stored_to("out2")];
        let goals = graph.fetch_goals(&mut relations).unwrap();
        expect!(goals).to_contain(vec![
          store("out1", relation("goal1", vec![("domain", 2, "out")])),
          store("out2", relation("goal2", vec![("domain", 2, "out")])),
        ]);
        expect!(relations.len()).to_equal(0);
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
        expect!(goals).to_contain(vec![store("out", relation("goal1", vec![("domain", 2, "out")]))]);
        expect!(relations.len()).to_equal(2);
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
        expect!(nodes).to_contain(vec![relation("rel", vec![("domain", 2, "out")])]);
        expect!(relations.len()).to_equal(0);
      }

      #[test]
      fn from_single_stored() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![ast::relation("rel", vec!["domain"]).loaded_from("in")];
        let body = vec![(name("rel"), 1)];
        let nodes = graph.fetch_relations(&body, &mut relations).unwrap();
        expect!(nodes).to_contain(vec![relation("rel", vec![("domain", 2, "out")])]);
        expect!(relations.len()).to_equal(0);
      }

      #[test]
      fn from_single_loaded() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![ast::relation("rel", vec!["domain"]).stored_to("out")];
        let body = vec![(name("rel"), 1)];
        let nodes = graph.fetch_relations(&body, &mut relations).unwrap();
        expect!(nodes).to_contain(vec![relation("rel", vec![("domain", 2, "out")])]);
        expect!(relations.len()).to_equal(0);
      }

      #[test]
      fn from_multiple() {
        let mut graph = RuleGraph::new();

        let domain = ast::domain("domain", 2).loaded_from("out");
        graph.register_domains(vec![domain]).unwrap();

        let mut relations = vec![ast::relation("rel1", vec!["domain"]), ast::relation("rel2", vec!["domain"])];
        let body = vec![(name("rel1"), 1)];
        let nodes = graph.fetch_relations(&body, &mut relations).unwrap();
        expect!(nodes).to_contain(vec![relation("rel1", vec![("domain", 2, "out")])]);
        expect!(relations.len()).to_equal(1);

        let body = vec![(name("rel2"), 1)];
        let nodes = graph.fetch_relations(&body, &mut relations).unwrap();
        expect!(nodes).to_contain(vec![relation("rel2", vec![("domain", 2, "out")])]);
        expect!(relations.len()).to_equal(0);
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
        expect!(nodes).to_be_empty();
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
        expect!(nodes).to_contain(vec![relation("rel", vec![("domain", 2, "out")])]);
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
        expect!(nodes).to_contain(vec![relation("rel1", vec![("domain", 2, "out")]), relation("rel2", vec![("domain", 2, "out")])]);
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
        let head = Atom::Pos(name("rel1"), vec![Term::Var(name("X"))]);
        let body = vec![Atom::Pos(name("rel2"), vec![Term::Var(name("X"))])];
        expect!(nodes).to_contain(vec![rule(head, body)]);
        expect!(rules.len()).to_equal(0);
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
        let head = Atom::Pos(name("rel1"), vec![Term::Var(name("X"))]);
        let body = vec![Atom::Pos(name("rel2"), vec![Term::Var(name("X"))])];
        expect!(nodes).to_contain(vec![rule(head, body)]);
        expect!(rules.len()).to_equal(1);

        let nodes = graph.fetch_rules(&pred2, &mut rules).unwrap();
        let head = Atom::Pos(name("rel2"), vec![Term::Var(name("X"))]);
        let body = vec![Atom::Pos(name("rel3"), vec![Term::Var(name("X"))])];
        expect!(nodes).to_contain(vec![rule(head, body)]);
        expect!(rules.len()).to_equal(0);
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
        expect!(nodes).to_be_empty();
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
        let head = Atom::Pos(name("rel1"), vec![Term::Var(name("X"))]);
        let body = vec![Atom::Pos(name("rel2"), vec![Term::Var(name("X"))])];
        expect!(nodes).to_contain(vec![rule(head, body)]);
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
        let head1 = Atom::Pos(name("rel1"), vec![Term::Var(name("X"))]);
        let body1 = vec![Atom::Pos(name("rel2"), vec![Term::Var(name("X"))])];
        let head2 = Atom::Pos(name("rel1"), vec![Term::Var(name("X"))]);
        let body2 = vec![Atom::Pos(name("rel3"), vec![Term::Var(name("X"))])];
        expect!(nodes).to_contain(vec![rule(head1, body1), rule(head2, body2)]);
      }
    }
  }

  #[derive(Debug)]
  struct StoreMatcher {
    uri: &'static str,
    relation: RelationMatcher,
  }

  impl Matcher<Rc<Node>> for StoreMatcher {
    fn matches(&self, actual: &Rc<Node>) -> bool {
      match &actual.kind {
        NodeKind::Store(store) => store.as_ref() == self.uri && self.relation.matches(actual.depends_on.borrow().first().unwrap()),
        _ => false,
      }
    }
  }

  fn store(uri: &'static str, relation: RelationMatcher) -> StoreMatcher {
    StoreMatcher { uri, relation }
  }

  #[derive(Debug)]
  struct RelationMatcher {
    name: &'static str,
    attributes: Vec<(&'static str, u128, &'static str)>,
  }

  impl Matcher<Rc<Node>> for RelationMatcher {
    fn matches(&self, actual: &Rc<Node>) -> bool {
      match &actual.kind {
        NodeKind::Relation { name, attributes } => {
          name.as_ref() == self.name
            && attributes
              .iter()
              .zip(&self.attributes)
              .all(|(a, (name, size, uri))| a.name.as_ref() == *name && a.size == *size && a.uri.as_ref() == *uri)
        }

        _ => false,
      }
    }
  }

  fn relation(name: &'static str, attributes: Vec<(&'static str, u128, &'static str)>) -> RelationMatcher {
    RelationMatcher { name, attributes }
  }

  #[derive(Debug)]
  struct RuleMatcher {
    head: Atom,
    body: Vec<Atom>,
  }

  impl Matcher<Rc<Node>> for RuleMatcher {
    fn matches(&self, actual: &Rc<Node>) -> bool {
      match &actual.kind {
        NodeKind::Rule { head, body } => head == &self.head && body == &self.body,
        _ => false,
      }
    }
  }

  fn rule(head: Atom, body: Vec<Atom>) -> RuleMatcher {
    RuleMatcher { head, body }
  }

  fn pred<T: AsRef<str>>(name: T, arity: usize) -> (Arc<str>, usize) {
    (Arc::from(name.as_ref()), arity)
  }

  fn name<T: AsRef<str>>(name: T) -> Arc<str> {
    Arc::from(name.as_ref())
  }
}
