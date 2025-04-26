use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::mem::replace;
use std::rc::Rc;
use std::sync::Arc;

use oxidd::bdd::BDDManagerRef;
use oxidd::util::OutOfMemory;

use crate::bdd::domain::BDDDomain;
use crate::util::compiler::ExactlyOnce;

use super::graph::{Atom, Cmp, Domain, Node, NodeAttributes, NodeKind, NodeVisitor, RuleGraph, RuleGraphVisitor, Term, Value};

pub struct DomainTypeFactory {
  types: HashMap<Arc<str>, u16>,
}

impl DomainTypeFactory {
  pub fn new() -> Self {
    let types = HashMap::new();
    DomainTypeFactory { types }
  }

  pub fn new_type_for(&mut self, base_type: impl Into<Arc<str>>) -> DomainType {
    let base_type = base_type.into();
    let number = self.types.entry(base_type.clone()).or_insert(0);
    *number += 1;
    DomainType(base_type.clone(), *number)
  }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Variable {
  pub name: Arc<str>,
  pub domains: Vec<Arc<BDDDomain>>,
}

impl Variable {
  pub fn new(name: Arc<str>, domains: Vec<Arc<BDDDomain>>) -> Self {
    Variable { name, domains }
  }

  pub fn domains(&self) -> &[Arc<BDDDomain>] {
    &self.domains
  }

  pub fn has_type(&self, rel_type: &RelationType) -> bool {
    self
      .domains
      .iter()
      .zip(rel_type.domains())
      .all(|(domain, domain_type)| domain.name == domain_type.0 && domain.id == domain_type.1)
  }
}

pub struct VariableEntry<'a> {
  entry: Entry<'a, u16, Variable>,
  names: &'a mut HashMap<Arc<str>, u16>,
}

impl<'a> VariableEntry<'a> {
  pub fn or_new<E>(self, name: &Arc<str>, domains: impl FnOnce() -> Result<Vec<Arc<BDDDomain>>, E>) -> Result<&'a mut Variable, E> {
    match self.entry {
      Entry::Vacant(entry) => {
        let number = self.names.entry(name.clone()).or_insert(0);
        *number += 1;
        let name = Arc::from(format!("{}_{}", name, number));
        let domains = domains()?;
        let var = entry.insert(Variable::new(name, domains));
        Ok(var)
      }
      Entry::Occupied(entry) => Ok(entry.into_mut()),
    }
  }
}

#[derive(Debug, Clone)]
pub struct VariableContext {
  names: HashMap<Arc<str>, u16>,
  primary: HashMap<u16, Variable>,
  secondary: HashMap<u16, Vec<Variable>>,
}

impl VariableContext {
  pub fn new() -> Self {
    let names = HashMap::new();
    let primary = HashMap::new();
    let secondary = HashMap::new();
    VariableContext { names, primary, secondary }
  }

  pub fn primary(&mut self, id: u16) -> VariableEntry<'_> {
    let entry = self.primary.entry(id);
    VariableEntry { entry, names: &mut self.names }
  }

  pub fn add(&mut self, id: u16, name: &Arc<str>, domains: Vec<Arc<BDDDomain>>) -> &mut Variable {
    let variables = self.secondary.entry(id).or_insert_with(Vec::new);
    if let Some(pos) = variables.iter().position(|var| &var.name == name && &var.domains == &domains) {
      return &mut variables[pos];
    }

    let number = self.names.entry(name.clone()).or_insert(0);
    *number += 1;
    let name = Arc::from(format!("{}_{}", name, number));

    variables.push(Variable::new(name, domains));
    variables.last_mut().unwrap()
  }

  pub fn temp(&mut self, name: &Arc<str>, domains: Vec<Arc<BDDDomain>>) -> Variable {
    let number = self.names.entry(name.clone()).or_insert(0);
    *number += 1;
    let name = Arc::from(format!("{}_{}", name, number));
    Variable::new(name, domains)
  }

  pub fn require(&self, id: u16, rel_type: &RelationType) -> Option<&Variable> {
    self
      .primary
      .get(&id)
      .filter(|var| var.has_type(rel_type))
      .or_else(|| self.secondary.get(&id).and_then(|vars| vars.iter().find(|var| var.has_type(rel_type))))
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

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct DomainType(Arc<str>, u16);

impl Display for DomainType {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}_{}", self.0, self.1)
  }
}

#[derive(Clone, Debug, PartialEq)]
pub struct RelationType(Vec<DomainType>);

impl Display for RelationType {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "({})", self.0.iter().map(|domain| domain.to_string()).collect::<Vec<_>>().join(", "))
  }
}

impl RelationType {
  pub fn domains(&self) -> &[DomainType] {
    &self.0
  }
}

#[derive(Clone, Debug)]
pub struct TypeBindings {
  pub primary: RelationType,
  pub secondary: Vec<RelationType>,
  pub parts: Vec<RelationType>,
  pub bound: Vec<(DomainType, Cmp, Term)>,
}

impl TypeBindings {
  pub fn new(primary: RelationType) -> Self {
    let secondary = Vec::new();
    let parts = Vec::new();
    let bound = Vec::new();
    TypeBindings { primary, secondary, parts, bound }
  }

  fn require(&mut self, rel_type: RelationType) {
    if self.primary != rel_type && !self.secondary.contains(&rel_type) {
      self.secondary.push(rel_type.clone());
    }
  }

  pub fn satisfies(&self, rel_type: &RelationType) -> bool {
    &self.primary == rel_type || self.secondary.contains(rel_type)
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
  Iter { current: Variable, next: Variable, body: Vec<BIRInst> },
  Phi { to: Variable, left: Variable, right: Variable },
  Load { to: Variable, from: Location },
  Store { from: Variable, to: Location },
  Copy { to: Variable, from: Variable },
  Project { to: Variable, from: Variable },
  Select { to: Variable, from: Variable, by: Vec<(Arc<BDDDomain>, Cmp, Value)> },
  Join { to: Variable, left: Variable, right: Variable },
  Union { to: Variable, left: Variable, right: Variable },
}

impl BIRInst {
  pub fn accept<E, T: BIRVisitor<E>>(&self, visitor: &mut T) -> Result<(), E> {
    use BIRInst::*;
    match self {
      Iter { current, next, body } => visitor.iter(current, next, body),
      Phi { to, left, right } => visitor.phi(to, left, right),
      Load { to, from } => visitor.load(to, from),
      Store { from, to } => visitor.store(from, to),
      Copy { to, from } => visitor.copy(to, from),
      Project { to, from } => visitor.project(to, from),
      Select { to, from, by } => visitor.select(to, from, by),
      Join { to, left, right } => visitor.join(to, left, right),
      Union { to, left, right } => visitor.union(to, left, right),
    }
  }
}

pub struct TypeAnalyzer {
  domains: DomainTypeFactory,
  types: NodeAttributes<TypeBindings>,
  visited: HashSet<u16>,
}

impl TypeAnalyzer {
  pub fn new() -> TypeAnalyzer {
    let domains = DomainTypeFactory::new();
    let types = NodeAttributes::new();
    let visited = HashSet::new();
    TypeAnalyzer { domains, types, visited }
  }

  pub fn types(self) -> NodeAttributes<TypeBindings> {
    self.types
  }
}

impl RuleGraphVisitor<()> for TypeAnalyzer {
  fn visit_graph(&mut self, graph: &RuleGraph) -> Result<(), ()> {
    for root in &graph.roots {
      root.accept(self)?;
    }
    Ok(())
  }
}

impl NodeVisitor<()> for TypeAnalyzer {
  fn visit_store(&mut self, id: u16, _store: &Arc<str>, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }

    for dep in depends_on {
      dep.accept(self)?;
    }

    Ok(())
  }

  fn visit_source(&mut self, id: u16, _store: &Arc<str>, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }

    for dep in depends_on {
      dep.accept(self)?;
    }

    Ok(())
  }

  fn visit_relation(&mut self, id: u16, _name: &Arc<str>, attributes: &Vec<Arc<Domain>>, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }
    let rel_type = self
      .types
      .entry(id)
      .or_insert_with(|| {
        let domain_types = attributes.iter().map(|domain| self.domains.new_type_for(domain.name.clone())).collect();
        TypeBindings::new(RelationType(domain_types))
      })
      .primary
      .clone();

    for dep in depends_on {
      self
        .types
        .entry(dep.id)
        .and_modify(|bindings| bindings.require(rel_type.clone()))
        .or_insert_with(|| TypeBindings::new(rel_type.clone()));
      dep.accept(self)?;
    }
    Ok(())
  }

  fn visit_rule(&mut self, id: u16, head: &Atom, body: &Vec<Atom>, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }
    let Atom::Pos(_h_name, h_terms) = head else {
      panic!("semantic analysis failure: rule head is not a positive atom");
    };
    let TypeBindings { primary, parts, bound, .. } = self.types.get_mut(id).expect(&format!("type analysis failure: missing type for node {}", id));

    let mut bindings = HashMap::new();
    for (term, binding) in h_terms
      .iter()
      .zip(primary.domains())
      .filter_map(|(term, domain)| if let Term::Var(variable) = term { Some((variable.clone(), domain.clone())) } else { None })
    {
      bindings.insert(term, binding);
    }

    let mut node_types = Vec::with_capacity(body.len());
    for atom in body {
      match atom {
        Atom::Pos(a_name, a_terms) | Atom::Neg(a_name, a_terms) => {
          let (id, attributes) = depends_on
            .iter()
            .find_map(|node| {
              let (name, attributes) = match &node.kind {
                NodeKind::Relation { name, attributes, .. } | NodeKind::Component { name, attributes } => (name, attributes),
                _ => return None,
              };
              if name == a_name && attributes.len() == a_terms.len() {
                Some((node.id, attributes.clone()))
              } else {
                None
              }
            })
            .expect(&format!("semantic analysis failure: no relation for atom {}", atom));

          let mut domain_types = Vec::new();
          for (term, domain) in a_terms.iter().zip(attributes.iter()) {
            let domain = if let Term::Var(variable) = term {
              bindings.entry(variable.clone()).or_insert_with(|| self.domains.new_type_for(domain.name.clone())).clone()
            } else {
              self.domains.new_type_for(domain.name.clone())
            };
            domain_types.push(domain);
          }
          let rel_type = RelationType(domain_types);
          parts.push(rel_type.clone());
          node_types.push((id, rel_type));
        }
        Atom::Constraint {
          left: Term::Var(var),
          cmp,
          right: value,
        } => {
          if let Some(binding) = bindings.get(var) {
            bound.push((binding.clone(), *cmp, value.clone()));
          } else {
            todo!("unsupported atom type");
          }
        }
        _ => todo!("unsupported atom type"),
      }
    }
    for (id, rel_type) in node_types {
      self
        .types
        .entry(id)
        .and_modify(|bindings| bindings.require(rel_type.clone()))
        .or_insert_with(|| TypeBindings::new(rel_type.clone()));
    }

    for dep in depends_on {
      dep.accept(self)?;
    }

    Ok(())
  }

  fn visit_component(&mut self, id: u16, _name: &Arc<str>, attributes: &Vec<Arc<Domain>>, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }

    let rel_type = self
      .types
      .entry(id)
      .or_insert_with(|| {
        let domain_types = attributes.iter().map(|domain| self.domains.new_type_for(domain.name.clone())).collect();
        TypeBindings::new(RelationType(domain_types))
      })
      .primary
      .clone();

    let root = depends_on
      .iter()
      .cloned()
      .filter(|node| if let NodeKind::Relation { .. } = node.kind { true } else { false })
      .collect::<ExactlyOnce<_>>()
      .expect("semantic analysis failure: component must have exactly one component root");

    root.accept(self)?;

    self
      .types
      .entry(root.id)
      .and_modify(|bindings| bindings.require(rel_type.clone()))
      .or_insert_with(|| TypeBindings::new(rel_type.clone()));

    let init = depends_on
      .iter()
      .cloned()
      .filter(|node| if let NodeKind::Init { .. } = node.kind { true } else { false })
      .collect::<ExactlyOnce<_>>()
      .expect("semantic analysis failure: component must have exactly one init node");

    init.accept(self)?;

    self
      .types
      .entry(init.id)
      .and_modify(|bindings| bindings.require(rel_type.clone()))
      .or_insert_with(|| TypeBindings::new(rel_type.clone()));

    Ok(())
  }

  fn visit_prefetch(&mut self, id: u16, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }

    for dep in depends_on {
      dep.accept(self)?;
    }
    Ok(())
  }

  fn visit_init(&mut self, id: u16, _name: &Arc<str>, attributes: &Vec<Arc<Domain>>, depends_on: &Vec<Rc<Node>>) -> Result<(), ()> {
    if !self.visited.insert(id) {
      return Ok(());
    }
    let rel_type = self
      .types
      .entry(id)
      .or_insert_with(|| {
        let domain_types = attributes.iter().map(|domain| self.domains.new_type_for(domain.name.clone())).collect();
        TypeBindings::new(RelationType(domain_types))
      })
      .primary
      .clone();

    for dep in depends_on {
      self
        .types
        .entry(dep.id)
        .and_modify(|bindings| bindings.require(rel_type.clone()))
        .or_insert_with(|| TypeBindings::new(rel_type.clone()));
      dep.accept(self)?;
    }
    Ok(())
  }
}

pub struct BIRGenerator {
  manager: BDDManagerRef,
  types: NodeAttributes<TypeBindings>,
  domains: HashMap<Arc<str>, crate::bdd::domain::Domain>,
  variables: VariableContext,
  instructions: Vec<BIRInst>,
  visited: HashSet<u16>,
}

impl BIRGenerator {
  pub fn new(manager: BDDManagerRef, types: NodeAttributes<TypeBindings>) -> BIRGenerator {
    let domains = HashMap::new();
    let variables = VariableContext::new();
    let instructions = Vec::new();
    let visited = HashSet::new();
    BIRGenerator {
      manager,
      types,
      domains,
      variables,
      instructions,
      visited,
    }
  }

  pub fn ir(self) -> BIRProg {
    BIRProg::new(self.instructions)
  }
}

impl RuleGraphVisitor<OutOfMemory> for BIRGenerator {
  fn visit_graph(&mut self, graph: &RuleGraph) -> Result<(), OutOfMemory> {
    self.domains = graph
      .domains
      .iter()
      .map(|(_, domain)| {
        let Domain { name, size, uri } = domain.as_ref();
        let domain = crate::bdd::domain::Domain::new(self.manager.clone(), name.clone(), *size).loaded_from(uri.clone());
        (name.clone(), domain)
      })
      .collect();
    for root in &graph.roots {
      root.accept(self)?;
    }
    Ok(())
  }
}

impl NodeVisitor<OutOfMemory> for BIRGenerator {
  fn visit_store(&mut self, id: u16, store: &Arc<str>, depends_on: &Vec<Rc<Node>>) -> Result<(), OutOfMemory> {
    if !self.visited.insert(id) {
      return Ok(());
    }

    let relation = depends_on
      .iter()
      .cloned()
      .collect::<ExactlyOnce<_>>()
      .expect("semantic analysis failure: store must have exactly one dependency equal to the relation to be stored");
    relation.accept(self)?;

    let var = self
      .variables
      .primary
      .get(&relation.id)
      .expect(&format!("ir generation failure: missing variable for {}", relation.id))
      .clone();

    let uri = Location::from(store.as_ref());
    self.instructions.push(BIRInst::Store { from: var, to: uri });
    Ok(())
  }

  fn visit_source(&mut self, id: u16, store: &Arc<str>, depends_on: &Vec<Rc<Node>>) -> Result<(), OutOfMemory> {
    if !self.visited.insert(id) {
      return Ok(());
    }

    let primary_type = self.types.get(id).expect(&format!("type analysis failure: missing type for node {}", id)).primary.clone();

    let var = self
      .variables
      .primary(id)
      .or_new(store, || {
        let domains = primary_type
          .domains()
          .iter()
          .map(|DomainType(name, id)| {
            Ok(
              self
                .domains
                .get_mut(name)
                .map(|base| base.instance(*id))
                .expect(&format!("type analysis failure: missing domain {}", name))?,
            )
          })
          .try_collect::<Vec<_>>()?;
        Ok(domains)
      })?
      .clone();

    let uri = Location::from(store.as_ref());
    self.instructions.push(BIRInst::Load { to: var.clone(), from: uri });

    if depends_on.len() != 0 {
      panic!("semantic analysis failure: source must not have a dependency");
    }

    Ok(())
  }

  fn visit_relation(&mut self, id: u16, name: &Arc<str>, _attributes: &Vec<Arc<Domain>>, depends_on: &Vec<Rc<Node>>) -> Result<(), OutOfMemory> {
    if !self.visited.insert(id) {
      return Ok(());
    }

    let TypeBindings {
      primary: primary_type,
      secondary: secondary_types,
      ..
    } = self.types.get(id).expect(&format!("type analysis failure: missing type for node {}", id));
    let primary_type = primary_type.clone();
    let secondary_types = secondary_types.clone();

    let var = self
      .variables
      .primary(id)
      .or_new(name, || {
        let domains = primary_type
          .domains()
          .iter()
          .map(|DomainType(name, id)| {
            Ok(
              self
                .domains
                .get_mut(name)
                .map(|base| base.instance(*id))
                .expect(&format!("type analysis failure: missing domain {}", name))?,
            )
          })
          .try_collect::<Vec<_>>()?;
        Ok(domains)
      })?
      .clone();

    let mut acc_var: Option<Variable> = None;
    for node in depends_on {
      node.accept(self)?;
      let result_var = self
        .variables
        .require(node.id, &primary_type)
        .expect(&format!("ir generation failure: missing variable for {}", node.id))
        .clone();
      let union_domains = var.domains.clone();
      let new_acc_var = self.variables.temp(name, union_domains);
      if let Some(acc_var) = acc_var {
        self.instructions.push(BIRInst::Union {
          to: new_acc_var.clone(),
          left: acc_var,
          right: result_var,
        });
      } else {
        self.instructions.push(BIRInst::Copy {
          to: new_acc_var.clone(),
          from: result_var,
        });
      }
      acc_var = Some(new_acc_var);
    }
    if let Some(acc_var) = acc_var {
      self.instructions.push(BIRInst::Copy {
        to: var.clone(),
        from: acc_var.clone(),
      });
    }
    for secondary_type in &secondary_types {
      let var2 = self
        .variables
        .add(
          id,
          name,
          secondary_type
            .domains()
            .iter()
            .map(|DomainType(name, id)| {
              Ok(
                self
                  .domains
                  .get_mut(name)
                  .map(|base| base.instance(*id))
                  .expect(&format!("type analysis failure: missing domain {}", name))?,
              )
            })
            .try_collect::<Vec<Arc<BDDDomain>>>()?,
        )
        .clone();
      self.instructions.push(BIRInst::Copy { to: var2.clone(), from: var.clone() });
    }
    Ok(())
  }

  fn visit_rule(&mut self, id: u16, head: &Atom, _body: &Vec<Atom>, depends_on: &Vec<Rc<Node>>) -> Result<(), OutOfMemory> {
    if !self.visited.insert(id) {
      return Ok(());
    }

    let TypeBindings {
      primary: primary_type,
      secondary: secondary_types,
      parts: part_types,
      bound: bound_types,
    } = self.types.get(id).expect(&format!("type analysis failure: missing type for node {}", id)).clone();
    let Atom::Pos(h_name, _h_terms) = head else {
      panic!("semantic analysis failure: rule head is not a positive atom");
    };

    let primary_type = primary_type.clone();
    let secondary_types = secondary_types.clone();
    let part_types = part_types.clone();
    let mut bound_types = bound_types.clone();

    let var = self
      .variables
      .primary(id)
      .or_new(h_name, || {
        let domains = primary_type
          .domains()
          .iter()
          .map(|DomainType(name, id)| {
            Ok(
              self
                .domains
                .get_mut(name)
                .map(|base| base.instance(*id))
                .expect(&format!("type analysis failure: missing domain {}", name))?,
            )
          })
          .try_collect::<Vec<_>>()?;
        Ok(domains)
      })?
      .clone();

    let mut last: Option<Variable> = None;
    for part_type in &part_types {
      let node = depends_on
        .iter()
        .find(|node| self.types.get(node.id).map(|node_type| node_type.satisfies(part_type)).unwrap_or(false))
        .expect(&format!("type analysis failure: missing node for type {:?}", part_type));
      node.accept(self)?;

      let join_var = self
        .variables
        .require(node.id, part_type)
        .expect(&format!("ir generation failure: missing variable for {}", node.id))
        .clone();
      let mut result_var = if let Some(last_var) = last {
        let temp_domains = union_of(&last_var.domains, &join_var.domains);
        let temp_name = join_var_name(&last_var.name, &join_var.name);
        let temp_var = self.variables.temp(&temp_name, temp_domains);
        self.instructions.push(BIRInst::Join {
          to: temp_var.clone(),
          left: last_var,
          right: join_var,
        });
        temp_var
      } else {
        join_var
      };
      let bindings = bound_types
        .extract_if(.., |(DomainType(name, id), _, _)| result_var.domains.iter().any(|d| &d.name == &*name && d.id == *id))
        .flat_map(|(domain, cmp, val)| val.as_value().map(|val| (domain, cmp, val)))
        .map(|(DomainType(name, id), cmp, val)| {
          let domain = self
            .domains
            .get_mut(&name)
            .map(|base| base.instance(id))
            .expect(&format!("type analysis failure: missing domain {}", name))?;
          Ok((domain, cmp, val))
        })
        .try_collect::<Vec<_>>()?;

      if !bindings.is_empty() {
        let selected_domains = result_var.domains.clone();

        let selected_name = select_var_name(&result_var.name);
        let selected_var = self.variables.temp(&selected_name, selected_domains);

        self.instructions.push(BIRInst::Select {
          to: selected_var.clone(),
          from: result_var.clone(),
          by: bindings,
        });

        result_var = selected_var;
      }

      last = Some(result_var);
    }

    if let Some(last) = last {
      self.instructions.push(BIRInst::Project { to: var.clone(), from: last.clone() });
      for secondary_type in &secondary_types {
        let var2 = self
          .variables
          .add(
            id,
            h_name,
            secondary_type
              .domains()
              .iter()
              .map(|DomainType(name, id)| {
                Ok(
                  self
                    .domains
                    .get_mut(name)
                    .map(|base| base.instance(*id))
                    .expect(&format!("type analysis failure: missing domain {}", name))?,
                )
              })
              .try_collect::<Vec<Arc<BDDDomain>>>()?,
          )
          .clone();
        self.instructions.push(BIRInst::Copy { to: var2.clone(), from: var.clone() });
      }
    }

    Ok(())
  }

  fn visit_component(&mut self, id: u16, name: &Arc<str>, _attributes: &Vec<Arc<Domain>>, depends_on: &Vec<Rc<Node>>) -> Result<(), OutOfMemory> {
    if !self.visited.insert(id) {
      return Ok(());
    }

    let TypeBindings {
      primary: primary_type,
      secondary: secondary_types,
      ..
    } = self.types.get(id).expect(&format!("type analysis failure: missing type for node {}", id));
    let primary_type = primary_type.clone();
    let secondary_types = secondary_types.clone();

    let var = self
      .variables
      .primary(id)
      .or_new(&name, || {
        let domains = primary_type
          .domains()
          .iter()
          .map(|DomainType(name, id)| {
            Ok(
              self
                .domains
                .get_mut(name)
                .map(|base| base.instance(*id))
                .expect(&format!("type analysis failure: missing domain {}", name))?,
            )
          })
          .try_collect::<Vec<_>>()?;
        Ok(domains)
      })?
      .clone();

    let mut vars2 = Vec::new();
    for secondary_type in &secondary_types {
      let var2 = self
        .variables
        .add(
          id,
          name,
          secondary_type
            .domains()
            .iter()
            .map(|DomainType(name, id)| {
              Ok(
                self
                  .domains
                  .get_mut(name)
                  .map(|base| base.instance(*id))
                  .expect(&format!("type analysis failure: missing domain {}", name))?,
              )
            })
            .try_collect::<Vec<Arc<BDDDomain>>>()?,
        )
        .clone();
      vars2.push(var2);
    }

    let (roots, inits, deps) = depends_on.iter().cloned().fold(
      (ExactlyOnce::<Rc<Node>>::None, ExactlyOnce::<Rc<Node>>::None, Vec::<Rc<Node>>::new()),
      |(root, init, mut deps), node| match node.kind {
        NodeKind::Relation { .. } => (root.accept(node), init, deps),
        NodeKind::Init { .. } => (root, init.accept(node), deps),
        _ => {
          deps.push(node);
          (root, init, deps)
        }
      },
    );
    let root = roots.expect("semantic analysis failure: component must have exactly one component root");
    let init = inits.expect("semantic analysis failure: component must have exactly one init node");

    init.accept(self)?;

    for dep in deps {
      dep.accept(self)?;
    }

    let component_instructions = Vec::new();
    let outer_instructions = replace(&mut self.instructions, component_instructions);

    root.accept(self)?;
    let result_var = self
      .variables
      .require(root.id, &primary_type)
      .expect(&format!("ir generation failure: missing variable for {}", root.id));
    let init_var = self
      .variables
      .require(init.id, &primary_type)
      .expect(&format!("ir generation failure: missing variable for {}", root.id));

    let inner_component_instructions = replace(&mut self.instructions, outer_instructions);

    let mut component_instructions = Vec::new();

    component_instructions.push(BIRInst::Phi {
      to: var.clone(),
      left: result_var.clone(),
      right: init_var.clone(),
    });
    for var2 in vars2 {
      component_instructions.push(BIRInst::Copy { to: var2.clone(), from: var.clone() });
    }
    component_instructions.extend(inner_component_instructions);

    self.instructions.push(BIRInst::Iter {
      current: var.clone(),
      next: result_var.clone(),
      body: component_instructions,
    });

    Ok(())
  }

  fn visit_prefetch(&mut self, id: u16, depends_on: &Vec<Rc<Node>>) -> Result<(), OutOfMemory> {
    if !self.visited.insert(id) {
      return Ok(());
    }

    for dep in depends_on {
      dep.accept(self)?;
    }
    Ok(())
  }

  fn visit_init(&mut self, id: u16, name: &Arc<str>, _attributes: &Vec<Arc<Domain>>, depends_on: &Vec<Rc<Node>>) -> Result<(), OutOfMemory> {
    if !self.visited.insert(id) {
      return Ok(());
    }
    let TypeBindings {
      primary: primary_type,
      secondary: secondary_types,
      ..
    } = self.types.get(id).expect(&format!("type analysis failure: missing type for node {}", id));
    let primary_type = primary_type.clone();
    let secondary_types = secondary_types.clone();

    let var = self
      .variables
      .primary(id)
      .or_new(name, || {
        let domains = primary_type
          .domains()
          .iter()
          .map(|DomainType(name, id)| {
            Ok(
              self
                .domains
                .get_mut(name)
                .map(|base| base.instance(*id))
                .expect(&format!("type analysis failure: missing domain {}", name))?,
            )
          })
          .try_collect::<Vec<_>>()?;
        Ok(domains)
      })?
      .clone();

    let mut acc_var: Option<Variable> = None;
    for node in depends_on {
      node.accept(self)?;
      let result_var = self
        .variables
        .require(node.id, &primary_type)
        .expect(&format!("ir generation failure: missing variable for {}", node.id))
        .clone();
      let union_domains = var.domains.clone();
      let new_acc_var = self.variables.temp(name, union_domains);
      if let Some(acc_var) = acc_var {
        self.instructions.push(BIRInst::Union {
          to: new_acc_var.clone(),
          left: acc_var,
          right: result_var,
        });
      } else {
        self.instructions.push(BIRInst::Copy {
          to: new_acc_var.clone(),
          from: result_var,
        });
      }
      acc_var = Some(new_acc_var);
    }
    if let Some(acc_var) = acc_var {
      self.instructions.push(BIRInst::Copy {
        to: var.clone(),
        from: acc_var.clone(),
      });
    }
    for secondary_type in &secondary_types {
      let var2 = self
        .variables
        .add(
          id,
          name,
          secondary_type
            .domains()
            .iter()
            .map(|DomainType(name, id)| {
              Ok(
                self
                  .domains
                  .get_mut(name)
                  .map(|base| base.instance(*id))
                  .expect(&format!("type analysis failure: missing domain {}", name))?,
              )
            })
            .try_collect::<Vec<Arc<BDDDomain>>>()?,
        )
        .clone();
      self.instructions.push(BIRInst::Copy { to: var2.clone(), from: var.clone() });
    }
    Ok(())
  }
}

fn join_var_name(left: &Arc<str>, right: &Arc<str>) -> Arc<str> {
  Arc::from(format!("{}⨝{}", extract_name(left), extract_name(right)))
}

fn select_var_name(base: &Arc<str>) -> Arc<str> {
  Arc::from(format!("σ{}", extract_name(base)))
}

fn extract_name(mut base: &str) -> &str {
  while let Some(next_base) = base.strip_suffix(&['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) {
    base = next_base;
  }
  while let Some(next_base) = base.strip_suffix(&['_']) {
    base = next_base;
  }
  base
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
pub trait BIRVisitor<E> {
  fn iter(&mut self, current: &Variable, next: &Variable, body: &Vec<BIRInst>) -> Result<(), E>;
  fn phi(&mut self, to: &Variable, left: &Variable, right: &Variable) -> Result<(), E>;
  fn load(&mut self, to: &Variable, from: &Location) -> Result<(), E>;
  fn store(&mut self, from: &Variable, to: &Location) -> Result<(), E>;
  fn copy(&mut self, to: &Variable, from: &Variable) -> Result<(), E>;
  fn project(&mut self, to: &Variable, from: &Variable) -> Result<(), E>;
  fn select(&mut self, to: &Variable, from: &Variable, by: &Vec<(Arc<BDDDomain>, Cmp, Value)>) -> Result<(), E>;
  fn join(&mut self, to: &Variable, left: &Variable, right: &Variable) -> Result<(), E>;
  fn union(&mut self, to: &Variable, left: &Variable, right: &Variable) -> Result<(), E>;
}
