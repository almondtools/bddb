use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;
use std::rc::Rc;

use crate::util::compiler::Separated;

pub trait TermTuple {
  fn terms(&self) -> &Vec<Term>;
}

pub trait VariableContaining {
  fn variables(&self) -> Vec<Rc<str>>;

  fn substitute<T>(&mut self, variables: &HashMap<Rc<str>, T>)
  where
    T: Clone + Into<Rc<str>>;
}

pub trait Accept<T> {
  fn accept<V: Visitor<T>>(&self, visitor: &mut V) -> T;
}

pub trait Visitor<T> {
  fn visit_ord_val(&mut self, term: u128) -> T;
  fn visit_bool_val(&mut self, term: bool) -> T;
  fn visit_str_val(&mut self, term: Rc<str>) -> T;
  fn visit_variable(&mut self, term: Rc<str>) -> T;
  fn visit_any(&mut self) -> T;
  fn visit_term(&mut self, term: &Term) -> T {
    use Term::*;
    match term {
      OrdVal(i) => self.visit_ord_val(*i),
      BoolVal(b) => self.visit_bool_val(*b),
      StringVal(s) => self.visit_str_val(s.clone()),
      Variable(v) => self.visit_variable(v.clone()),
      Any => self.visit_any(),
    }
  }
  fn visit_negative_literal(&mut self, literal: &PrefixLiteral) -> T;
  fn visit_positive_literal(&mut self, literal: &PrefixLiteral) -> T;
  fn visit_infix_literal(&mut self, literal: &InfixLiteral) -> T;
  fn visit_literal(&mut self, literal: &Literal) -> T {
    use Literal::*;
    match literal {
      Positive(p) => self.visit_positive_literal(p),
      Negative(n) => self.visit_negative_literal(n),
      Comparative(c) => self.visit_infix_literal(c),
    }
  }
}

#[derive(PartialEq, Debug, Clone, Copy)]
pub enum Operator {
  Less,
  LessEqual,
  Greater,
  GreaterEqual,
  NotEqual,
  Equal,
}

impl Operator {
  pub fn swap(&self) -> Operator {
    use Operator::*;
    match self {
      Less => Greater,
      LessEqual => GreaterEqual,
      Greater => Less,
      GreaterEqual => LessEqual,
      NotEqual => NotEqual,
      Equal => Equal,
    }
  }
}

impl Display for Operator {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use Operator::*;
    let op_str = match self {
      Less => "<",
      LessEqual => "<=",
      Greater => ">",
      GreaterEqual => ">=",
      NotEqual => "!=",
      Equal => "=",
    };
    write!(f, "{}", op_str)
  }
}

#[derive(PartialEq, Debug, Clone)]
pub enum Term {
  OrdVal(u128),
  BoolVal(bool),
  StringVal(Rc<str>),
  Variable(Rc<str>),
  Any,
}

impl Term {
  pub fn is_ground(&self) -> bool {
    use Term::*;
    match self {
      OrdVal(_) | BoolVal(_) | StringVal(_) => true,
      Variable(_) | Any => false,
    }
  }

  pub fn is_variable(&self) -> bool {
    use Term::*;
    if let Variable(_) = self { true } else { false }
  }

  pub fn replace(&self, from: &Rc<str>, to: &Term) -> Option<Term> {
    use Term::*;
    match self {
      OrdVal(_) | BoolVal(_) | StringVal(_) => None,
      Any => None,
      Variable(n) => (from == n).then(|| to.clone()),
    }
  }
}

pub fn bool(val: bool) -> Term {
  Term::BoolVal(val)
}

pub fn ord(val: u128) -> Term {
  Term::OrdVal(val)
}

pub fn string(val: &str) -> Term {
  Term::StringVal(Rc::from(val))
}

pub fn variable(name: &str) -> Term {
  Term::Variable(Rc::from(name))
}

impl VariableContaining for Term {
  fn variables(&self) -> Vec<Rc<str>> {
    use Term::*;
    match self {
      OrdVal(_) | BoolVal(_) | StringVal(_) => Vec::new(),
      Variable(v) => vec![v.clone()],
      Any => Vec::new(),
    }
  }

  fn substitute<T>(&mut self, variables: &HashMap<Rc<str>, T>)
  where
    T: Clone + Into<Rc<str>>,
  {
    use Term::*;
    match self {
      Variable(v) => {
        if let Some(replacement) = variables.get(&*v) {
          *v = replacement.clone().into();
        }
      }
      _ => {}
    }
  }
}

impl Display for Term {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use Term::*;
    match self {
      OrdVal(v) => write!(f, "{}", v),
      BoolVal(b) => write!(f, "{}", b),
      StringVal(s) => write!(f, "\"{}\"", s),
      Variable(v) => write!(f, "{}", v),
      Any => write!(f, "*"),
    }
  }
}

impl<T> Accept<T> for Term {
  fn accept<V: Visitor<T>>(&self, visitor: &mut V) -> T {
    visitor.visit_term(self)
  }
}

#[derive(PartialEq, Debug, Clone)]
pub struct PrefixLiteral {
  pub name: Rc<str>,
  pub terms: Vec<Term>,
}

pub fn head(name: &str, terms: Vec<Term>) -> PrefixLiteral {
  let name = Rc::from(name);
  PrefixLiteral { name, terms }
}

impl PrefixLiteral {
  pub fn new<T: Into<Rc<str>>>(name: T, terms: Vec<Term>) -> Self {
    let name = name.into();
    PrefixLiteral { name, terms }
  }

  pub fn is_ground(&self) -> bool {
    self.terms.iter().all(|t| t.is_ground())
  }

  pub fn replace(&self, from: &Rc<str>, to: &Term) -> Option<PrefixLiteral> {
    let name = self.name.clone();
    let terms = self.terms.iter().map(|t| t.replace(from, to)).try_collect()?;
    Some(PrefixLiteral { name, terms })
  }
}

impl TermTuple for PrefixLiteral {
  fn terms(&self) -> &Vec<Term> {
    &self.terms
  }
}

impl VariableContaining for PrefixLiteral {
  fn variables(&self) -> Vec<Rc<str>> {
    self.terms.iter().flat_map(|t| t.variables()).collect()
  }

  fn substitute<T>(&mut self, variables: &HashMap<Rc<str>, T>)
  where
    T: Clone + Into<Rc<str>>,
  {
    for t in &mut self.terms {
      t.substitute(variables);
    }
  }
}

impl Display for PrefixLiteral {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}({})", self.name, self.terms.separated(", "))
  }
}

#[derive(PartialEq, Debug, Clone)]
pub struct InfixLiteral {
  pub left: Term,
  pub op: Operator,
  pub right: Term,
}

impl InfixLiteral {
  pub fn new(left: Term, op: Operator, right: Term) -> Self {
    InfixLiteral { left, op, right }
  }

  pub fn is_ground(&self) -> bool {
    self.left.is_ground() && self.right.is_ground()
  }

  fn is_trivial(&self) -> bool {
    if let Operator::Equal = self.op
      && self.left == self.right
    {
      true
    } else {
      false
    }
  }

  pub fn replace(&self, from: &Rc<str>, to: &Term) -> Option<InfixLiteral> {
    let op = self.op;
    let left = self.left.replace(from, to)?;
    let right = self.right.replace(from, to)?;
    Some(InfixLiteral { left, op, right })
  }
}

impl VariableContaining for InfixLiteral {
  fn variables(&self) -> Vec<Rc<str>> {
    self.left.variables().iter().chain(self.right.variables().iter()).cloned().collect()
  }

  fn substitute<T>(&mut self, variables: &HashMap<Rc<str>, T>)
  where
    T: Clone + Into<Rc<str>>,
  {
    self.left.substitute(variables);
    self.right.substitute(variables);
  }
}

impl Display for InfixLiteral {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{} {} {}", self.left, self.op, self.right)
  }
}

#[derive(PartialEq, Debug, Clone)]
pub enum Literal {
  Positive(PrefixLiteral),
  Negative(PrefixLiteral),
  Comparative(InfixLiteral),
}

pub fn pos_lit(name: &str, terms: Vec<Term>) -> Literal {
  let name = Rc::from(name);
  Literal::Positive(PrefixLiteral { name, terms })
}

pub fn neg_lit(name: &str, terms: Vec<Term>) -> Literal {
  let name = Rc::from(name);
  Literal::Negative(PrefixLiteral { name, terms })
}

impl Literal {
  pub fn is_ground(&self) -> bool {
    use Literal::*;
    match self {
      Positive(l) | Negative(l) => l.is_ground(),
      Comparative(l) => l.is_ground(),
    }
  }

  pub fn is_trivial(&self) -> bool {
    use Literal::*;
    match self {
      Comparative(l) => l.is_trivial(),
      _ => false,
    }
  }

  pub fn replace(&self, from: &Rc<str>, to: &Term) -> Option<Literal> {
    use Literal::*;
    match self {
      Positive(p) => Some(Positive(p.replace(from, to)?)),
      Negative(p) => Some(Negative(p.replace(from, to)?)),
      Comparative(i) => Some(Comparative(i.replace(from, to)?)),
    }
  }
}

impl VariableContaining for Literal {
  fn variables(&self) -> Vec<Rc<str>> {
    use Literal::*;
    match self {
      Positive(l) | Negative(l) => l.variables(),
      Comparative(l) => l.variables(),
    }
  }

  fn substitute<T>(&mut self, variables: &HashMap<Rc<str>, T>)
  where
    T: Clone + Into<Rc<str>>,
  {
    use Literal::*;
    match self {
      Positive(l) | Negative(l) => l.substitute(variables),
      Comparative(l) => l.substitute(variables),
    }
  }
}

impl Display for Literal {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use Literal::*;
    match self {
      Positive(l) => write!(f, "{}", l),
      Negative(l) => write!(f, "~{}", l),
      Comparative(l) => write!(f, "{}", l),
    }
  }
}

impl<T> Accept<T> for Literal {
  fn accept<V: Visitor<T>>(&self, visitor: &mut V) -> T {
    visitor.visit_literal(self)
  }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Rule {
  pub head: PrefixLiteral,
  pub body: Vec<Literal>,
}

impl Rule {
  pub fn new(head: PrefixLiteral, body: Vec<Literal>) -> Rule {
    Rule { head, body }
  }

  pub fn substitute<T>(&mut self, variables: HashMap<Rc<str>, T>)
  where
    T: Clone + Into<Rc<str>>,
  {
    self.head.substitute(&variables);
    for t in &mut self.body {
      t.substitute(&variables);
    }
  }
}

impl VariableContaining for Rule {
  fn variables(&self) -> Vec<Rc<str>> {
    self.head.variables().into_iter().chain(self.body.iter().flat_map(|t| t.variables())).fold(Vec::new(), |mut v, t| {
      if !v.contains(&t) {
        v.push(t);
      }
      v
    })
  }

  fn substitute<T>(&mut self, variables: &HashMap<Rc<str>, T>)
  where
    T: Clone + Into<Rc<str>>,
  {
    self.head.substitute(variables);
    for l in &mut self.body {
      l.substitute(variables);
    }
  }
}

impl Display for Rule {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{} <- {}", self.head, self.body.separated(" & "))
  }
}

#[derive(PartialEq, Debug, Clone)]
pub struct RelationSignature {
  pub name: Rc<str>,
  pub attributes: Vec<Rc<str>>,
}

pub fn relation_signature(name: &str, attributes: &[&str]) -> RelationSignature {
  let name: Rc<str> = Rc::from(name);
  let attributes = attributes.iter().map(|s| Rc::from(*s)).collect();
  RelationSignature { name, attributes }
}

impl RelationSignature {
  pub fn matches(&self, name: &str, arity: usize) -> bool {
    self.name.as_ref() == name && self.attributes.len() == arity
  }
}

#[derive(PartialEq, Debug, Clone)]
pub enum Relation {
  From(RelationSignature, Rc<str>),
  To(RelationSignature, Rc<str>),
  Mem(RelationSignature),
}

impl Relation {
  pub fn loaded_from(self, uri: impl Into<Rc<str>>) -> Relation {
    Relation::From(self.into(), uri.into())
  }

  pub fn stored_to(self, uri: impl Into<Rc<str>>) -> Relation {
    Relation::To(self.into(), uri.into())
  }

  pub fn signature(&self) -> &RelationSignature {
    match self {
      Relation::Mem(sig) => sig,
      Relation::From(sig, _) => sig,
      Relation::To(sig, _) => sig,
    }
  }

  pub fn store(&self) -> Option<Rc<str>> {
    match self {
      Relation::To(_, store) => Some(store.clone()),
      _ => None,
    }
  }

  pub fn is_stored(&self) -> bool {
    self.store().is_some()
  }

  pub fn source(&self) -> Option<Rc<str>> {
    match self {
      Relation::From(_, store) => Some(store.clone()),
      _ => None,
    }
  }

  pub fn is_loaded(&self) -> bool {
    self.source().is_some()
  }
}

impl Into<RelationSignature> for Relation {
  fn into(self) -> RelationSignature {
    match self {
      Relation::Mem(sig) => sig,
      Relation::From(sig, _) => sig,
      Relation::To(sig, _) => sig,
    }
  }
}

pub fn relation<T: Into<Rc<str>>>(name: T, attributes: Vec<T>) -> Relation {
  let name = name.into();
  let attributes = attributes.into_iter().map(|attribute| attribute.into()).collect();
  let signature = RelationSignature { name, attributes };
  Relation::Mem(signature)
}

#[derive(PartialEq, Debug, Clone)]
pub struct Domain {
  pub name: Rc<str>,
  pub size: u128,
  pub uri: Rc<str>,
}

pub fn domain(name: impl Into<Rc<str>>, size: u128) -> Domain {
  let name = name.into();
  let uri: Rc<str> = Rc::default();
  Domain { name, size, uri }
}

impl Domain {
  pub fn loaded_from(self, uri: impl Into<Rc<str>>) -> Domain {
    let name = self.name;
    let size = self.size;
    let uri = uri.into();
    Domain { name, size, uri }
  }
}

#[derive(PartialEq, Debug, Clone)]
pub struct Spec {
  pub domains: Vec<Domain>,
  pub relations: Vec<Relation>,
  pub rules: Vec<Rule>,
}

impl Spec {
  pub fn new(domains: Vec<Domain>, relations: Vec<Relation>, rules: Vec<Rule>) -> Spec {
    Spec { domains, relations, rules }
  }
}
