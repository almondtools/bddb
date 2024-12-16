use crate::lang::ast::{InfixLiteral, Operator, Rule, Term, VariableContaining};
use crate::lang::source::{AnalysisError, ErrorMapper, LineInfo, LocationMapper, SourceInfo};
use crate::util::compiler::Separated;
use lalrpop_util::ParseError;
use lalrpop_util::lexer::Token;
use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::fmt::Display;
use std::rc::Rc;
use std::str::FromStr;

use super::ast::{Literal, PrefixLiteral, TermTuple};

#[derive(PartialEq, Debug, Clone)]
pub enum SemanticError {
  UnknownDomain(String),
  UnknownRelation(String)
}

#[derive(PartialEq, Debug, Clone)]
pub struct BytePos {
  from: usize,
  to: usize,
}

impl BytePos {
  pub fn new(from: usize, to: usize) -> Self {
    BytePos { from, to }
  }
}

impl Display for BytePos {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}:{}", self.from, self.to)
  }
}

impl<'input> LocationMapper<BytePos> for SourceInfo<'input> {
  fn map_location(&self, location: BytePos) -> LineInfo {
    let BytePos { from, to } = location;
    let span = to - from;
    let bytes = self.text.as_bytes();
    let (line, from, to) = (0..to).rev().map(|i| bytes[i]).enumerate().fold((None, 1, 1), |(line, from, to), (i, b)| {
      if b == b'\n' {
        (line.map(|l| l + 1).or(Some(2)), from, to)
      } else if line.is_some() {
        (line, from, to)
      } else if i < span {
        match b {
          b'\t' => (line, from, to + self.tab),
          control if control < 32 => (line, from, to),
          _ => (line, from, to + 1),
        }
      } else {
        match b {
          b'\t' => (line, from + self.tab, to + self.tab),
          control if control < 32 => (line, from, to),
          _ => (line, from + 1, to + 1),
        }
      }
    });
    LineInfo::new(line.unwrap_or(1), from, to)
  }
}

pub fn parse_error<'input, L: Display>(msg: String, detail: Option<String>, location: L) -> ParseError<usize, Token<'input>, AnalysisError<L>> {
  ParseError::User {
    error: AnalysisError::new(msg, detail, location),
  }
}

impl<'input> ErrorMapper<ParseError<usize, Token<'input>, AnalysisError<BytePos>>> for SourceInfo<'input> {
  fn map_error(&self, error: ParseError<usize, Token<'input>, AnalysisError<BytePos>>) -> AnalysisError<LineInfo> {
    match error {
      ParseError::User {
        error: AnalysisError { msg, detail, location },
      } => AnalysisError::new(msg, detail, self.map_location(location)),
      ParseError::UnrecognizedToken { token: (from, token, to), expected } => AnalysisError::new(
        format!("Unrecognized token `{}` found", token),
        Some(self.expect_tokens(&expected)),
        self.map_location(BytePos::new(from, to)),
      ),
      ParseError::InvalidToken { location } => AnalysisError::new("Invalid token".to_string(), None, self.map_location(BytePos::new(location, location))),
      ParseError::UnrecognizedEof { location, expected } => AnalysisError::new(
        "Unexpected end of file".to_string(),
        Some(self.expect_tokens(&expected)),
        self.map_location(BytePos::new(location, location)),
      ),
      ParseError::ExtraToken { token: (from, token, to) } => AnalysisError::new(format!("Extra token `{}` found", token), None, self.map_location(BytePos::new(from, to))),
    }
  }
}

pub fn create_rule<'a>(head: PrefixLiteral, body: Vec<Literal>, from: usize, to: usize) -> Result<Rule, ParseError<usize, Token<'a>, AnalysisError<BytePos>>> {
  let (unbound_head, unbound_neg, unbound_comp) = compute_unbound(&head, &body);
  if !unbound_head.is_empty() {
    return Err(parse_error(
      format!("invalid query head `{} <- {}`", &head, body.separated(" & ")),
      Some(format!("all terms in a rule head must be bound in body")),
      BytePos::new(from, to),
    ));
  }
  if !unbound_neg.is_empty() {
    return Err(parse_error(
      format!("invalid rule body `{}`", body.separated(" & ")),
      Some(format!("all terms in negative literals must be bound (positive) in body")),
      BytePos::new(from, to),
    ));
  }
  if !unbound_comp.is_empty() {
    return Err(parse_error(
      format!("invalid rule body `{}`", body.separated(" & ")),
      Some(format!("all terms in comparative literals must be bound (positive) in body")),
      BytePos::new(from, to),
    ));
  }

  let unifications = compute_unification_links(&body);
  if unifications.into_iter().any(|(var, exprs)| exprs.into_iter().flat_map(|t| t.variables()).any(|v| v == var)) {
    return Err(parse_error(
      format!("invalid rule body `{}`", body.separated(" & ")),
      Some(format!("all terms in unifying literals are not allowed to be bound recursively")),
      BytePos::new(from, to),
    ));
  }

  Ok(Rule::new(head, body))
}

fn compute_unbound<T: TermTuple>(head: &T, body: &[Literal]) -> (Vec<Rc<str>>, Vec<Rc<str>>, Vec<Rc<str>>) {
  use Literal::*;

  let mut unbound_head = Vec::new();
  for t in head.terms() {
    for v in t.variables() {
      if !unbound_head.contains(&v) {
        unbound_head.push(v);
      }
    }
  }

  let mut bound_body = Vec::new();
  let mut unbound_neg = Vec::new();
  let mut unbound_comp = Vec::new();
  for literal in body {
    match literal {
      Positive(l) => {
        bound_body.extend(l.variables());
      }
      Negative(l) => {
        unbound_neg.extend(l.variables());
      }
      Comparative(l) => {
        if l.op == Operator::Equal {
          bound_body.extend(l.variables());
        } else {
          unbound_comp.extend(l.variables());
        }
      }
    }
  }

  unbound_head.retain(|v| !bound_body.contains(v));
  unbound_neg.retain(|v| !bound_body.contains(v));
  unbound_comp.retain(|v| !bound_body.contains(v));

  (unbound_head, unbound_neg, unbound_comp)
}

fn compute_unification_links(body: &[Literal]) -> HashMap<Rc<str>, Vec<Term>> {
  use Literal::*;
  let mut linked = HashMap::new();
  for literal in body {
    if let Comparative(InfixLiteral { left, op: Operator::Equal, right }) = literal {
      if let Term::Variable(var) = &left {
        let related = linked.entry(var.clone()).or_insert_with(Vec::new);
        related.push(right.clone());
      }
      if let Term::Variable(var) = &right {
        let related = linked.entry(var.clone()).or_insert_with(Vec::new);
        related.push(left.clone());
      }
    }
  }
  let mut todo = VecDeque::new();
  todo.extend(linked.keys().cloned());
  while let Some(var) = todo.pop_front() {
    let mut new_terms = Vec::new();
    if let Some(related) = linked.get(&var) {
      for term in related {
        for variable in term.variables() {
          for replacement in linked.get(&variable).into_iter().flatten().cloned() {
            if let Some(new_term) = term.replace(&variable, &replacement)
              && !related.contains(&new_term)
              && !new_term.is_variable()
            {
              new_terms.push(new_term)
            }
          }
        }
      }
    }
    if new_terms.is_empty() {
      continue;
    }
    let new_variables = new_terms.iter().flat_map(|t| t.variables()).collect::<Vec<_>>();
    for term in new_terms {
      linked.get_mut(&var).unwrap().push(term);
    }
    if !new_variables.contains(&var) {
      todo.push_back(var);
    }
  }

  linked
}

pub fn recognize_bool(token: &str) -> bool {
  bool::from_str(token).unwrap_or_else(|_| panic!("did not expect any other than `true` or `false`, but was `{}`", token))
}

pub fn recognize_ord(token: &str, pos: usize) -> Result<u128, ParseError<usize, Token<'_>, AnalysisError<BytePos>>> {
  u128::from_str(token).map_err(|_| {
    parse_error(
      format!("invalid integer `{}`", token),
      Some(format!("Legal range is [{},{}]", u128::min_value(), u128::max_value())),
      BytePos::new(pos, pos + token.len()),
    )
  })
}

pub fn recognize_string(token: &str) -> Rc<str> {
  let (unescaped, _) = token[1..token.len() - 1].chars().fold((String::new(), Vec::new()), |(mut str, mut buf), c| {
    if buf.is_empty() {
      if c == '\\' {
        buf.push(c);
      } else {
        str.push(c);
      }
    } else {
      match buf.as_slice() {
        ['\\'] => match c {
          't' => {
            buf.clear();
            str.push('\t');
          }
          'n' => {
            buf.clear();
            str.push('\n');
          }
          '"' => {
            buf.clear();
            str.push('"');
          }
          'u' => {
            buf.push('u');
          }
          '\\' => {
            buf.clear();
            str.push('\\');
          }
          _ => {
            for &c in &buf {
              str.push(c);
            }
            str.push(c);
          }
        },
        unicode @ ['\\', 'u', ..] if unicode.len() < 7 => {
          buf.push(c);
        }
        ['\\', 'u', '{', number @ ..] if c == '}' => {
          if let Some(c) = number
            .iter()
            .fold(Some(0), |acc, c| acc.and_then(|base| c.to_digit(16).map(|d| base * 16 + d)))
            .and_then(char::from_u32)
          {
            buf.clear();
            str.push(c);
          }
        }
        _ => {
          for &c in &buf {
            str.push(c);
          }
          buf.clear();
          str.push(c);
        }
      }
    }
    (str, buf)
  });
  Rc::from(unescaped.as_ref())
}

pub fn recognize_identifier(token: &str) -> Rc<str> {
  Rc::from(token)
}

#[cfg(test)]
#[allow(warnings)]
mod test {

  use super::*;
  use crate::lang::ast::Literal::*;
  use crate::lang::ast::Term::*;
  use crate::lang::ast::*;

  pub fn new_rule(name: &str, terms: Vec<Term>, body: Vec<Literal>) -> Rule {
    let head = PrefixLiteral::new(name, terms);
    create_rule(head, body, 0, 0).unwrap()
  }

  pub fn pos(name: &str, terms: Vec<Term>) -> Literal {
    Positive(PrefixLiteral::new(name, terms))
  }

  pub fn neg(name: &str, terms: Vec<Term>) -> Literal {
    Negative(PrefixLiteral::new(name, terms))
  }

  pub fn cmp(l_term: Term, op: Operator, r_term: Term) -> Literal {
    Comparative(InfixLiteral::new(l_term, op, r_term))
  }

  pub fn t() -> Term {
    BoolVal(true)
  }

  pub fn f() -> Term {
    BoolVal(false)
  }

  pub fn ord(val: u128) -> Term {
    OrdVal(val)
  }

  pub fn string<T: Into<Rc<str>>>(val: T) -> Term {
    let val = val.into();
    StringVal(val)
  }

  pub fn var<T: Into<Rc<str>>>(name: T) -> Term {
    let name = name.into();
    Variable(name)
  }
}
