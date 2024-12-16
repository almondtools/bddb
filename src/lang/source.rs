use std::fmt;
use std::fmt::Display;

#[derive(PartialEq, Debug, Clone)]
pub struct LineInfo {
  line: usize,
  from: usize,
  to: usize,
}

impl LineInfo {
  pub fn new(line: usize, from: usize, to: usize) -> Self {
    LineInfo { line, from, to }
  }
}

impl Display for LineInfo {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if self.from == self.to {
      write!(f, "Line {} Position {}", self.line, self.from)
    } else {
      write!(f, "Line {} Position {}-{}", self.line, self.from, self.to)
    }
  }
}

#[derive(PartialEq, Debug, Clone)]
pub struct AnalysisError<L: Display> {
  pub msg: String,
  pub detail: Option<String>,
  pub location: L,
}

impl<L: Display> AnalysisError<L> {
  pub fn new(msg: String, detail: Option<String>, location: L) -> Self {
    AnalysisError { msg, detail, location }
  }
}

impl<L: Display> fmt::Display for AnalysisError<L> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{} at {}", self.msg, self.location)?;
    if let Some(ref detail) = self.detail {
      write!(f, ":\n{}", detail)?;
    }
    Ok(())
  }
}

pub trait ErrorMapper<T> {
  fn map_error(&self, error: T) -> AnalysisError<LineInfo>;
}

pub trait LocationMapper<T> {
  fn map_location(&self, location: T) -> LineInfo;
}

#[derive(PartialEq, Debug, Clone)]
pub struct SourceInfo<'input> {
  pub text: &'input str,
  pub tab: usize,
}

impl<'input> SourceInfo<'input> {
  pub fn new(text: &'input str) -> Self {
    SourceInfo { text, tab: 4 }
  }

  pub fn tab(mut self, tab: usize) -> Self {
    self.tab = tab;
    self
  }

  pub fn expect_tokens(&self, expected: &[String]) -> String {
    let mut buffer = String::new();
    for (i, token) in expected.iter().enumerate() {
      if i == 0 {
        buffer.push_str("Expected one of ");
      } else if i == expected.len() - 1 {
        buffer.push_str(" or ");
      } else if i > 0 {
        buffer.push_str(", ");
      }
      buffer.push_str(token);
    }
    buffer
  }
}
