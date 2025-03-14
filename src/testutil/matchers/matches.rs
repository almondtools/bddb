use super::super::core::*;
use std::fmt::Debug;

#[macro_export]
macro_rules! strictly {
  ($pred:expr) => {{
    let description = stringify!($pred);
    StrictDescription {
      predicate: &$pred,
      description: description.to_string(),
    }
  }};
}

#[macro_export]
macro_rules! description {
  ($pred:expr) => {{
    let description = stringify!($pred);
    CompoundDescription::new(&$pred, description)
  }};
}

pub trait Description<S> {
  fn describe(&self, subject: S) -> String;
  fn describe_mismatch(&self, subject: S) -> String;
}

pub struct StrictDescription<'a, S>
where
  S: Copy,
{
  predicate: &'a (dyn Fn(S) -> bool),
  description: String,
}

impl<'a, S> StrictDescription<'a, S>
where
  S: Copy,
{
  pub fn new(predicate: &'a (dyn Fn(S) -> bool), description: &str) -> Self {
    StrictDescription {
      predicate,
      description: description.to_string(),
    }
  }
}

impl<'a, S> Description<S> for StrictDescription<'a, S>
where
  S: Copy + Debug,
{
  fn describe(&self, subject: S) -> String {
    format!("<{:?}> should satisfy {}", subject, self.description)
  }

  fn describe_mismatch(&self, subject: S) -> String {
    format!("<{:?}> should not satisfy {}", subject, self.description)
  }
}

pub struct CompoundDescription<'a, S> {
  predicate: &'a (dyn Fn(&'a S) -> bool),
  description: String,
}

impl<'a, S> CompoundDescription<'a, S> {
  pub fn new(predicate: &'a (dyn Fn(&'a S) -> bool), description: &str) -> Self {
    CompoundDescription {
      predicate,
      description: description.to_string(),
    }
  }
}

impl<'a, S> Description<&S> for CompoundDescription<'a, S>
where
  S: Debug,
{
  fn describe(&self, subject: &S) -> String {
    format!("<{:?}> should satisfy {}", subject, self.description)
  }

  fn describe_mismatch(&self, subject: &S) -> String {
    format!("<{:?}> should not satisfy {}", subject, self.description)
  }
}

pub trait Matches<D> {
  #[allow(clippy::wrong_self_convention)]
  fn to_match(self, description: D) -> Self;
}

impl<'a, S> Matches<CompoundDescription<'a, S>> for Subject<'a, S>
where
  S: Debug,
{
  fn to_match(self, description: CompoundDescription<'a, S>) -> Self {
    let subject = self.subject();
    let matches = description.predicate;

    if !matches(subject) {
      Mismatch::from(self).expecting(description.describe(subject)).found("mismatch".to_string()).fail()
    }
    self
  }
}

impl<'a, S> Matches<StrictDescription<'a, S>> for Subject<'a, S>
where
  S: Copy + Debug,
{
  fn to_match(self, description: StrictDescription<'a, S>) -> Self {
    let subject = *self.subject();
    let matches = description.predicate;

    if !matches(subject) {
      Mismatch::from(self).expecting(description.describe(subject)).found("mismatch".to_string()).fail()
    }
    self
  }
}

impl<'a, S> Matches<CompoundDescription<'a, S>> for NegativeConstrainedSubject<'a, S>
where
  S: Debug,
{
  fn to_match(self, description: CompoundDescription<'a, S>) -> Self {
    let subject = self.subject();
    let matches = description.predicate;

    if matches(subject) {
      Mismatch::from(self).expecting(description.describe_mismatch(subject)).found("match".to_string()).fail()
    }
    self
  }
}

impl<'a, S> Matches<StrictDescription<'a, S>> for NegativeConstrainedSubject<'a, S>
where
  S: Copy + Debug,
{
  fn to_match(self, description: StrictDescription<'a, S>) -> Self {
    let subject = *self.subject();
    let matches = description.predicate;

    if matches(subject) {
      Mismatch::from(self).expecting(description.describe_mismatch(subject)).found("match".to_string()).fail()
    }
    self
  }
}

#[cfg(test)]
mod tests {

  use super::*;

  #[test]
  fn compiles_with_different_expectations() {
    since("values (copy) should compile").expect(&1).to_match(strictly!(|x| x == 1));
    since("references (dereferenced) should compile").expect(&1).to_match(description!(|x| *x == 1));
    since("references (matched) should compile").expect(&1).to_match(description!(|&x| x == 1));
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: <1> should satisfy |x| x == 2\n\
                             \t   found: mismatch\n\
                             at location.rs:42\n")]
  fn failure_message() {
    since("description should be displayed").expect(&1).at("location.rs:42").to_match(strictly!(|x| x == 2));
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: <1> should not satisfy |x| x == 1\n\
                             \t   found: match\n\
                             at location.rs:42\n")]
  fn inverted_failure_message() {
    since("description should be displayed").expect(&1).at("location.rs:42").not().to_match(strictly!(|x| x == 1));
  }
}
