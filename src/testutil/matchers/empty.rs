use super::super::core::*;
use super::super::types::*;

pub trait Empty {
  #[allow(clippy::wrong_self_convention)]
  fn to_be_empty(self) -> Self;
}

impl<'a, I> Empty for Subject<'a, I>
where
  I: Iterable,
{
  fn to_be_empty(self) -> Self {
    let size = self.subject().count();

    if size > 0 {
      Mismatch::from(self).expecting("empty collection").found(format!("has size <{}>", size)).fail()
    }
    self
  }
}

impl<'a, I> Empty for NegativeConstrainedSubject<'a, I>
where
  I: Iterable,
{
  fn to_be_empty(self) -> Self {
    let size = self.subject().count();

    if size == 0 {
      Mismatch::from(self).expecting("not empty collection").found("was empty").fail()
    }
    self
  }
}

#[cfg(test)]
mod tests {

  use super::*;
  use std::collections::HashSet;

  #[test]
  fn compiles_with_different_expectations() {
    since("vec should compile").expect(&Vec::<i8>::new()).to_be_empty();
    since("hashset should compile").expect(&HashSet::<i8>::new()).to_be_empty();
    since("iter should compile").expect(&Vec::<i8>::new().iter()).to_be_empty();
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: empty collection\n\
                             \t   found: has size <1>\n\
                             at location.rs:42\n")]
  fn failure_message() {
    since("description should be displayed").expect(&vec![1]).at("location.rs:42").to_be_empty();
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: not empty collection\n\
                             \t   found: was empty\n\
                             at location.rs:42\n")]
  fn inverted_failure_message() {
    since("description should be displayed").expect(&Vec::<i8>::new()).at("location.rs:42").not().to_be_empty();
  }
}
