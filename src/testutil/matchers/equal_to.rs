use super::super::core::*;
use std::fmt::Debug;

pub trait EqualTo<E> {
  #[allow(clippy::wrong_self_convention)]
  fn to_equal(self, expected: E) -> Self;
}

impl<'a, T, E> EqualTo<E> for Subject<'a, T>
where
  T: PartialEq<E> + Debug,
  E: Debug,
{
  fn to_equal(self, expected: E) -> Self {
    let subject = self.subject();
    if !subject.eq(&expected) {
      Mismatch::from(self).expecting(format!("<{:?}>", &expected)).found(format!("<{:?}>", subject)).fail()
    }
    self
  }
}

impl<'a, T, E> EqualTo<E> for NegativeConstrainedSubject<'a, T>
where
  T: PartialEq<E> + Debug,
  E: Debug,
{
  fn to_equal(self, expected: E) -> Self {
    let subject = self.subject();
    if subject.eq(&expected) {
      Mismatch::from(self).expecting(format!("<{:?}> not to equal <{:?}>", subject, &expected)).found("was equal").fail()
    }
    self
  }
}

#[cfg(test)]
mod tests {

  use super::*;

  #[test]
  fn compiles_with_different_expectations() {
    since("values should compile").expect(&1).to_equal(1);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: <2>\n\
                             \t   found: <1>\n\
                             at location.rs:42\n")]
  fn failure_message() {
    since("description should be displayed").expect(&1).at("location.rs:42").to_equal(2);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: <1> not to equal <1>\n\
                             \t   found: was equal\n\
                             at location.rs:42\n")]
  fn inverted_failure_message() {
    since("description should be displayed").expect(&1).at("location.rs:42").not().to_equal(1);
  }
}
