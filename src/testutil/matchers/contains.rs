use super::super::core::*;
use super::super::types::*;
use super::Matcher;
use crate::since;
use std::fmt::Debug;

pub trait Contains<T: Debug>: Sized {
  #[allow(clippy::wrong_self_convention)]
  fn to_contain(self, set: Vec<T>) -> Self;
}

fn highlight<T: Debug>(expected: &[T]) -> String {
  let mut highlighted = String::new();
  let mut it = expected.iter();
  if let Some(element) = it.next() {
    highlighted.push_str(&format!("<{:?}>", element));
    for element in it {
      highlighted.push_str(", ");
      highlighted.push_str(&format!("<{:?}>", element));
    }
  }
  highlighted
}

fn abbreviate_highlight<T: Debug>(expected: &[T]) -> String {
  let mut highlighted = String::new();
  let mut it = expected.iter().take(5);
  if let Some(element) = it.next() {
    highlighted.push_str(&format!("<{:?}>", element));
    for element in it {
      highlighted.push_str(", ");
      highlighted.push_str(&format!("<{:?}>", element));
    }
  }
  if expected.len() > 5 {
    highlighted.push_str(format!(", ... ({} items)", expected.len() - 5).as_str());
  }
  highlighted
}

fn fail_matching<C, T: Debug>(subject: NegativeConstrainedSubject<C>, expected: &[T]) -> ! {
  let expected_str = highlight(expected);
  Mismatch::from(subject)
    .expecting(format!("collection not containing [{}]", expected_str))
    .found(format!("[{}]", expected_str))
    .fail();
}

fn fail_missing<C, M: Debug, T: Debug>(subject: Subject<C>, expected: &[M], missing: Vec<&M>, found: &[T]) -> ! {
  Mismatch::from(subject)
    .expecting(format!("collection containing [{}]", highlight(expected)))
    .found(format!("collection [{}] did not contain [{}]", abbreviate_highlight(found), highlight(&missing)))
    .fail();
}

fn fail_surplus<C, T: Debug, M: Debug>(subject: Subject<C>, expected: &[M], surplus: Vec<&T>, found: &[T]) -> ! {
  Mismatch::from(subject)
    .expecting(format!("collection containing [{}]", highlight(expected)))
    .found(format!("collection [{}] contained also [{}]", abbreviate_highlight(found), highlight(&surplus)))
    .fail();
}

impl<'a, I, T, M> Contains<M> for Subject<'a, I>
where
  I: Iterable<Item = T>,
  T: Debug + 'a,
  M: Matcher<T> + Debug,
{
  fn to_contain(self, set: Vec<M>) -> Self {
    let elements = self.subject().elements();

    let mut missing = set.iter().collect::<Vec<&M>>();
    missing.retain(|matcher| !elements.iter().any(|element| matcher.matches(element)));
    if !missing.is_empty() {
      fail_missing(self, &set, missing, &elements);
    }

    let mut surplus = elements.iter().collect::<Vec<&T>>();
    surplus.retain(|element| !set.iter().any(|matcher| matcher.matches(element)));
    if !surplus.is_empty() {
      fail_surplus(self, &set, surplus, &elements);
    }
    self
  }
}

impl<'a, I, T> Contains<T> for NegativeConstrainedSubject<'a, I>
where
  I: Iterable<Item = T>,
  T: Debug + PartialEq<T> + 'a,
{
  fn to_contain(self, set: Vec<T>) -> Self {
    let elements = self.subject().elements();

    let mut missing = set.iter().collect::<Vec<&T>>();
    missing.retain(|element| !elements.contains(element));
    if !missing.is_empty() {
      return self;
    }

    let mut surplus = elements.iter().collect::<Vec<&T>>();
    surplus.retain(|element| !set.contains(element));
    if !surplus.is_empty() {
      return self;
    }
    fail_matching(self, &set);
  }
}

#[cfg(test)]
mod tests {

  use super::*;

  use std::collections::HashSet;
  use std::iter::FromIterator;

  #[test]
  fn compiles_with_different_expectations() {
    since("vec should compile").expect(&vec![1i8]).to_contain(vec![1i8]);
    since("hashset should compile").expect(&HashSet::from_iter(vec![1i8]) as &HashSet<i8>).to_contain(vec![1i8]);
    since("iter should compile").expect(&vec![1i8].iter()).to_contain(vec![1i8]);

    since("vec should compile").expect(&vec![1i8]).not().to_contain(vec![1i8, 2i8]);
    since("hashset should compile").expect(&HashSet::from_iter(vec![1i8, 2i8]) as &HashSet<i8>).not().to_contain(vec![1i8]);
    since("iter should compile").expect(&vec![1i8].iter()).not().to_contain(vec![2i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection containing [<2>]\n\
                             \t   found: collection [<1>] did not contain [<2>]\n\
                             at location.rs:42\n")]
  fn failure_message_for_mismatch() {
    since("description should be displayed").expect(&vec![1i8]).at("location.rs:42").to_contain(vec![2i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection containing [<2>]\n\
                             \t   found: collection [<2>, <3>] contained also [<3>]\n\
                             at location.rs:42\n")]
  fn failure_message_for_surplus() {
    since("description should be displayed").expect(&vec![2i8, 3i8]).at("location.rs:42").to_contain(vec![2i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection containing [<2>]\n\
                             \t   found: collection [<2>, <3>, <4>] contained also [<3>, <4>]\n\
                             at location.rs:42\n")]
  fn failure_message_for_multiple_surplus() {
    since("description should be displayed").expect(&vec![2i8, 3i8, 4i8]).at("location.rs:42").to_contain(vec![2i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection containing [<2>, <3>]\n\
                             \t   found: collection [<2>] did not contain [<3>]\n\
                             at location.rs:42\n")]
  fn failure_message_for_missing() {
    since("description should be displayed").expect(&vec![2i8]).at("location.rs:42").to_contain(vec![2i8, 3i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection containing [<2>, <3>, <4>]\n\
                             \t   found: collection [<2>] did not contain [<3>, <4>]\n\
                             at location.rs:42\n")]
  fn failure_message_for_multiple_missing() {
    since!("description should be displayed").expect(&vec![2i8]).at("location.rs:42").to_contain(vec![2i8, 3i8, 4i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection not containing [<2>]\n\
                             \t   found: [<2>]\n\
                             at location.rs:42\n")]
  fn inverted_failure_message() {
    since!("description should be displayed").expect(&vec![2i8]).at("location.rs:42").not().to_contain(vec![2i8]);
  }
}
