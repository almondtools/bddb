use super::super::core::*;
use super::super::types::*;
use std::fmt::Debug;

pub enum Quantity<T> {
  None,
  One(T),
  Few(T),
}

impl<T> Quantity<T> {
  pub fn append(self, element: T) -> Self {
    match self {
      Quantity::None => Quantity::One(element),
      Quantity::One(_) | Quantity::Few(_) => Quantity::Few(element),
    }
  }
  pub fn map<R, O, F>(&self, none: R, one: O, few: F) -> R
  where
    O: FnOnce(&T) -> R,
    F: FnOnce(&T) -> R,
  {
    match self {
      Quantity::None => none,
      Quantity::One(last) => one(last),
      Quantity::Few(last) => few(last),
    }
  }
}

pub trait ContainsInOrder<T: Debug>: Sized {
  #[allow(clippy::wrong_self_convention)]
  fn to_contain_in_order(self, sequence: Vec<T>) -> Self;
}

fn fail_matching<C, T: Debug>(subject: NegativeConstrainedSubject<C>, last: Quantity<&T>) -> ! {
  let content = last.map("".to_string(), |element| format!("<{:?}>", element), |element| format!("..., <{:?}>", element));
  Mismatch::from(subject)
    .expecting(format!("collection not containing [{}]", content))
    .found(format!("[{}]", content))
    .fail();
}

fn fail_missing<C, T: Debug>(subject: Subject<C>, last: Quantity<&T>, missing: &T) -> ! {
  let expected_prefix = last.map("".to_string(), |element| format!("<{:?}>, ", element), |element| format!("..., <{:?}>, ", element));
  let found_prefix = last.map("".to_string(), |element| format!("<{:?}>", element), |element| format!("..., <{:?}>", element));
  Mismatch::from(subject)
    .expecting(format!("collection containing [{}<{:?}>]", expected_prefix, missing))
    .found(format!("collection containing [{}]", found_prefix))
    .fail();
}

fn fail_surplus<C, T: Debug>(subject: Subject<C>, last: Quantity<&T>, surplus: &T) -> ! {
  let expected_prefix = last.map("".to_string(), |element| format!("<{:?}>", element), |element| format!("..., <{:?}>", element));
  let found_prefix = last.map("".to_string(), |element| format!("<{:?}>, ", element), |element| format!("..., <{:?}>, ", element));
  Mismatch::from(subject)
    .expecting(format!("collection containing [{}]", expected_prefix))
    .found(format!("collection containing [{}<{:?}>]", found_prefix, surplus))
    .fail();
}

fn fail_mismatch<C, T: Debug>(subject: Subject<C>, last: Quantity<&T>, actual: &T, expected: &T) -> ! {
  let prefix = last.map("", |_| "..., ", |_| "..., ").to_string();
  Mismatch::from(subject)
    .expecting(format!("collection containing [{}<{:?}>, ...]", prefix, expected))
    .found(format!("collection containing [{}<{:?}>, ...]", prefix, actual))
    .fail();
}

impl<'a, I, T> ContainsInOrder<T> for Subject<'a, I>
where
  I: Iterable<Item = T>,
  T: Debug + PartialEq<T> + 'a,
{
  fn to_contain_in_order(self, sequence: Vec<T>) -> Self {
    let elements = self.subject().elements();
    let mut iterator = elements.iter();
    let mut expected_iterator = sequence.iter();

    let mut last = Quantity::None;
    loop {
      let current = iterator.next();
      let expected_current = expected_iterator.next();

      if current.is_none() && expected_current.is_none() {
        return self;
      } else if current.is_none() {
        fail_missing(self, last, expected_current.unwrap())
      } else if expected_current.is_none() {
        fail_surplus(self, last, &current.unwrap())
      }
      let current_value = current.unwrap();
      let expected_value = expected_current.unwrap();
      if *current_value != *expected_value {
        fail_mismatch(self, last, current_value, expected_value)
      }
      last = last.append(expected_value);
    }
  }
}

impl<'a, I, T> ContainsInOrder<T> for NegativeConstrainedSubject<'a, I>
where
  I: Iterable<Item = T>,
  T: Debug + PartialEq<T> + 'a,
{
  fn to_contain_in_order(self, sequence: Vec<T>) -> Self {
    let elements = self.subject().elements();
    let mut iterator = elements.iter();
    let mut expected_iterator = sequence.iter();

    let mut last = Quantity::None;
    loop {
      let current = iterator.next();
      let expected_current = expected_iterator.next();

      if current.is_none() && expected_current.is_none() {
        fail_matching(self, last)
      } else if current.is_none() || expected_current.is_none() {
        return self;
      }
      let current_value = current.unwrap();
      let expected_value = expected_current.unwrap();
      if *current_value != *expected_value {
        return self;
      }
      last = last.append(expected_value);
    }
  }
}

#[cfg(test)]
mod tests {

  use super::*;

  use std::collections::HashSet;
  use std::iter::FromIterator;

  #[test]
  fn compiles_with_different_expectations() {
    since("vec should compile").expect(&vec![1i8]).to_contain_in_order(vec![1i8]);
    since("hashset should compile").expect(&HashSet::from_iter(vec![1i8]) as &HashSet<i8>).to_contain_in_order(vec![1i8]);
    since("iter should compile").expect(&vec![1i8].iter()).to_contain_in_order(vec![1i8]);

    since("vec should compile").expect(&vec![1i8]).not().to_contain_in_order(vec![1i8, 2i8]);
    since("hashset should compile")
      .expect(&HashSet::from_iter(vec![1i8, 2i8]) as &HashSet<i8>)
      .not()
      .to_contain_in_order(vec![1i8]);
    since("iter should compile").expect(&vec![1i8].iter()).not().to_contain_in_order(vec![2i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection containing [<2>, ...]\n\
                             \t   found: collection containing [<1>, ...]\n\
                             at location.rs:42\n")]
  fn failure_message_for_mismatch() {
    since("description should be displayed").expect(&vec![1i8]).at("location.rs:42").to_contain_in_order(vec![2i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection containing [..., <2>, ...]\n\
                             \t   found: collection containing [..., <1>, ...]\n\
                             at location.rs:42\n")]
  fn failure_message_for_mismatch_at_later_element() {
    since("description should be displayed")
      .expect(&vec![1i8, 1i8])
      .at("location.rs:42")
      .to_contain_in_order(vec![1i8, 2i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection containing [<2>]\n\
                             \t   found: collection containing [<2>, <3>]\n\
                             at location.rs:42\n")]
  fn failure_message_for_surplus() {
    since("description should be displayed").expect(&vec![2i8, 3i8]).at("location.rs:42").to_contain_in_order(vec![2i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection containing [..., <2>]\n\
                             \t   found: collection containing [..., <2>, <3>]\n\
                             at location.rs:42\n")]
  fn failure_message_for_surplus_at_later_element() {
    since("description should be displayed")
      .expect(&vec![0i8, 2i8, 3i8])
      .at("location.rs:42")
      .to_contain_in_order(vec![0i8, 2i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection containing [<2>, <3>]\n\
                             \t   found: collection containing [<2>]\n\
                             at location.rs:42\n")]
  fn failure_message_for_missing() {
    since("description should be displayed").expect(&vec![2i8]).at("location.rs:42").to_contain_in_order(vec![2i8, 3i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection containing [..., <2>, <3>]\n\
                             \t   found: collection containing [..., <2>]\n\
                             at location.rs:42\n")]
  fn failure_message_for_missing_at_later_element() {
    since("description should be displayed")
      .expect(&vec![0i8, 2i8])
      .at("location.rs:42")
      .to_contain_in_order(vec![0i8, 2i8, 3i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection not containing [<2>]\n\
                             \t   found: [<2>]\n\
                             at location.rs:42\n")]
  fn inverted_failure_message() {
    since("description should be displayed").expect(&vec![2i8]).at("location.rs:42").not().to_contain_in_order(vec![2i8]);
  }

  #[test]
  #[should_panic(expected = "\n\
                             description should be displayed:\n\
                             \texpected: collection not containing [..., <3>]\n\
                             \t   found: [..., <3>]\n\
                             at location.rs:42\n")]
  fn inverted_failure_message_at_later_element() {
    since("description should be displayed")
      .expect(&vec![2i8, 3i8])
      .at("location.rs:42")
      .not()
      .to_contain_in_order(vec![2i8, 3i8]);
  }
}
