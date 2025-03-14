use std::collections::HashSet;
use std::slice::Iter;

pub trait Iterable {
  type Item;
  fn elements(&self) -> Vec<Self::Item>;
  fn count(&self) -> usize;
}

impl<T> Iterable for Option<T>
where
  T: Clone,
{
  type Item = T;

  fn elements(&self) -> Vec<T> {
    self.iter().cloned().collect()
  }

  fn count(&self) -> usize {
    if self.is_some() { 1 } else { 0 }
  }
}

impl<T> Iterable for Vec<T>
where
  T: Clone,
{
  type Item = T;

  fn elements(&self) -> Vec<T> {
    self.to_vec()
  }

  fn count(&self) -> usize {
    self.len()
  }
}

impl<T> Iterable for HashSet<T>
where
  T: Clone,
{
  type Item = T;

  fn elements(&self) -> Vec<T> {
    let mut cloned = Vec::new();
    for element in self {
      let e = element.clone();
      cloned.push(e);
    }
    cloned
  }

  fn count(&self) -> usize {
    self.len()
  }
}

impl<'a, T> Iterable for Iter<'a, T>
where
  T: Clone,
{
  type Item = T;

  fn elements(&self) -> Vec<T> {
    let elements = self.to_owned();
    let mut cloned = Vec::new();
    for element in elements {
      let e = element.clone();
      cloned.push(e);
    }

    cloned
  }

  fn count(&self) -> usize {
    self.len()
  }
}
