use std::collections::VecDeque;
use std::fmt::Display;
use std::iter::FromIterator;
use std::ops::Deref;
use std::vec::IntoIter;

#[derive(Debug, Clone)]
pub struct VecSet<T: PartialEq> {
  items: Vec<T>,
}

impl<T: PartialEq> VecSet<T> {
  pub fn empty() -> Self {
    let items = Vec::new();
    VecSet { items }
  }

  pub fn one(item: T) -> Self {
    let items = vec![item];
    VecSet { items }
  }

  pub fn insert(&mut self, item: T) {
    self.items.push(item);
  }

  pub fn all<F>(&self, predicate: F) -> bool
  where
    F: Fn(&T) -> bool,
  {
    for item in &self.items {
      if !predicate(item) {
        return false;
      }
    }
    true
  }

  pub fn any<F>(&self, predicate: F) -> bool
  where
    F: Fn(&T) -> bool,
  {
    for item in &self.items {
      if predicate(item) {
        return true;
      }
    }
    false
  }
}

impl<T: PartialEq> VecSet<T> {
  pub fn union<I>(mut self, items: I) -> Self
  where
    I: IntoIterator<Item = T>,
  {
    for item in items {
      if !self.items.contains(&item) {
        self.items.push(item);
      }
    }
    self
  }

  pub fn retain(mut self, filter: impl Fn(&T) -> bool) -> Self {
    self.items.retain(filter);
    self
  }
}

impl<T: PartialEq> From<Vec<T>> for VecSet<T> {
  fn from(value: Vec<T>) -> Self {
    VecSet::from_iter(value)
  }
}

impl<T: PartialEq, const N: usize> From<[T; N]> for VecSet<T> {
  fn from(value: [T; N]) -> Self {
    VecSet::from_iter(value)
  }
}

impl<T: PartialEq> FromIterator<T> for VecSet<T> {
  fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
    let items = iter.into_iter().fold(Vec::new(), |mut items, item| {
      if !items.contains(&item) {
        items.push(item);
      }
      items
    });
    VecSet { items }
  }
}

impl<T: PartialEq> IntoIterator for VecSet<T> {
  type Item = T;
  type IntoIter = IntoIter<T>;

  fn into_iter(self) -> IntoIter<T> {
    self.items.into_iter()
  }
}

impl<T: PartialEq> Deref for VecSet<T> {
  type Target = [T];

  fn deref(&self) -> &[T] {
    &self.items
  }
}

pub struct WorkSet<T> {
  items: VecDeque<T>,
}
impl<T: PartialEq> WorkSet<T> {
  pub fn remove(&mut self) -> Option<T> {
    self.items.pop_front()
  }

  pub fn append(&mut self, item: T) {
    if !self.items.contains(&item) {
      self.items.push_back(item);
    }
  }
}

impl<T> From<VecDeque<T>> for WorkSet<T>
where
  T: Clone,
{
  fn from(value: VecDeque<T>) -> Self {
    let items = value;
    WorkSet { items }
  }
}

pub trait Separated {
  fn separated(&self, separator: &str) -> String;
}

impl<T> Separated for Vec<T>
where
  T: Display,
{
  fn separated(&self, separator: &str) -> String {
    self.iter().map(|item| item.to_string()).intersperse(separator.to_string()).collect()
  }
}

impl<T> Separated for VecSet<T>
where
  T: Display + PartialEq,
{
  fn separated(&self, separator: &str) -> String {
    self.items.iter().map(|item| item.to_string()).intersperse(separator.to_string()).collect()
  }
}
