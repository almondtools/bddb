pub mod contains;
pub mod contains_in_order;
pub mod empty;
pub mod equal_to;
pub mod matches;

pub trait Matcher<T> {
  fn matches(&self, actual: &T) -> bool;
}

impl<T> Matcher<T> for T
where
  T: PartialEq<T>,
{
  fn matches(&self, actual: &T) -> bool {
    self == actual
  }
}
