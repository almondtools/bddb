use std::sync::Arc;

pub trait IntoVec<T> {
  fn into_vec(self) -> Vec<T>;
}

impl<T> IntoVec<Arc<str>> for T
where
  T: IntoVec<&'static str>,
{
  fn into_vec(self) -> Vec<Arc<str>> {
    let base: Vec<&'static str> = self.into_vec();
    base.into_iter().map(|e| Arc::from(e)).collect()
  }
}

impl IntoVec<&'static str> for &'static str {
  fn into_vec(self) -> Vec<&'static str> {
    vec![self]
  }
}

impl<T> IntoVec<T> for (T, T) {
  fn into_vec(self) -> Vec<T> {
    vec![self.0, self.1]
  }
}

impl<T> IntoVec<T> for (T, T, T) {
  fn into_vec(self) -> Vec<T> {
    vec![self.0, self.1, self.2]
  }
}

#[macro_export]
macro_rules! set {
  ($($arg:expr),*) => {{
    use std::collections::BTreeSet;

    let mut set : BTreeSet<Arc<str>> = BTreeSet::new();
    $(
        set.insert(Arc::from($arg));
    )*
    set
}};
}

#[macro_export]
macro_rules! relation {
  ($($arg:expr),*) => {{
    use std::collections::BTreeSet;
    use crate::util::sets::IntoVec;

    let mut set : BTreeSet<Vec<Arc<str>>> = BTreeSet::new();
    $(
      let arg :Vec<&'static str> = $arg.into_vec();
      let arg = arg.into_iter().map(|s| Arc::from(s)).collect::<Vec<Arc<str>>>();
      set.insert(arg);
    )*
    set
}};
}
