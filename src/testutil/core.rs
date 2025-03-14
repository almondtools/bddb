#[macro_export]
macro_rules! since {
  (&$subject:expr) => {
    since!($subject)
  };
  ($subject:expr) => {
    since(&$subject).at(format!("{}:{}", file!(), line!()))
  };
}

pub fn since(description: &str) -> Description {
  Description {
    description: Some(description.to_string()),
    location: None,
  }
}

pub trait Locatable<T> {
  fn at(self, location: T) -> Self;
}

impl<L> Locatable<&str> for L
where
  L: Locatable<String>,
{
  fn at(self, location: &str) -> Self {
    self.at(location.to_string())
  }
}

pub struct Description {
  description: Option<String>,
  location: Option<String>,
}

impl Description {
  pub fn expect<S>(self, subject: &S) -> Subject<S> {
    Subject {
      subject,
      description: self.description,
      location: self.location,
    }
  }
}

impl Locatable<String> for Description {
  fn at(mut self, location: String) -> Self {
    self.location = Some(location);
    self
  }
}

#[macro_export]
macro_rules! expect_for {
  ($subject:expr) => {
    $subject.at(format!("{}:{}", file!(), line!()))
  };
}

#[macro_export]
macro_rules! expect {
  (&$subject:expr) => {
    expect!($subject)
  };
  ($subject:expr) => {
    expect(&$subject).at(format!("{}:{}", file!(), line!()))
  };
}

pub fn expect<S>(subject: &S) -> Subject<S> {
  Subject {
    subject,
    description: None,
    location: None,
  }
}

pub struct Subject<'a, S> {
  subject: &'a S,
  description: Option<String>,
  location: Option<String>,
}

impl<'a, S> Subject<'a, S> {
  pub fn subject(&self) -> &'a S {
    self.subject
  }

  #[allow(clippy::should_implement_trait)]
  pub fn not(self) -> NegativeConstrainedSubject<'a, S> {
    NegativeConstrainedSubject {
      subject: self.subject,
      description: self.description,
      location: self.location,
    }
  }
}

impl<'a, S> Locatable<String> for Subject<'a, S> {
  fn at(mut self, location: String) -> Self {
    self.location = Some(location);
    self
  }
}

pub struct NegativeConstrainedSubject<'a, S> {
  subject: &'a S,
  description: Option<String>,
  location: Option<String>,
}

impl<'a, S> NegativeConstrainedSubject<'a, S> {
  pub fn subject(&self) -> &'a S {
    self.subject
  }

  #[allow(clippy::should_implement_trait)]
  pub fn not(self) -> Subject<'a, S> {
    Subject {
      subject: self.subject,
      description: self.description,
      location: self.location,
    }
  }
}

impl<'a, S> Locatable<String> for NegativeConstrainedSubject<'a, S> {
  fn at(mut self, location: String) -> Self {
    self.location = Some(location);
    self
  }
}

pub trait Expecting<T> {
  fn expecting(self, expected: T) -> Self;
}

impl<E> Expecting<&str> for E
where
  E: Expecting<String>,
{
  fn expecting(self, expected: &str) -> Self {
    self.expecting(expected.to_string())
  }
}

pub trait Found<T> {
  fn found(self, actual: T) -> Self;
}

impl<F> Found<&str> for F
where
  F: Found<String>,
{
  fn found(self, actual: &str) -> Self {
    self.found(actual.to_string())
  }
}
pub struct Mismatch {
  description: Option<String>,
  expected: Option<String>,
  actual: Option<String>,
  location: Option<String>,
}

impl<'a, S> From<Subject<'a, S>> for Mismatch {
  fn from(subject: Subject<'a, S>) -> Self {
    Mismatch {
      description: subject.description.clone(),
      expected: None,
      actual: None,
      location: subject.location,
    }
  }
}

impl<'a, S> From<NegativeConstrainedSubject<'a, S>> for Mismatch {
  fn from(subject: NegativeConstrainedSubject<'a, S>) -> Self {
    Mismatch {
      description: subject.description.clone(),
      expected: None,
      actual: None,
      location: subject.location,
    }
  }
}

impl Mismatch {
  pub fn fail(self) -> ! {
    let location = self.location.map_or_else(String::new, |location| format!("at {}\n", location));

    let description = self.description.map_or_else(String::new, |description| format!("\n{}:", description));

    let expected = self.expected.unwrap_or_else(|| panic!("\n\tNo expectation \n{}", location));

    let actual = self.actual.unwrap_or_else(|| panic!("\n\tNo actual value \n{}", location));

    panic!(
      "{}\n\
       \texpected: {}\n\
       \t   found: {}\n\
       {}",
      description, expected, actual, location
    )
  }
}

impl Expecting<String> for Mismatch {
  fn expecting(mut self, expected: String) -> Self {
    self.expected = Some(expected);
    self
  }
}

impl Found<String> for Mismatch {
  fn found(mut self, actual: String) -> Self {
    self.actual = Some(actual);
    self
  }
}
