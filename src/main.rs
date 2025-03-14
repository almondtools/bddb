#![feature(cell_update)]
#![feature(let_chains)]
#![feature(iter_intersperse)]
#![feature(iterator_try_collect)]
#![feature(iterator_try_reduce)]

use lang::datalogparser::SpecParser;

pub mod bdd;
pub mod lang;
pub mod testutil;
pub mod util;

fn main() {
  let _parser = SpecParser::new();
  todo!();
}

#[cfg(test)]
mod test {
  use std::collections::BTreeSet;
  use {relation, set};

  use super::*;

  mod solve {
    use std::sync::{Arc, Mutex};

    use bdd::domain::DomainSource;
    use bdd::evaluator::Evaluator;
    use lang::graph::RuleGraph;

    use super::*;

    mod simple_rules {

      use crate::bdd::database::BDDBManager;
      use crate::bdd::relation::{TupleSource, TupleStore};

      use super::*;

      #[test]
      fn projecting_simple() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";
      strings ~ 4 <- "strings.domain";

      names[numbers,strings] <- "names.relation";

      out[strings, numbers] -> "out.relation";

      out(string, number) <- names(number,string);
      "#;
        let spec = parser.parse(code).unwrap();

        let out = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));
        eval.register_domain("strings", DomainSource::Set(set!["eins", "zwei", "drei", "vier"]));
        eval.register_in(
          "names.relation",
          &["numbers", "strings"],
          TupleSource::Set(relation![("1", "eins"), ("2", "zwei"), ("3", "drei"), ("4", "vier")]),
        );
        eval.register_out("out.relation", &["strings", "numbers"], TupleStore::Set(out.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*out.lock().unwrap(), &relation![("drei", "3"), ("eins", "1"), ("vier", "4"), ("zwei", "2")]);
      }

      #[test]
      fn selecting() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";
      strings ~ 4 <- "strings.domain";

      names[numbers,strings] <- "names.relation";

      out[strings] -> "out.relation";

      out(string) <- names("2",string);
      "#;
        let spec = parser.parse(code).unwrap();

        let out = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));
        eval.register_domain("strings", DomainSource::Set(set!["eins", "zwei", "drei", "vier"]));
        eval.register_in(
          "names.relation",
          &["numbers", "strings"],
          TupleSource::Set(relation![("1", "eins"), ("2", "zwei"), ("3", "drei"), ("4", "vier")]),
        );
        eval.register_out("out.relation", &["strings"], TupleStore::Set(out.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*out.lock().unwrap(), &relation![("zwei")]);
      }

      #[test]
      fn selecting_gt() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";
      strings ~ 4 <- "strings.domain";

      names[numbers,strings] <- "names.relation";

      out[strings] -> "out.relation";

      out(string) <- names(n,string) & n > "2";
      "#;
        let spec = parser.parse(code).unwrap();

        let out = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));
        eval.register_domain("strings", DomainSource::Set(set!["eins", "zwei", "drei", "vier"]));
        eval.register_in(
          "names.relation",
          &["numbers", "strings"],
          TupleSource::Set(relation![("1", "eins"), ("2", "zwei"), ("3", "drei"), ("4", "vier")]),
        );
        eval.register_out("out.relation", &["strings"], TupleStore::Set(out.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*out.lock().unwrap(), &relation![("drei"), ("vier")]);
      }

      #[test]
      fn selecting_ge() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";
      strings ~ 4 <- "strings.domain";

      names[numbers,strings] <- "names.relation";

      out[strings] -> "out.relation";

      out(string) <- names(n,string) & n >= "2";
      "#;
        let spec = parser.parse(code).unwrap();

        let out = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));
        eval.register_domain("strings", DomainSource::Set(set!["eins", "zwei", "drei", "vier"]));
        eval.register_in(
          "names.relation",
          &["numbers", "strings"],
          TupleSource::Set(relation![("1", "eins"), ("2", "zwei"), ("3", "drei"), ("4", "vier")]),
        );
        eval.register_out("out.relation", &["strings"], TupleStore::Set(out.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*out.lock().unwrap(), &relation![("zwei"), ("drei"), ("vier")]);
      }

      #[test]
      fn selecting_lt() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";
      strings ~ 4 <- "strings.domain";

      names[numbers,strings] <- "names.relation";

      out[strings] -> "out.relation";

      out(string) <- names(n,string) & n < "2";
      "#;
        let spec = parser.parse(code).unwrap();

        let out = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));
        eval.register_domain("strings", DomainSource::Set(set!["eins", "zwei", "drei", "vier"]));
        eval.register_in(
          "names.relation",
          &["numbers", "strings"],
          TupleSource::Set(relation![("1", "eins"), ("2", "zwei"), ("3", "drei"), ("4", "vier")]),
        );
        eval.register_out("out.relation", &["strings"], TupleStore::Set(out.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*out.lock().unwrap(), &relation![("eins")]);
      }

      #[test]
      fn selecting_le() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";
      strings ~ 4 <- "strings.domain";

      names[numbers,strings] <- "names.relation";

      out[strings] -> "out.relation";

      out(string) <- names(n,string) & n <= "2";
      "#;
        let spec = parser.parse(code).unwrap();

        let out = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));
        eval.register_domain("strings", DomainSource::Set(set!["eins", "zwei", "drei", "vier"]));
        eval.register_in(
          "names.relation",
          &["numbers", "strings"],
          TupleSource::Set(relation![("1", "eins"), ("2", "zwei"), ("3", "drei"), ("4", "vier")]),
        );
        eval.register_out("out.relation", &["strings"], TupleStore::Set(out.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*out.lock().unwrap(), &relation![("eins"), ("zwei")]);
      }

      #[test]
      fn selecting_ne() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";
      strings ~ 4 <- "strings.domain";

      names[numbers,strings] <- "names.relation";

      out[strings] -> "out.relation";

      out(string) <- names(n,string) & n != "2";
      "#;
        let spec = parser.parse(code).unwrap();

        let out = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));
        eval.register_domain("strings", DomainSource::Set(set!["eins", "zwei", "drei", "vier"]));
        eval.register_in(
          "names.relation",
          &["numbers", "strings"],
          TupleSource::Set(relation![("1", "eins"), ("2", "zwei"), ("3", "drei"), ("4", "vier")]),
        );
        eval.register_out("out.relation", &["strings"], TupleStore::Set(out.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*out.lock().unwrap(), &relation![("eins"), ("drei"), ("vier")]);
      }

      #[test]
      fn joining() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";

      next[numbers,numbers] <- "next.relation";
      nnext[numbers,numbers] -> "nnext.relation";

      nnext(n, m) <- next(n,t) & next(t,m);
      "#;
        let spec = parser.parse(code).unwrap();

        let nnext = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));

        eval.register_in("next.relation", &["numbers", "numbers"], TupleSource::Set(relation![("1", "2"), ("2", "3"), ("3", "4"), ("4", "1")]));
        eval.register_out("nnext.relation", &["numbers", "numbers"], TupleStore::Set(nnext.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*nnext.lock().unwrap(), &relation![("1", "3"), ("2", "4"), ("3", "1"), ("4", "2")]);
      }

      #[test]
      fn joining_two_predicates() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";
      strings ~ 4 <- "strings.domain";

      names[numbers,strings] <- "names.relation";
      le2[numbers] <- "le2.relation";

      out[strings] -> "out.relation";
      
      out(s) <- names(n,s) & le2(n);
      "#;
        let spec = parser.parse(code).unwrap();

        let out = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));
        eval.register_domain("strings", DomainSource::Set(set!["eins", "zwei", "drei", "vier"]));
        eval.register_in(
          "names.relation",
          &["numbers", "strings"],
          TupleSource::Set(relation![("1", "eins"), ("2", "zwei"), ("3", "drei"), ("4", "vier")]),
        );
        eval.register_in("le2.relation", &["numbers"], TupleSource::Set(relation![("1"), ("2")]));
        eval.register_out("out.relation", &["strings", "numbers"], TupleStore::Set(out.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*out.lock().unwrap(), &relation![("eins"), ("zwei")]);
      }

      #[test]
      fn joining_and_selecting() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";

      next[numbers,numbers] <- "next.relation";
      nnext[numbers,numbers] -> "nnext.relation";

      nnext(n, m) <- next(n,t) & next(t,m) & m = "4";
      "#;
        let spec = parser.parse(code).unwrap();

        let nnext = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));

        eval.register_in("next.relation", &["numbers", "numbers"], TupleSource::Set(relation![("1", "2"), ("2", "3"), ("3", "4"), ("4", "1")]));
        eval.register_out("nnext.relation", &["numbers", "numbers"], TupleStore::Set(nnext.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*nnext.lock().unwrap(), &relation![("2", "4")]);
      }

      #[test]
      fn loop_joining() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";

      next[numbers,numbers] <- "next.relation";
      reaches4[numbers] -> "reaches4.relation";

      reaches4(n) <- next(n,"4");
      reaches4(n) <- next(n, t) & reaches4(t);
      "#;
        let spec = parser.parse(code).unwrap();

        let reaches = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));

        eval.register_in("next.relation", &["numbers", "numbers"], TupleSource::Set(relation![("1", "2"), ("2", "3"), ("3", "4")]));
        eval.register_out("reaches4.relation", &["numbers"], TupleStore::Set(reaches.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*reaches.lock().unwrap(), &relation![("1"), ("2"), ("3")]);
      }

      #[test]
      fn mixed_loop_joining() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";

      base[numbers,numbers] <- "base.relation";
      inner[numbers,numbers] -> "inner.relation";

      inner(n,m) <- base(n,m) & m = "1";
      inner(n,m) <- base(n,t) & inner(t,m);
      "#;
        let spec = parser.parse(code).unwrap();

        let inner = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));

        eval.register_in("base.relation", &["numbers", "numbers"], TupleSource::Set(relation![("1", "2"), ("2", "3"), ("3", "4"), ("4", "1")]));
        eval.register_out("inner.relation", &["numbers", "numbers"], TupleStore::Set(inner.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*inner.lock().unwrap(), &relation![("1", "1"), ("1", "2"), ("1", "3"), ("1", "4")]);
      }

      #[test]
      fn multiple_loop_joining() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";

      base[numbers,numbers] <- "base.relation";
      inner[numbers,numbers] -> "inner.relation";
      outer[numbers,numbers,numbers] -> "outer.relation";

      inner(n,m) <- base(n,m) & m = "1";
      inner(n,m) <- base(n,t) & inner(t,m);

      outer(n,m,l) <- inner(n,m) & l = "4";
      outer(n,m,l) <- outer(n,m,t) & inner(t,l);
      "#;
        let spec = parser.parse(code).unwrap();

        let inner = Arc::new(Mutex::new(BTreeSet::new()));
        let outer = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));

        eval.register_in("base.relation", &["numbers", "numbers"], TupleSource::Set(relation![("1", "2"), ("2", "3"), ("3", "4"), ("4", "1")]));
        eval.register_out("inner.relation", &["numbers", "numbers"], TupleStore::Set(inner.clone()));
        eval.register_out("outer.relation", &["numbers", "numbers", "numbers"], TupleStore::Set(outer.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*inner.lock().unwrap(), &relation![("1", "1"), ("1", "2"), ("1", "3"), ("1", "4")]);
        assert_eq!(&*outer.lock().unwrap(), &relation![("todo")]);
      }

      #[test]
      fn nested_loop_joining() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";

      base[numbers,numbers] <- "base.relation";
      inner[numbers,numbers];
      outer[numbers,numbers,numbers] -> "outer.relation";

      inner(n,m) <- base(n,m) & outer(n,m,"4");
      inner(n,m) <- base(n,t) & inner(t,m);

      outer(n,m,l) <- inner(n,m) & l = "4";
      outer(n,m,l) <- outer(n,m,t) & inner(t,l);
      "#;
        let spec = parser.parse(code).unwrap();

        let outer = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));

        eval.register_in("base.relation", &["numbers", "numbers"], TupleSource::Set(relation![("1", "2"), ("2", "3"), ("3", "4"), ("4", "1")]));
        eval.register_out("outer.relation", &["numbers", "numbers", "numbers"], TupleStore::Set(outer.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*outer.lock().unwrap(), &relation![("todo")]);
      }

      #[test]
      fn overlapping_loop_joining() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";

      fix[numbers] <- "fix.relation";
      base[numbers,numbers] <- "base.relation";
      out[numbers,numbers] -> "out.relation";

      out(n,m) <- base(n,m) & fix(m);
      out(n,m) <- out(n,t) & base(t,m);
      out(n,m) <- base(n,t) & out(t,m);
      "#;
        let spec = parser.parse(code).unwrap();

        let out = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4", "5", "6"]));

        eval.register_in("fix.relation", &["numbers"], TupleSource::Set(relation!["3"]));
        eval.register_in("base.relation", &["numbers", "numbers"], TupleSource::Set(relation![("1", "2"), ("2", "3"), ("3", "4")]));
        eval.register_out("out.relation", &["numbers", "numbers"], TupleStore::Set(out.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*out.lock().unwrap(), &relation![("1", "3"), ("2", "3"), ("2", "4"), ("1", "4")]);
      }

      #[test]
      fn cross_loop_joining() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";

      lbase[numbers,numbers] <- "lbase.relation";
      rbase[numbers,numbers] <- "rbase.relation";
      left[numbers,numbers] -> "left.relation";
      right[numbers,numbers] -> "right.relation";

      left(n,m) <- lbase(n,m);
      left(n,m) <- right(n,t) & lbase(t,m);
      right(n,m) <- rbase(n,m);
      right(n,m) <- left(n,t) & rbase(t,m);
      "#;
        let spec = parser.parse(code).unwrap();

        let left = Arc::new(Mutex::new(BTreeSet::new()));
        let right = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));

        eval.register_in("lbase.relation", &["numbers", "numbers"], TupleSource::Set(relation![("1", "2"), ("2", "3")]));
        eval.register_in("rbase.relation", &["numbers", "numbers"], TupleSource::Set(relation![("3", "4"), ("4", "1")]));
        eval.register_out("left.relation", &["numbers", "numbers"], TupleStore::Set(left.clone()));
        eval.register_out("right.relation", &["numbers", "numbers"], TupleStore::Set(right.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*left.lock().unwrap(), &relation![("todo")]);
        assert_eq!(&*right.lock().unwrap(), &relation![("todo")]);
      }

      #[test]
      fn unioning() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";

      next1[numbers,numbers] <- "next1.relation";
      next2[numbers,numbers] <- "next2.relation";
      next[numbers,numbers] -> "next.relation";

      next(n, m) <- next1(n,m);
      next(n, m) <- next2(n,m);
      "#;
        let spec = parser.parse(code).unwrap();

        let next = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));

        eval.register_in("next1.relation", &["numbers", "numbers"], TupleSource::Set(relation![("1", "2"), ("2", "3")]));
        eval.register_in("next2.relation", &["numbers", "numbers"], TupleSource::Set(relation![("3", "4"), ("4", "1")]));
        eval.register_out("next.relation", &["numbers", "numbers"], TupleStore::Set(next.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*next.lock().unwrap(), &relation![("1", "2"), ("2", "3"), ("3", "4"), ("4", "1")]);
      }
    }
  }
}
