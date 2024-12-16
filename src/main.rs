#![feature(let_chains)]
#![feature(iter_intersperse)]
#![feature(iterator_try_collect)]
#![feature(iterator_try_reduce)]

use lang::datalogparser::SpecParser;

pub mod bdd;
pub mod lang;
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
      fn projecting() {
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

        assert_eq!(&*out.lock().unwrap(), &relation![("drei", "3"), ("eins", "1"), ("vier", "4"), ("zwei", "2")])
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

        assert_eq!(&*nnext.lock().unwrap(), &relation![("1", "3"), ("2", "4"), ("3", "1"), ("4", "2")])
      }

      #[test]
      fn recursive_joining() {
        let parser = SpecParser::new();
        let code = r#"
      numbers ~ 4 <- "numbers.domain";

      next[numbers,numbers] <- "next.relation";
      reaches4[numbers] -> "reaches4.relation";

      reaches4(n) <- next(n,"4");
      reaches4(n) <- next(n,t) & reaches4(t);
      "#;
        let spec = parser.parse(code).unwrap();

        let reaches = Arc::new(Mutex::new(BTreeSet::new()));

        let mut eval = Evaluator::new();
        eval.register_domain("numbers", DomainSource::Set(set!["1", "2", "3", "4"]));

        eval.register_in("next.relation", &["numbers", "numbers"], TupleSource::Set(relation![("1", "2"), ("2", "3"), ("3", "4"), ("4", "1")]));
        eval.register_out("reaches4.relation", &["numbers"], TupleStore::Set(reaches.clone()));

        let graph = RuleGraph::new().insert(spec).unwrap();
        let manager = BDDBManager::new(1024, 1024, 1);

        eval.execute(graph, manager).unwrap();

        assert_eq!(&*reaches.lock().unwrap(), &relation![("1"), ("2"), ("3")])
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

        assert_eq!(&*next.lock().unwrap(), &relation![("1", "2"), ("2", "3"), ("3", "4"), ("4", "1")])
      }
    }
  }
}
