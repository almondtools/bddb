use lalrpop_util::lalrpop_mod;

pub mod datalog_lalr;
lalrpop_mod!(pub datalogparser,"/lang/datalogparser.rs");
pub mod ast;
pub mod source;
pub mod graph;
pub mod ir;
