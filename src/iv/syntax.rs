use lalrpop_util::lalrpop_mod;

pub mod lexer;
mod tokens;
lalrpop_mod!(pub parser, "/iv/syntax/parser.rs");
