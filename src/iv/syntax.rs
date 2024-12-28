use lalrpop_util::lalrpop_mod;

mod lexer;
mod tokens;
lalrpop_mod!(parser, "/iv/syntax/parser.rs");

use super::types::Module;
use lexer::Lexer;
use parser::IVParser;

// TODO: return either instead of maybe
pub fn parse(input: &str) -> Option<Module> {
    let lexer = Lexer::new(input);
    let parser = IVParser::new();
    parser.parse(input, lexer).ok()
}
