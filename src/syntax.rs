use lalrpop_util::lalrpop_mod;

pub mod ast;
mod lexer;
mod tokens;

lalrpop_mod!(
    #[allow(clippy::all)]
    #[rustfmt::skip]
    parser,
    "/syntax/parser.rs"
);

use ast::Module;
use lexer::Lexer;
use parser::IVParser;

pub fn parse(input: &str) -> Result<Module, String> {
    let lexer = Lexer::new(input);
    let parser = IVParser::new();
    parser.parse(input, lexer).map_err(|e| format!("{:?}", e))
}
