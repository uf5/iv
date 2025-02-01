use lalrpop_util::lalrpop_mod;

pub mod ast;
mod lexer;
pub mod module_wrapper;
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

pub fn parse(
    input: &str,
) -> Result<Module, lalrpop_util::ParseError<usize, tokens::Token<'_>, tokens::LexingError>> {
    let lexer = Lexer::new(input);
    let parser = IVParser::new();
    parser.parse(input, lexer)
}
