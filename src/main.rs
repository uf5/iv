pub mod iv;

use crate::iv::syntax::{lexer::Lexer, parser::IVParser};
use std::io;

fn main() -> io::Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let lexer = Lexer::new(&input);
    let parser = IVParser::new();
    let module = parser.parse(&input, lexer).unwrap();
    println!("{:?}", module);
    Ok(())
}
