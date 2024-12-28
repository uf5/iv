pub mod iv;

use crate::iv::syntax::parse;
use std::io;

fn main() -> io::Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let module = parse(&input);
    println!("{:?}", module);
    Ok(())
}
