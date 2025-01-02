pub mod iv;

use crate::iv::syntax::parse;
use crate::iv::typing::inference::*;
use std::io;

fn main() -> io::Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let module = parse(&input).unwrap();
    println!("{:?}", module);
    let mut inf = Inference::new(&module);
    let inf_status = inf.infer();
    println!("inf status: {:?}", &inf_status);
    Ok(())
}
