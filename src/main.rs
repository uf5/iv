use iv::syntax::parse;
use iv::typing::inference::Inference;
use std::io;

fn main() -> io::Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let module = parse(&input).unwrap();
    println!("{:?}", module);
    let mut inf = Inference::new(&module);
    let inf_status = inf.typecheck();
    println!("inf status: {:?}", &inf_status);
    Ok(())
}
