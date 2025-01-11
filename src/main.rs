use iv::evaluation::evaluator::Evaluator;
use iv::syntax::parse;
use iv::typing::inference::Inference;
use std::io;

fn main() -> io::Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let module = parse(&input).unwrap();
    println!("parsing:");
    println!("{:?}", module);
    let mut inf = Inference::new(&module);
    let inf_status = inf.typecheck().unwrap();
    println!("inference:");
    println!("{:?}", &inf_status);
    println!("evaluation:");
    let mut evaluator = Evaluator::new(&module);
    evaluator.eval_main().unwrap();
    println!("{:?}", evaluator.stack);
    Ok(())
}
