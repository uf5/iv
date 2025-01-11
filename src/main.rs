mod cli;

use iv::evaluation::evaluator::Evaluator;
use iv::syntax::parse;
use iv::typing::inference::Inference;
use std::env;
use std::fs;
use std::io;

fn main() {
    let cli_args = cli::CliArgs::new(env::args());
    let input = match cli_args.file_path {
        Some(file_path) => fs::read_to_string(file_path).expect("file read error"),
        None => io::read_to_string(io::stdin()).expect("stdin read error"),
    };
    match cli_args.mode {
        cli::Mode::Typecheck => {
            let module = parse(&input).unwrap();
            let mut inf = Inference::new(&module);
            println!("{:?}", inf.typecheck());
        }
        cli::Mode::Evaluate => {
            let module = parse(&input).unwrap();
            let mut evaluator = Evaluator::new(&module);
            evaluator.eval_main().expect("no main function");
            println!("{:?}", evaluator.stack);
        }
        cli::Mode::Compile => unimplemented!("compilation"),
    }
}
