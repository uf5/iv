mod cli;

use iv::evaluation::evaluator::Evaluator;
use iv::syntax::ast::Span;
use iv::syntax::parse;
use iv::typing::inference::Inference;
use std::env;
use std::fs;
use std::io;

use lalrpop_util::ParseError;

fn main() {
    let cli_args = cli::CliArgs::new(env::args());
    let input = match cli_args.file_path {
        Some(file_path) => fs::read_to_string(file_path).expect("file read error"),
        None => io::read_to_string(io::stdin()).expect("stdin read error"),
    };
    let module = match parse(&input) {
        Ok(module) => module,
        Err(
            err @ ParseError::UnrecognizedToken {
                token: (loc, _, _), ..
            },
        )
        | Err(err @ ParseError::InvalidToken { location: loc, .. })
        | Err(err @ ParseError::UnrecognizedEof { location: loc, .. })
        | Err(err @ ParseError::ExtraToken { token: (loc, _, _) }) => {
            let span = Span {
                start: loc,
                end: loc,
            };
            cli::print_span_in_source(&input, &span);
            panic!("parsing error {:?}", err)
        }
        Err(err) => {
            panic!("parsing error {:?}", err)
        }
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
