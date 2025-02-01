use iv::syntax::ast::Span;
use std::env;
use std::iter::repeat;

pub enum Mode {
    Typecheck,
    Evaluate,
    Compile,
}

pub struct CliArgs {
    pub mode: Mode,
    pub file_path: Option<String>,
}

impl CliArgs {
    pub fn new(args: env::Args) -> Self {
        let mut a = CliArgs {
            mode: Mode::Typecheck,
            file_path: None,
        };
        for arg in args.skip(1).rev() {
            match arg.as_str() {
                "--typecheck" => a.mode = Mode::Typecheck,
                "--evaluate" => a.mode = Mode::Evaluate,
                "--compile" => a.mode = Mode::Compile,
                _ => a.file_path = Some(arg),
            }
        }
        a
    }
}

pub fn print_span_in_source(source: &str, span: &Span) {
    for (i, line) in source.lines().enumerate() {
        let line_start = line.as_ptr() as usize - source.as_ptr() as usize;
        let line_end = line.as_ptr() as usize + line.len() - source.as_ptr() as usize;
        if line_start <= span.start && span.start <= line_end {
            let line_n = i + 1;
            let col_n = span.start - line_start;
            println!("line: {}, col: {}", line_n, col_n);
            println!("{}", line);
            println!("{}^", repeat(' ').take(col_n).collect::<String>());
        }
    }
}
