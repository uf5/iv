use std::env;

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
