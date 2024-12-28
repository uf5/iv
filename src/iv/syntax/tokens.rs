use logos::Logos;
use std::num::ParseIntError;

#[derive(Default, Debug, Clone, PartialEq)]
pub enum LexingError {
    InvalidInteger,
    #[default]
    Unexpected,
}

impl From<ParseIntError> for LexingError {
    fn from(_: ParseIntError) -> Self {
        LexingError::InvalidInteger
    }
}

#[derive(Debug, Logos, PartialEq, Clone)]
#[logos(error = LexingError)]
#[logos(skip r"[ \t\n\r]+")]
pub enum Token<'source> {
    #[token(".")]
    End,

    #[regex(r"[+-]?\d+", |lex| lex.slice().parse())]
    Number(i32),

    #[regex(r"[a-z][A-Za-z0-9]*'*", |lex| lex.slice())]
    LIdent(&'source str),

    #[regex(r"[A-Z][A-Za-z0-9]*'*", |lex| lex.slice())]
    UIdent(&'source str),

    #[token("define")]
    Define,
    #[token("data")]
    Data,

    #[token(":")]
    Colon,
    #[token(",")]
    Comma,

    #[token("[")]
    BracketOpen,
    #[token("]")]
    BracketClose,

    #[token("(")]
    ParenOpen,
    #[token(")")]
    ParenClose,

    #[token("{")]
    BraceOpen,
    #[token("}")]
    BraceClose,
}
