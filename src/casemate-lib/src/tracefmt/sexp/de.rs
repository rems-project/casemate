use crate::shim::*;

use super::Sexp;

#[derive(Clone, Debug)]
pub enum SexpParseError {
    UnexpectedEOF,
    UnexpectedToken(usize, char),
}

impl fmt::Display for SexpParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnexpectedEOF => write!(f, "unexpected EOF"),
            Self::UnexpectedToken(i, t) => write!(f, "unexpected token '{t}' at position #{i}"),
        }
    }
}

impl StdError for SexpParseError {}

struct SExpParser<'s> {
    chars: iter::Peekable<str::Chars<'s>>,
    cur: usize,
}

fn is_word_char(c: char) -> bool {
    c.is_alphabetic() || c.is_numeric() || c == '_' || c == '-'
}

impl<'s> SExpParser<'s> {
    fn new(contents: &'s str) -> Self {
        Self {
            chars: contents.chars().peekable(),
            cur: 0,
        }
    }

    fn unexpected(&self, c: char) -> SexpParseError {
        SexpParseError::UnexpectedToken(self.cur, c)
    }

    fn peek(&mut self) -> Result<char, SexpParseError> {
        if let Some(c) = self.chars.peek() {
            Ok(*c)
        } else {
            Err(SexpParseError::UnexpectedEOF)
        }
    }

    fn at_eof(&mut self) -> bool {
        self.chars.peek().is_none()
    }

    fn accept(&mut self, expected: char) -> Result<(), SexpParseError> {
        let c = self.chars.next();
        match c {
            None => Err(SexpParseError::UnexpectedEOF),
            Some(c) if c == expected => Ok(()),
            Some(c) => Err(self.unexpected(c)),
        }
    }

    fn consume(&mut self) -> Result<char, SexpParseError> {
        self.cur += 1;
        self.chars.next().ok_or(SexpParseError::UnexpectedEOF)
    }

    fn consume_any_whitespace(&mut self) -> Result<(), SexpParseError> {
        while !self.at_eof() && self.peek()?.is_whitespace() {
            self.consume()?;
        }
        Ok(())
    }

    fn parse_list(&mut self) -> Result<Sexp, SexpParseError> {
        self.accept('(')?;
        self.consume_any_whitespace()?;

        let mut vs = Vec::new();

        while self.peek()? != ')' {
            vs.push(self.parse_exp()?);
            self.consume_any_whitespace()?;
        }

        self.accept(')')?;
        Ok(Sexp::List(vs))
    }

    fn parse_word(&mut self) -> Result<Sexp, SexpParseError> {
        let mut cs = Vec::new();
        while is_word_char(self.peek()?) {
            cs.push(self.consume()?);
        }
        Ok(Sexp::Val(String::from_iter(cs.iter())))
    }

    fn parse_str(&mut self) -> Result<Sexp, SexpParseError> {
        self.accept('"')?;
        let mut cs = Vec::new();
        cs.push('"');
        while self.peek()? != '"' {
            cs.push(self.consume()?);
        }
        self.accept('"')?;
        cs.push('"');
        Ok(Sexp::Val(String::from_iter(cs.iter())))
    }

    fn parse_exp(&mut self) -> Result<Sexp, SexpParseError> {
        self.consume_any_whitespace()?;
        match self.peek()? {
            '(' => self.parse_list(),
            '"' => self.parse_str(),
            _ => self.parse_word(),
        }
    }
}

pub fn parse_sexpr(contents: &str) -> Result<Sexp, SexpParseError> {
    let mut parser = SExpParser::new(contents);
    parser.parse_exp()
}
