pub mod cursor;
pub mod line_data;
pub mod spam;
pub mod token;

pub use cursor::*;
pub use line_data::*;
pub use spam::*;
pub use token::*;

use std::{fmt::Debug, ops::Deref, rc::Rc, str::Chars};

pub struct Lexer {
    cursor: Cursor,
    file_name: Rc<String>,
}

impl Lexer {
    pub fn new(file_name: String, file: String) -> Lexer {
        let file = Rc::new(file);
        let file_name = Rc::new(file_name);
        Lexer {
            cursor: Cursor::new(Spam::whole(&file)),
            file_name,
        }
    }

    fn ident(&mut self) -> Option<Token> {
        let line_data = self.line_data();
        let start = self.cursor.progress();
        loop {
            let char = self.cursor.peek().unwrap_or('\0');
            if !char.is_alphanumeric() && char != '_' {
                break;
            }
            self.cursor.advance();
        }
        let end = self.cursor.progress();
        let value = self.cursor.sub(start..end);
        let kind = match value.deref() {
            "fun" => TKind::Fun,
            "attr" => TKind::Attr,
            "pass" => TKind::Pass,
            "mut" => TKind::Mut,
            "return" => TKind::Return,
            "if" => TKind::If,
            "elif" => TKind::Elif,
            "else" => TKind::Else,
            "let" => TKind::Let,
            "var" => TKind::Var,
            "svar" => TKind::Svar,
            "loop" => TKind::Loop,
            "break" => TKind::Break,
            "continue" => TKind::Continue,
            "struct" => TKind::Struct,
            "embed" => TKind::Embed,
            "max" | "min" | "as" | "abs" => TKind::Op,
            "true" => TKind::Bool(true),
            "false" => TKind::Bool(false),
            _ => TKind::Ident,
        };
        Some(Token::new(kind, value, line_data))
    }

    fn op(&mut self) -> Option<Token> {
        let line_data = self.line_data();
        let start = self.cursor.progress();
        while self.cursor.peek().unwrap_or('\0').is_operator() {
            self.cursor.advance();
        }
        let end = self.cursor.progress();
        let value = self.cursor.sub(start..end);
        let kind = match value.deref() {
            ":" => TKind::Colon,
            "->" => TKind::RArrow,
            _ => TKind::Op,
        };
        Some(Token::new(kind, value, line_data))
    }

    fn indent(&mut self) -> Option<Token> {
        let line_data = self.line_data();
        let start = self.cursor.progress();
        self.cursor.advance();
        let mut indentation = 0;
        loop {
            match self.cursor.peek()? {
                ' ' => {
                    self.cursor.advance();
                    indentation += 1;
                }
                '\t' => {
                    self.cursor.advance();
                    indentation += 2;
                }
                '\r' => {
                    self.cursor.advance();
                }
                _ => break,
            }
        }
        let end = self.cursor.progress();
        let value = self.cursor.sub(start..end);
        Some(Token::new(TKind::Indent(indentation / 2), value, line_data))
    }

    fn number(&mut self) -> Option<Token> {
        let mut number = 0u64;
        let mut fraction = 0u64;
        let mut exponent = 1i64;
        let start = self.cursor.progress();
        let line_data = self.line_data();
        while self.cursor.peek().unwrap_or('\0').is_numeric() {
            number = number * 10 + (self.cursor.advance().unwrap() as u64 - '0' as u64);
        }
        let is_float = self.cursor.peek()? == '.';
        if is_float {
            self.cursor.advance();
            while self.cursor.peek().unwrap_or('\0').is_numeric() {
                fraction = fraction * 10 + (self.cursor.advance().unwrap() as u64 - '0' as u64);
                exponent *= 10;
            }
        }
        let next_char = self.cursor.peek().unwrap_or('\0');
        let kind = match next_char {
            'i' | 'u' | 'f' => {
                self.cursor.advance();
                let mut base = 0u16;
                while self.cursor.peek().unwrap_or('\0').is_numeric() {
                    base = base * 10 + (self.cursor.advance().unwrap() as u16 - '0' as u16);
                }
                match next_char {
                    'i' => TKind::Int(number as i64, base),
                    'u' => TKind::Uint(number, base),
                    'f' => TKind::Float(number as f64 + fraction as f64 / exponent as f64, base),
                    _ => unreachable!(),
                }
            }
            _ => {
                if fraction == 0 && !is_float {
                    TKind::Int(number as i64, 64)
                } else {
                    TKind::Float(number as f64 + fraction as f64 / exponent as f64, 64)
                }
            }
        };
        let end = self.cursor.progress();
        let value = self.cursor.sub(start..end);
        Some(Token::new(kind, value, line_data))
    }

    fn char_or_label(&mut self) -> Option<Token> {
        let line_data = self.line_data();
        let start = self.cursor.progress();
        self.cursor.advance()?;
        let current = self.cursor.advance()?;

        let (char, may_be_label) = if current == '\\' {
            let start = self.cursor.progress();
            (
                match self.char_escape() {
                    Some(c) => c,
                    None => {
                        let end = self.cursor.progress();
                        return Some(Token::new(
                            TKind::InvalidChar,
                            self.cursor.sub(start..end),
                            self.line_data(),
                        ));
                    }
                },
                false,
            )
        } else {
            (current, true)
        };

        let next = self.cursor.peek().unwrap_or('\0');

        if !may_be_label && next != '\'' {
            return None;
        }

        if next == '\'' {
            self.cursor.advance();
            let end = self.cursor.progress();
            let value = self.cursor.sub(start..end);
            Some(Token::new(TKind::Char(char), value, line_data))
        } else {
            while self.cursor.peek().unwrap_or('\0').is_alphanumeric() {
                self.cursor.advance();
            }
            let end = self.cursor.progress();
            let value = self.cursor.sub(start..end);
            Some(Token::new(TKind::Label, value, line_data))
        }
    }

    fn string(&mut self) -> Option<Token> {
        let line_data = self.line_data();
        let start = self.cursor.progress();
        self.cursor.advance()?;
        let mut string_data = Vec::new();
        loop {
            match self.cursor.peek()? {
                '\\' => {
                    let start = self.cursor.progress();
                    match self.char_escape() {
                        Some(ch) => {
                            let len = string_data.len();
                            string_data.resize(len + ch.len_utf8(), 0);
                            ch.encode_utf8(&mut string_data[len..]);
                        }
                        None => {
                            let end = self.cursor.progress();
                            return Some(Token::new(
                                TKind::InvalidChar,
                                self.cursor.sub(start..end),
                                self.line_data(),
                            ));
                        }
                    }
                }
                '"' => {
                    self.cursor.advance();
                    break;
                }
                _ => {
                    let ch = self.cursor.advance()?;
                    let len = string_data.len();
                    string_data.resize(len + ch.len_utf8(), 0);
                    ch.encode_utf8(&mut string_data[len..]);
                }
            }
        }

        // note: we don't care if string has incorrect encoding
        let end = self.cursor.progress();
        let value = self.cursor.sub(start..end);
        Some(Token::new(
            TKind::String(Rc::new(string_data)),
            value,
            line_data,
        ))
    }

    fn char_escape(&mut self) -> Option<char> {
        self.cursor.advance();
        let current = self.cursor.advance().unwrap_or('\0');
        Some(match current {
            'a' | 'b' | 'e' | 'f' | 'n' | 'r' | 't' | 'v' | '\\' | '\'' | '"' => match current {
                'a' => '\x07',
                'b' => '\x08',
                'e' => '\x1b',
                'f' => '\x0c',
                'v' => '\x0b',
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                _ => current,
            },
            '0'..='7' => {
                let mut res = 0u8;
                for _ in 0..3 {
                    res = res * 8 + (self.cursor.advance()?.to_digit(8)? as u8 - '0' as u8);
                }
                res as char
            }
            'x' | 'u' | 'U' => {
                let len = match current {
                    'x' => 2,
                    'u' => 4,
                    'U' => 8,
                    _ => unreachable!(),
                };

                let mut res = 0u32;
                for _ in 0..len {
                    res = res * 16 + (self.cursor.advance()?.to_digit(16)? - '0' as u32);
                }
                return char::from_u32(res);
            }
            _ => return None,
        })
    }

    fn line_data(&self) -> LineData {
        LineData::new(
            self.cursor.line(),
            self.cursor.column(),
            Spam::whole(&self.file_name),
        )
    }
}

impl<'a> Iterator for Lexer {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let char = self.cursor.peek()?;
        if char.is_alphabetic() || char == '_' {
            return self.ident();
        }
        if char.is_operator() {
            return self.op();
        }
        if char.is_numeric() {
            return self.number();
        }

        let kind = match char {
            '\n' => return self.indent(),
            ' ' | '\r' | '\t' => {
                while matches!(self.cursor.peek()?, ' ' | '\t' | '\r') {
                    self.cursor.advance();
                }
                return self.next();
            }
            '\'' => return self.char_or_label(),
            '"' => return self.string(),
            '#' => TKind::Hash,
            ',' => TKind::Comma,
            '(' => TKind::LPar,
            ')' => TKind::RPar,
            '{' => TKind::LCurly,
            '}' => TKind::RCurly,
            '[' => TKind::LBra,
            ']' => TKind::RBra,
            '.' => TKind::Dot,

            _ => TKind::UnknownCharacter(char),
        };

        let line_data = self.line_data();
        let start = self.cursor.progress();
        self.cursor.advance();
        Some(Token::new(
            kind,
            self.cursor.sub(start..start + 1),
            line_data,
        ))
    }
}

impl IsOperator for char {
    fn is_operator(&self) -> bool {
        matches!(
            self,
            '+' | '-' | '*' | '/' | '%' | '^' | '=' | '<' | '>' | '!' | '&' | '|' | '?' | ':' | '~'
        )
    }
}

pub trait IsOperator {
    fn is_operator(&self) -> bool;
}

//#[cfg(feature = "testing")]
pub fn test() {
    let lexer = Lexer::new(
        "test_code.pmh".to_string(),
        crate::testing::TEST_CODE.to_string(),
    );

    lexer.for_each(|token| println!("{:?}", token));
}
