pub mod spam;

pub use spam::*;

use std::{
    fmt::{Debug, Display},
    ops::{Deref, Range},
    rc::Rc,
    str::Chars,
};

pub struct TokenView {
    repr: String,
}

impl TokenView {
    pub fn new(token: &Token) -> Self {
        if token.kind == TKind::None {
            return Self {
                repr: String::from("|> no line information"),
            };
        }

        let mut range = token.spam.range.clone();
        let string = token.spam.string();
        if string[range.start..range.end].starts_with("\n") {
            range.start += 1;
        }
        let mut repr = String::new();
        repr.push_str(format!("|> {}\n", token.line_data).as_str());
        repr.push_str("|");

        let end = string[range.end..]
            .find('\n')
            .map(|i| i + range.end)
            .unwrap_or(string.len());
        let start = string[..range.start].rfind('\n').unwrap_or(0) + 1;

        let mut new_string = String::with_capacity(range.end - range.start);
        new_string.push_str(&string[start..range.start]);
        let mut max = 0;
        let mut min = range.start - start;
        let mut i = min;
        for ch in string[range.start..range.end].chars() {
            new_string.push(ch);
            if ch.is_whitespace() {
                if ch == '\n' {
                    new_string.push_str("|");
                    i = 0;
                }
            } else {
                max = (i + 1).max(max);
                min = (i - 1).min(min);
            }
            i += 1;
        }

        repr.push_str(&new_string);
        repr.push_str(&string[range.end..end]);
        repr.push_str("\n|");
        repr.extend(std::iter::repeat(' ').take(min));
        repr.extend(std::iter::repeat('^').take(max - min));

        Self { repr }
    }
}

impl Display for TokenView {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.repr)
    }
}

#[derive(Debug, Default)]
pub struct Lexer {
    cursor: Cursor,
    file_name: &'static str,
}

impl Lexer {
    pub fn new(file_name: String, file: String) -> Lexer {
        let file_name = Box::leak(file_name.into_boxed_str());
        Lexer {
            cursor: Cursor::new(file),
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
            "priv" => TKind::Priv,
            "pub" => TKind::Pub,
            "use" => TKind::Use,
            "extern" => TKind::Extern,
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
            "::" => TKind::DoubleColon,
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
        let start = self.cursor.progress();
        let line_data = self.line_data();
        let number = match self.parse_number_err(10) {
            Ok((number, _)) => number,
            Err(token) => return Some(token),
        };
        let is_float = self.cursor.peek()? == '.';
        let (fraction, exponent) = if is_float {
            self.cursor.advance();
            match self.parse_number_err(10) {
                Ok(number) => number,
                Err(token) => return Some(token),
            }
        } else {
            (0, 0)
        };
        let next_char = self.cursor.peek().unwrap_or('\0');
        let kind = match next_char {
            'i' | 'u' | 'f' => {
                self.cursor.advance();
                let base = match self.parse_number_err(10) {
                    Ok((number, _)) => number as u16,
                    Err(token) => return Some(token),
                };
                match next_char {
                    'i' => TKind::Int(number as i64, base),
                    'u' => TKind::Uint(number, base),
                    'f' => TKind::Float(number as f64 + fraction as f64 / exponent as f64, base),
                    _ => unreachable!(),
                }
            }
            _ => {
                if fraction == 0 && !is_float {
                    TKind::Int(number as i64, 0)
                } else {
                    TKind::Float(number as f64 + fraction as f64 / exponent as f64, 64)
                }
            }
        };
        let end = self.cursor.progress();
        let value = self.cursor.sub(start..end);
        Some(Token::new(kind, value, line_data))
    }

    fn parse_number_err(&mut self, base: u64) -> Result<(u64, u64), Token> {
        let start = self.cursor.progress();
        self.parse_number(base).ok_or_else(|| {
            let line_data = self.line_data();
            let end = self.cursor.progress();
            let value = self.cursor.sub(start..end);
            Token::new(TKind::InvalidChar, value, line_data)
        })
    }

    fn parse_number(&mut self, base: u64) -> Option<(u64, u64)> {
        let mut number = 0u64;
        let mut exponent = 1u64;
        let base32 = base as u32;
        loop {
            let ch = self.cursor.peek().unwrap_or('\0');
            if ch == '_' {
                self.cursor.advance();
                continue;
            }
            if !ch.is_numeric() {
                break Some((number, exponent));
            }
            number = number * base + self.cursor.advance().unwrap().to_digit(base32)? as u64;
            exponent *= base;
        }
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
        let mut string_data = vec![];
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

        string_data.push(0);

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
                let mut res = 0u8 + current as u8 - '0' as u8;
                for _ in 0..2 {
                    res = res * 8 + self.cursor.advance()?.to_digit(8)? as u8;
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
                    res = res * 16 + self.cursor.advance()?.to_digit(16)?;
                }
                return char::from_u32(res);
            }
            _ => return None,
        })
    }

    fn line_data(&self) -> LineData {
        LineData::new(
            self.cursor.line,
            self.cursor.column(),
            Spam::whole(&self.file_name),
        )
    }

    pub fn file_name(&self) -> &'static str {
        self.file_name
    }
}

impl Clone for Lexer {
    fn clone(&self) -> Self {
        unsafe { std::ptr::read(self as *const _) }
    }
}

impl Iterator for Lexer {
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

#[derive(Debug, Clone)]
pub struct Cursor {
    data: &'static str,
    chars: Chars<'static>,
    line: usize,
    last_n_line: usize,
}

impl Default for Cursor {
    fn default() -> Self {
        Self {
            data: "",
            chars: "".chars(),
            line: 1,
            last_n_line: 1,
        }
    }
}

impl Cursor {
    pub fn new(data: String) -> Self {
        let data = Box::leak(data.into_boxed_str());
        Cursor {
            //SAFETY: cursor disposes data only upon drop
            chars: data.chars(),
            data,
            line: 1,
            last_n_line: 0,
        }
    }

    pub fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }

    pub fn peek_n(&self, n: usize) -> Option<char> {
        self.chars.clone().nth(n)
    }

    pub fn progress(&self) -> usize {
        self.data.len() - self.chars.as_str().len()
    }

    #[inline]
    pub fn advance(&mut self) -> Option<char> {
        let char = self.chars.next();
        if char == Some('\n') {
            self.line += 1;
            self.last_n_line = self.progress();
        }
        char
    }

    pub fn sub(&self, range: Range<usize>) -> Spam {
        Spam::new(self.data, range)
    }

    pub fn column(&self) -> usize {
        self.progress() - self.last_n_line
    }
}

#[derive(Debug, Clone, Default)]
pub struct Token {
    pub kind: TKind,
    pub spam: Spam,
    pub line_data: LineData,
}

impl Token {
    pub fn builtin(spam: &'static str) -> Self {
        Token {
            kind: TKind::Ident,
            spam: Spam::whole(spam),
            line_data: LineData::default(),
        }
    }

    pub fn new(kind: TKind, spam: Spam, line_data: LineData) -> Self {
        Token {
            kind,
            spam,
            line_data,
        }
    }

    pub fn eof() -> Self {
        Token {
            kind: TKind::Eof,
            spam: Spam::default(),
            line_data: LineData::default(),
        }
    }

    pub fn to_group(&mut self, end: &Token, trim: bool) {
        self.spam = self.spam.join(&end.spam, trim);
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {:?}", self.kind, self.spam)?;
        Ok(())
    }
}

impl PartialEq<Token> for Token {
    fn eq(&self, other: &Token) -> bool {
        self.kind == other.kind && self.spam == other.spam
    }
}

impl PartialEq<TKind> for Token {
    fn eq(&self, other: &TKind) -> bool {
        self.kind == *other
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum TKind {
    Pub,
    Priv,
    Use,
    Extern,
    Fun,
    Attr,
    Pass,
    Mut,
    Return,
    If,
    Elif,
    Else,
    Var,
    Let,
    Loop,
    Break,
    Continue,
    Struct,
    Embed,

    Label,
    Ident,
    Op,

    LPar,
    RPar,
    LCurly,
    RCurly,
    LBra,
    RBra,
    Colon,
    DoubleColon,
    Comma,
    RArrow,
    Hash,
    Dot,

    Int(i64, u16),
    Uint(u64, u16),
    Float(f64, u16),
    Bool(bool),
    Char(char),
    InvalidChar,
    String(Rc<Vec<u8>>),

    Indent(usize),

    Group,

    UnknownCharacter(char),
    Eof,
    None,
}

impl std::fmt::Display for TKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match *self {
            TKind::Priv => "'priv'",
            TKind::Pub => "'pub'",
            TKind::Use => "'use'",
            TKind::Extern => "'extern'",
            TKind::Fun => "'fun'",
            TKind::Attr => "'attr'",
            TKind::Pass => "'pass'",
            TKind::Mut => "'mut'",
            TKind::Return => "'return'",
            TKind::If => "'if'",
            TKind::Elif => "'elif'",
            TKind::Else => "'else'",
            TKind::Var => "'var'",
            TKind::Let => "'let'",
            TKind::Loop => "'loop'",
            TKind::Break => "'break'",
            TKind::Continue => "'continue'",
            TKind::Struct => "'struct'",
            TKind::Embed => "'embed'",
            TKind::Label => "'label'",
            TKind::Ident => "ident",
            TKind::Op => "operator",
            TKind::LPar => "'('",
            TKind::RPar => "')'",
            TKind::LCurly => "'{'",
            TKind::RCurly => "'}'",
            TKind::LBra => "'['",
            TKind::RBra => "']'",
            TKind::Colon => "':'",
            TKind::DoubleColon => "'::'",
            TKind::Comma => "','",
            TKind::RArrow => "'->'",
            TKind::Dot => "'.'",
            TKind::Hash => "'#'",
            TKind::Indent(_) => "indentation",
            TKind::Int(..) => "integer",
            TKind::Uint(..) => "unsigned integer",
            TKind::Float(..) => "float",
            TKind::Bool(_) => "boolean",
            TKind::Char(_) => "character",
            TKind::InvalidChar => "invalid character",
            TKind::String(_) => "string",
            TKind::Group => "group",
            TKind::UnknownCharacter(_) => "unknown character",
            TKind::Eof => "end of file",
            TKind::None => "nothing",
        })
    }
}

impl Default for TKind {
    fn default() -> Self {
        TKind::None
    }
}

#[derive(Debug, Clone, Default)]
pub struct LineData {
    pub line: usize,
    pub column: usize,
    pub file_name: Spam,
}

impl LineData {
    pub fn new(line: usize, column: usize, file_name: Spam) -> Self {
        Self {
            line,
            column,
            file_name,
        }
    }

    pub fn file_name(&self) -> &Spam {
        &self.file_name
    }
}

impl Display for LineData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}:{}", self.line, self.column, self.file_name.raw())
    }
}
