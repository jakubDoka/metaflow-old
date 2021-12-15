use crate::util::storage::IndexPointer;
use std::{
    fmt::{Debug, Display},
    ops::Range,
    rc::Rc,
};

use crate::util::storage::List;

type Result<T = Token> = std::result::Result<T, LError>;

#[derive(Debug)]
pub struct Lexer<'a> {
    source: &'a str,
    state: &'a mut LState,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str, state: &'a mut LState) -> Self {
        Lexer { source, state }
    }

    fn ident(&mut self) -> Result<Token> {
        let line_data = self.line_data();
        let start = self.state.progress;
        loop {
            let char = self.peek().unwrap_or('\0');
            if !char.is_alphanumeric() && char != '_' {
                break;
            }
            self.advance();
        }
        let end = self.state.progress;
        let value = self.sub(start..end);
        let kind = match &self.source[start..end] {
            "priv" => TKind::Priv,
            "pub" => TKind::Pub,
            "use" => TKind::Use,
            "fun" => TKind::Fun,
            "attr" => TKind::Attr,
            "pass" => TKind::Pass,
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
        Ok(Token::new(kind, value, line_data))
    }

    fn op(&mut self) -> Result<Token> {
        let line_data = self.line_data();
        let start = self.state.progress;
        while self.peek().unwrap_or('\0').is_operator() {
            self.advance();
        }
        let end = self.state.progress;
        let value = self.sub(start..end);
        let kind = match &self.source[start..end] {
            ":" => TKind::Colon,
            "::" => TKind::DoubleColon,
            "->" => TKind::RArrow,
            _ => TKind::Op,
        };
        Ok(Token::new(kind, value, line_data))
    }

    fn indent(&mut self) -> Result<Token> {
        let line_data = self.line_data();
        let start = self.state.progress;
        self.advance();
        let mut indentation = 0;
        loop {
            match self.peek() {
                Some(' ') => {
                    self.advance();
                }
                Some('\t') => {
                    self.advance();
                    indentation += 2;
                }
                Some('\r') => {
                    self.advance();
                }
                _ => break,
            }
        }
        let end = self.state.progress;
        let value = self.sub(start..end);
        Ok(Token::new(TKind::Indent(indentation / 2), value, line_data))
    }

    fn number(&mut self) -> Result {
        let start = self.state.progress;
        let line_data = self.line_data();
        let number = self.parse_number_err(10)?.0;
        let is_float = self.peek() == Some('.');
        let (fraction, exponent) = if is_float {
            self.advance();
            self.parse_number_err(10)?
        } else {
            (0, 0)
        };
        let next_char = self.peek().unwrap_or('\0');
        let kind = match next_char {
            'i' | 'u' | 'f' => {
                self.advance();
                let base = self.parse_number_err(10)?.0 as u16;
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
        let end = self.state.progress;
        let value = self.sub(start..end);
        Ok(Token::new(kind, value, line_data))
    }

    fn parse_number_err(&mut self, base: u64) -> Result<(u64, u64)> {
        let start = self.state.progress;
        self.parse_number(base).ok_or_else(|| {
            let line_data = self.line_data();
            let end = self.state.progress;
            let value = self.sub(start..end);
            LError::new(LEKind::InvalidCharacter, value, line_data)
        })
    }

    fn parse_number(&mut self, base: u64) -> Option<(u64, u64)> {
        let mut number = 0u64;
        let mut exponent = 1u64;
        let base32 = base as u32;
        loop {
            let ch = self.peek().unwrap_or('\0');
            if ch == '_' {
                self.advance();
                continue;
            }
            if !ch.is_numeric() {
                break Some((number, exponent));
            }
            number = number * base + self.advance().unwrap().to_digit(base32)? as u64;
            exponent *= base;
        }
    }

    fn char_or_label(&mut self) -> Result {
        let line_data = self.line_data();
        let start = self.state.progress;
        self.advance();
        let current = self.advance().unwrap_or('\0');

        let (char, may_be_label) = if current == '\\' {
            let start = self.state.progress;
            (
                match self.char_escape() {
                    Some(c) => c,
                    None => {
                        let end = self.state.progress;
                        return Err(LError::new(
                            LEKind::InvalidCharacter,
                            self.sub(start..end),
                            line_data,
                        ));
                    }
                },
                false,
            )
        } else {
            (current, true)
        };

        let next = self.peek().unwrap_or('\0');

        if !may_be_label && next != '\'' {
            return Err(LError::new(
                LEKind::UnclosedCharacter,
                self.sub(start..self.state.progress),
                line_data,
            ));
        }

        if next == '\'' {
            self.advance();
            let end = self.state.progress;
            let value = self.sub(start..end);
            Ok(Token::new(TKind::Char(char), value, line_data))
        } else {
            while self.peek().unwrap_or('\0').is_alphanumeric() {
                self.advance();
            }
            let end = self.state.progress;
            let value = self.sub(start..end);
            Ok(Token::new(TKind::Label, value, line_data))
        }
    }

    fn string(&mut self) -> Result<Token> {
        let line_data = self.line_data();
        let start = self.state.progress;
        self.advance();
        let mut string_data = vec![];
        loop {
            match self.peek() {
                Some('\\') => {
                    let start = self.state.progress;
                    match self.char_escape() {
                        Some(ch) => {
                            let len = string_data.len();
                            string_data.resize(len + ch.len_utf8(), 0);
                            ch.encode_utf8(&mut string_data[len..]);
                        }
                        None => {
                            let end = self.state.progress;
                            return Err(LError::new(
                                LEKind::InvalidCharacter,
                                self.sub(start..end),
                                line_data,
                            ));
                        }
                    }
                }
                Some('"') => {
                    self.advance();
                    break;
                }
                Some(_) => {
                    let ch = self.advance().unwrap();
                    let len = string_data.len();
                    string_data.resize(len + ch.len_utf8(), 0);
                    ch.encode_utf8(&mut string_data[len..]);
                }
                None => {
                    return Err(LError::new(
                        LEKind::UnclosedString,
                        self.sub(start..self.state.progress),
                        line_data,
                    ));
                }
            }
        }

        string_data.push(0);

        // note: we don't care if string has incorrect encoding
        let end = self.state.progress;
        let value = self.sub(start..end);
        Ok(Token::new(
            TKind::String(Rc::new(string_data)),
            value,
            line_data,
        ))
    }

    fn char_escape(&mut self) -> Option<char> {
        self.advance();
        let current = self.advance().unwrap_or('\0');
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
                    res = res * 8 + self.advance()?.to_digit(8)? as u8;
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
                    res = res * 16 + self.advance()?.to_digit(16)?;
                }
                return char::from_u32(res);
            }
            _ => return None,
        })
    }

    fn line_data(&self) -> LineData {
        LineData::new(self.state.line, self.column(), self.state.source)
    }

    pub fn peek(&self) -> Option<char> {
        self.source[self.state.progress..].chars().next()
    }

    pub fn peek_n(&self, n: usize) -> Option<char> {
        self.source[self.state.progress..].chars().nth(n)
    }

    #[inline]
    pub fn advance(&mut self) -> Option<char> {
        let char = self.peek();

        if let Some(ch) = char {
            if ch == '\n' {
                self.state.line += 1;
                self.state.last_n_line = self.state.progress;
            }
            self.state.progress += ch.len_utf8();
        }

        char
    }

    pub fn sub(&self, range: Range<usize>) -> Spam {
        Spam::new(self.state.source, range)
    }

    pub fn column(&self) -> usize {
        self.state.progress - self.state.last_n_line
    }

    pub fn next(&mut self) -> Result {
        let char = self.peek().unwrap_or('\0');
        if char.is_alphabetic() || char == '_' {
            return self.ident();
        }
        if char.is_operator() {
            return self.op();
        }
        if char.is_numeric() {
            return self.number();
        }

        let line_data = self.line_data();
        let start = self.state.progress;

        let kind = match char {
            '\n' => return self.indent(),
            ' ' | '\r' | '\t' => {
                while matches!(self.peek(), Some(' ' | '\t' | '\r')) {
                    self.advance();
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
            '\0' => TKind::Eof,
            _ => {
                return Err(LError::new(
                    LEKind::UnknownCharacter,
                    self.sub(start..start + 1),
                    line_data,
                ))
            }
        };

        self.advance();
        Ok(Token::new(kind, self.sub(start..start + 1), line_data))
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

#[derive(Default, Debug, Clone)]
pub struct LState {
    pub source: Source,
    pub progress: usize,
    pub line: usize,
    pub last_n_line: usize,
}

impl LState {
    pub fn new(source: Source) -> Self {
        Self {
            source,
            progress: 0,
            line: 1,
            last_n_line: 0,
        }
    }
}

pub struct LMainState {
    sources: List<Source, SourceEnt>,
    builtin_source: Source,
}

impl LMainState {
    pub fn new() -> Self {
        let mut sources = List::new();
        let builtin_source = sources.add(SourceEnt {
            name: String::from("builtin_spams.mf"),
            content: String::new(),
        });

        LMainState {
            sources,
            builtin_source,
        }
    }

    pub fn display(&self, spam: &Spam) -> &str {
        &self.sources[spam.source].content[spam.range.clone()]
    }

    pub fn join_spams_low(&self, spam: &mut Spam, other: &Spam, trim: bool) {
        debug_assert!(spam.source == other.source && spam.range.end <= other.range.start);

        spam.range.end = if trim {
            other.range.start
        } else {
            other.range.end
        };
    }

    pub fn builtin_spam(&mut self, name: &str) -> Spam {
        let builtin = &mut self.sources[self.builtin_source].content;
        let start = builtin.len();
        builtin.push_str(name);
        let end = builtin.len();
        Spam::new(self.builtin_source, start..end)
    }

    pub fn lexer_for<'a>(&'a self, state: &'a mut LState) -> Lexer<'a> {
        Lexer::new(self.sources[state.source].content.as_str(), state)
    }
}

crate::index_pointer!(Source);

#[derive(Debug, Clone, Default)]
pub struct SourceEnt {
    name: String,
    content: String,
}

#[derive(Debug, Clone, Default)]
pub struct Token {
    pub kind: TKind,
    pub spam: Spam,
    pub line_data: LineData,
}

impl Token {
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
    Fun,
    Attr,
    Pass,
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
    String(Rc<Vec<u8>>),

    Indent(usize),

    Group,

    Eof,
    None,
}

impl std::fmt::Display for TKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match *self {
            TKind::Priv => "'priv'",
            TKind::Pub => "'pub'",
            TKind::Use => "'use'",
            TKind::Fun => "'fun'",
            TKind::Attr => "'attr'",
            TKind::Pass => "'pass'",
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
            TKind::String(_) => "string",
            TKind::Group => "group",
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

pub struct TokenDisplay<'a> {
    pub state: &'a LMainState,
    pub token: &'a Token,
}

impl<'a> TokenDisplay<'a> {
    pub fn new(state: &'a LMainState, token: &'a Token) -> Self {
        TokenDisplay { state, token }
    }
}

impl std::fmt::Display for TokenDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.token.kind == TKind::None {
            write!(f, "|> no line information available")?;
            return Ok(());
        }

        let mut range = self.token.spam.range.clone();
        let string = &self.state.sources[self.token.spam.source].content;
        if string[range.start..range.end].starts_with("\n") {
            range.start += 1;
        }

        writeln!(
            f,
            "|> {}",
            LineDataDisplay::new(self.state, &self.token.line_data)
        )?;

        let end = string[range.end..]
            .find('\n')
            .map(|i| i + range.end)
            .unwrap_or(string.len());
        let start = string[..range.start]
            .rfind('\n')
            .map(|i| i + 1)
            .unwrap_or(0);

        for i in string[start..end].split('\n') {
            writeln!(f, "| {}", i)?;
        }

        let mut max = 0;
        let mut min = range.start - start;

        if let TKind::Indent(_) = self.token.kind {
            min = range.start - start;
            max = range.end - start - 1 * (range.end - start != 0) as usize;
        } else {
            let mut i = min;
            for ch in string[range.start..range.end].chars() {
                if ch.is_whitespace() {
                    if ch == '\n' {
                        i = 0;
                    }
                } else {
                    max = i.max(max);
                    min = i.min(min);
                }
                i += 1;
            }
        }

        write!(f, "| ")?;
        for _ in 0..min {
            write!(f, " ")?;
        }
        for _ in min..=max {
            write!(f, "^")?;
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct LError {
    pub kind: LEKind,
    pub spam: Spam,
    pub line_data: LineData,
}

impl LError {
    pub fn new(kind: LEKind, spam: Spam, line_data: LineData) -> Self {
        LError {
            kind,
            spam,
            line_data,
        }
    }
}

#[derive(Debug)]
pub enum LEKind {
    InvalidCharacter,
    UnknownCharacter,
    UnclosedCharacter,
    UnclosedString,
}

pub struct LineDataDisplay<'a> {
    state: &'a LMainState,
    data: &'a LineData,
}

impl<'a> LineDataDisplay<'a> {
    pub fn new(state: &'a LMainState, data: &'a LineData) -> Self {
        Self { state, data }
    }
}

impl Display for LineDataDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}:{}",
            self.data.line, self.data.column, self.state.sources[self.data.source].name
        )
    }
}

#[derive(Debug, Clone, Default)]
pub struct LineData {
    pub line: usize,
    pub column: usize,
    pub source: Source,
}

impl LineData {
    pub fn new(line: usize, column: usize, source: Source) -> Self {
        Self {
            line,
            column,
            source,
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Spam {
    pub source: Source,
    pub range: Range<usize>,
}

impl Spam {
    pub fn new(source: Source, range: Range<usize>) -> Self {
        Self { source, range }
    }
}

//#[cfg(feature = "testing")]
pub fn test() {
    let mut main_state = LMainState::new();
    let source_ent = SourceEnt {
        name: "text_code.mf".to_string(),
        content: crate::testing::TEST_CODE.to_string(),
    };
    let source = main_state.sources.add(source_ent);
    let mut state = LState::new(source);

    loop {
        let token = main_state.lexer_for(&mut state).next().unwrap();
        if token.kind == TKind::Eof {
            break;
        }
        println!("{}", TokenDisplay::new(&main_state, &token));
    }
}
