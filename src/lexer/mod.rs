use meta_ser::{CustomDefault, MetaSer, MetaQuickSer};
use traits::MetaQuickSer;

use crate::util::{
    sdbm::ID,
    storage::{IndexPointer, Map},
};
use std::{
    fmt::{Debug, Display},
    time::SystemTime,
};

use crate::util::storage::List;

type Result<T = Token> = std::result::Result<T, LError>;

#[derive(Debug)]
pub struct Lexer<'a> {
    source: &'a str,
    state: &'a mut LState,
    main_state: &'a mut LMainState,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str, state: &'a mut LState, main_state: &'a mut LMainState) -> Self {
        Lexer {
            source,
            state,
            main_state,
        }
    }

    fn ident(&mut self) -> Result<Token> {
        let start = self.state.progress;
        loop {
            let char = self.peek().unwrap_or('\0');
            if !char.is_alphanumeric() && char != '_' {
                break;
            }
            self.advance();
        }
        let end = self.state.progress;
        let value = self.span(start, end);
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
            "impl" => TKind::Impl,
            "max" | "min" | "as" | "abs" => TKind::Op,
            "true" => TKind::Bool(true),
            "false" => TKind::Bool(false),
            _ => TKind::Ident,
        };
        Ok(Token::new(kind, value))
    }

    fn op(&mut self) -> Result<Token> {
        let start = self.state.progress;
        while self.peek().unwrap_or('\0').is_operator() {
            self.advance();
        }
        let end = self.state.progress;
        let value = self.span(start, end);
        let kind = match &self.source[start..end] {
            ":" => TKind::Colon,
            "::" => TKind::DoubleColon,
            "->" => TKind::RArrow,
            _ => TKind::Op,
        };
        Ok(Token::new(kind, value))
    }

    fn indent(&mut self) -> Result<Token> {
        let start = self.state.progress;
        self.advance();
        let mut indentation = 0;
        loop {
            match self.peek() {
                Some(' ') => {
                    self.advance();
                    indentation += 1;
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
        let value = self.span(start, end);
        Ok(Token::new(TKind::Indent(indentation / 2), value))
    }

    fn number(&mut self) -> Result {
        let start = self.state.progress;
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
        let value = self.span(start, end);
        Ok(Token::new(kind, value))
    }

    fn parse_number_err(&mut self, base: u64) -> Result<(u64, u64)> {
        let start = self.state.progress;
        self.parse_number(base).ok_or_else(|| {
            let end = self.state.progress;
            let value = self.span(start, end);
            LError::new(LEKind::InvalidCharacter, value)
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
        let start = self.state.progress;
        self.advance();
        let current = self.peek().unwrap_or('\0');

        let (char, may_be_label) = if current == '\\' {
            let start = self.state.progress;
            (
                match self.char_escape() {
                    Some(c) => c,
                    None => {
                        let end = self.state.progress;
                        return Err(LError::new(LEKind::InvalidCharacter, self.span(start, end)));
                    }
                },
                false,
            )
        } else {
            self.advance();
            (current, true)
        };

        let next = self.peek().unwrap_or('\0');

        if !may_be_label && next != '\'' {
            return Err(LError::new(
                LEKind::UnclosedCharacter,
                self.span(start, self.state.progress),
            ));
        }

        if next == '\'' {
            self.advance();
            let end = self.state.progress;
            let value = self.span(start, end);
            Ok(Token::new(TKind::Char(char), value))
        } else {
            while self.peek().unwrap_or('\0').is_alphanumeric() {
                self.advance();
            }
            let end = self.state.progress;
            let value = self.span(start, end);
            Ok(Token::new(TKind::Label, value))
        }
    }

    fn comment(&mut self) -> Result {
        let start = self.state.progress;
        self.advance();
        let is_doc = self.peek() == Some('#');
        if is_doc {
            self.advance();
        }

        if self.peek() == Some('[') {
            let mut depth = 0;
            loop {
                match self.peek() {
                    Some(']') => {
                        self.advance();
                        if self.peek() == Some('#') {
                            self.advance();
                            if depth == 0 {
                                break;
                            }
                            depth -= 1;
                        }
                    }
                    Some('#') => {
                        self.advance();
                        if self.peek() == Some('[') {
                            self.advance();
                            depth += 1;
                        }
                    }
                    Some(_) => {
                        self.advance();
                    }
                    None => break,
                }
            }
        } else {
            loop {
                match self.peek() {
                    Some('\n') | None => break,
                    Some(_) => {
                        self.advance();
                    }
                }
            }
        }

        let end = self.state.progress;
        let value = self.span(start, end);

        Ok(Token::new(TKind::Comment(is_doc), value))
    }

    fn string(&mut self) -> Result<Token> {
        let start = self.state.progress;
        self.advance();
        let mut string_data = std::mem::take(&mut self.main_state.string_lit_buffer);
        string_data.clear();

        loop {
            match self.peek() {
                Some('\\') => {
                    let start = self.state.progress;
                    match self.char_escape() {
                        Some(ch) => {
                            string_data.push(ch);
                        }
                        None => {
                            let end = self.state.progress;
                            return Err(LError::new(
                                LEKind::InvalidCharacter,
                                self.span(start, end),
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
                    string_data.push(ch);
                }
                None => {
                    return Err(LError::new(
                        LEKind::UnclosedString,
                        self.span(start, self.state.progress),
                    ));
                }
            }
        }

        string_data.push('\x00');

        let span = self.main_state.builtin_span(&string_data);

        self.main_state.string_lit_buffer = string_data;

        // note: we don't care if string has incorrect encoding
        let end = self.state.progress;
        let value = self.span(start, end);
        Ok(Token::new(TKind::String(span), value))
    }

    fn char_escape(&mut self) -> Option<char> {
        self.advance();
        let current = self.advance().unwrap_or('\0');
        Some(match current {
            'a' | 'b' | 'e' | 'f' | 'n' | 'r' | 't' | 'v' | '\\' | '\'' | '"' | '0' => {
                match current {
                    'a' => '\x07',
                    'b' => '\x08',
                    'e' => '\x1b',
                    'f' => '\x0c',
                    'v' => '\x0b',
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    '0' => '\0',
                    _ => current,
                }
            }
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

    pub fn peek(&self) -> Option<char> {
        self.source[self.state.progress..].chars().next()
    }

    pub fn peek_n(&self, n: usize) -> Option<char> {
        self.source[self.state.progress..].chars().nth(n)
    }

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

    pub fn span(&self, start: usize, end: usize) -> Span {
        Span::new(
            self.state.source,
            ID::new(&self.source[start as usize..end as usize]),
            start as u32,
            end as u32,
            self.state.line as u32,
            end as u32 - self.state.last_n_line as u32,
        )
    }

    pub fn next(&mut self) -> Result {
        loop {
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

            let start = self.state.progress;

            let kind = match char {
                '\n' => return self.indent(),
                ' ' | '\r' | '\t' => {
                    while matches!(self.peek(), Some(' ' | '\t' | '\r')) {
                        self.advance();
                    }
                    continue;
                }
                '\'' => return self.char_or_label(),
                '"' => return self.string(),
                '#' => {
                    let comment = self.comment()?;
                    if comment.kind == TKind::Comment(false) {
                        continue;
                    }
                    return Ok(comment);
                }
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
                        self.span(start, start + 1),
                    ))
                }
            };

            self.advance();
            let end = self.state.progress;
            return Ok(Token::new(kind, self.span(start, end)));
        }
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

#[derive(Default, Debug, Clone, Copy, MetaQuickSer)]
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

#[derive(Debug, Clone, MetaSer)]
pub struct LMainState {
    pub sources: List<Source, SourceEnt>,
    pub builtin_source: Source,
    pub builtin_spans: Map<Range>,
    pub string_lit_buffer: String,
}

impl LMainState {
    pub fn new() -> Self {
        let mut sources = List::new();
        let builtin_source = sources.add(SourceEnt {
            name: String::from("builtin_spans.mf"),
            content: String::new(),
            ..Default::default()
        });

        LMainState {
            sources,
            builtin_source,
            string_lit_buffer: String::new(),
            builtin_spans: Map::new(),
        }
    }

    pub fn display(&self, span: &Span) -> &str {
        &self.sources[span.source].content[span.start as usize..span.end as usize]
    }

    pub fn join_spans(&self, span: &mut Span, other: &Span, trim: bool) {
        if span.end == other.end {
            return;
        }

        debug_assert!(
            span.source == other.source && span.end <= other.start,
            "{:?} {:?}",
            span,
            other,
        );

        let end = if trim { other.start } else { other.end } as usize;

        span.end = span.start
            + self.sources[span.source].content[span.start as usize..end]
                .trim_end()
                .len() as u32;
    }

    pub fn builtin_span(&mut self, name: &str) -> Span {
        let hash = ID::new(name);
        let builtin = &mut self.sources[self.builtin_source].content;
        let (start, end) = if let Some(&range) = self.builtin_spans.get(hash) {
            (range.0, range.1)
        } else {
            let start = builtin.len() as u32;
            builtin.push_str(name);
            let end = builtin.len() as u32;
            self.builtin_spans.insert(hash, Range(start, end));
            (start, end)
        };
        Span::new(self.builtin_source, hash, start, end, 0, 0)
    }

    pub fn slice_span(&self, span: &Span, start: usize, end: usize) -> Span {
        let new_range = span.start as usize + start..span.start as usize + end;
        let hash = ID::new(&self.sources[span.source].content[new_range.clone()]);
        Span::new(
            span.source,
            hash,
            new_range.start as u32,
            new_range.end as u32,
            span.line,
            span.column,
        )
    }

    pub fn lexer_for<'a>(&'a mut self, state: &'a mut LState) -> Lexer<'a> {
        Lexer::new(
            unsafe {
                std::mem::transmute::<&str, &str>(self.sources[state.source].content.as_str())
            },
            state,
            self,
        )
    }
}

impl Default for LMainState {
    fn default() -> Self {
        Self::new()
    }
}

crate::index_pointer!(Source);

#[derive(Debug, Clone, CustomDefault, MetaSer)]
pub struct SourceEnt {
    pub name: String,
    pub content: String,
    #[default(SystemTime::UNIX_EPOCH)]
    pub modified: SystemTime,
}

#[derive(Debug, Clone, Copy, Default, MetaQuickSer)]
pub struct Token {
    pub kind: TKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TKind, span: Span) -> Self {
        Token { kind, span }
    }

    pub fn eof() -> Self {
        Token {
            kind: TKind::Eof,
            span: Span::default(),
        }
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {:?}", self.kind, self.span)?;
        Ok(())
    }
}

impl PartialEq<Token> for Token {
    fn eq(&self, other: &Token) -> bool {
        self.kind == other.kind && self.span == other.span
    }
}

impl PartialEq<TKind> for Token {
    fn eq(&self, other: &TKind) -> bool {
        self.kind == *other
    }
}

#[derive(Debug, Clone, Copy, PartialEq, MetaQuickSer)]
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
    Impl,

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
    Dot,

    Int(i64, u16),
    Uint(u64, u16),
    Float(f64, u16),
    Bool(bool),
    Char(char),
    String(Span),

    Comment(bool),
    Indent(usize),

    Group,

    Eof,
    Error,
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
            TKind::Impl => "'impl'",
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
            TKind::Indent(_) => "indentation",
            TKind::Comment(_) => "comment",
            TKind::Int(..) => "integer",
            TKind::Uint(..) => "unsigned integer",
            TKind::Float(..) => "float",
            TKind::Bool(_) => "boolean",
            TKind::Char(_) => "character",
            TKind::String(_) => "string",
            TKind::Group => "group",
            TKind::Eof => "end of file",
            TKind::None => "nothing",
            TKind::Error => "error",
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
            return Ok(());
        }

        let mut range = self.token.span.start as usize..self.token.span.end as usize;
        let string = &self.state.sources[self.token.span.source].content;
        if string[range.start..range.end].starts_with("\n") {
            range.start += 1;
        }

        writeln!(f, "|> {}", SpanDisplay::new(self.state, &self.token.span))?;

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
            max = range.end - start - 1 * (range.end - start != 0) as usize;
        } else {
            let mut i = min;
            for ch in string[range.start..range.end].chars() {
                if ch.is_whitespace() {
                    if ch == '\n' {
                        i = 0;
                    }
                    if ch != ' ' {
                        continue;
                    }
                }

                max = i.max(max);
                min = i.min(min);
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

crate::def_displayer!(
    LErrorDisplay,
    LMainState,
    LError,
    |self, f| {
        LEKind::InvalidCharacter => {
            write!(f, "invalid character literal")?;
        },
        LEKind::UnknownCharacter => {
            write!(f, "lexer does not recognize this character")?;
        },
        LEKind::UnclosedCharacter => {
            writeln!(f, "unclosed character literal")?;
        },
        LEKind::UnclosedString => {
            writeln!(f, "unclosed string literal")?;
        },
    }
);

#[derive(Debug)]
pub struct LError {
    pub kind: LEKind,
    pub token: Token,
}

impl LError {
    pub fn new(kind: LEKind, span: Span) -> Self {
        Self {
            kind,
            token: Token {
                kind: TKind::Error,
                span: span,
            },
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

pub struct SpanDisplay<'a> {
    state: &'a LMainState,
    data: &'a Span,
}

impl<'a> SpanDisplay<'a> {
    pub fn new(state: &'a LMainState, data: &'a Span) -> Self {
        Self { state, data }
    }
}

impl Display for SpanDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}:{}",
            self.data.line, self.data.column, self.state.sources[self.data.source].name
        )
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, MetaQuickSer)]
pub struct Span {
    pub source: Source,
    pub hash: ID,
    pub start: u32,
    pub end: u32,
    pub line: u32,
    pub column: u32,
}

impl Span {
    pub fn new(source: Source, hash: ID, start: u32, end: u32, line: u32, column: u32) -> Self {
        Self {
            source,
            start,
            end,
            hash,
            line,
            column,
        }
    }

    pub fn len(&self) -> usize {
        (self.end - self.start) as usize
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, MetaQuickSer)]
pub struct Range(u32, u32);

pub fn test() {
    let mut main_state = LMainState::new();
    let source_ent = SourceEnt {
        name: "text_code.mf".to_string(),
        content: crate::testing::TEST_CODE.to_string(),
        ..Default::default()
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
