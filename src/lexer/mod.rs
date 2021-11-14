use std::{
    fmt::Debug,
    ops::{Deref, Range},
    rc::Rc,
    str::Chars,
};

pub struct Lexer {
    cursor: Cursor,
    file_name: Rc<String>,
}

impl Lexer {
    pub fn new(file_name: String, file: String) -> Lexer {
        let file = Rc::new(file);
        let file_name = Rc::new(file_name);
        Lexer {
            cursor: Cursor::new(StrRef::whole(&file)),
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
        let value = self.cursor.data.sub(start..end);
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
            "loop" => TKind::Loop,
            "break" => TKind::Break,
            "continue" => TKind::Continue,
            "max" => TKind::Op,
            "min" => TKind::Op,
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
        let value = self.cursor.data.sub(start..end);
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
        let value = self.cursor.data.sub(start..end);
        Some(Token::new(TKind::Indent(indentation / 2), value, line_data))
    }

    fn number(&mut self) -> Option<Token> {
        let mut number = 0u64;
        let start = self.cursor.progress();
        let line_data = self.line_data();
        while self.cursor.peek().unwrap_or('\0').is_numeric() {
            number = number * 10 + (self.cursor.advance().unwrap() as u64 - '0' as u64);
        }
        let next_char = self.cursor.peek().unwrap_or('\0');
        let kind = match next_char {
            'i' | 'u' => {
                self.cursor.advance();
                let mut base = 0u16;
                while self.cursor.peek().unwrap_or('\0').is_numeric() {
                    base = base * 10 + (self.cursor.advance().unwrap() as u16 - '0' as u16);
                }
                match next_char {
                    'i' => TKind::Int(number as i64, base),
                    'u' => TKind::Uint(number, base),
                    _ => unreachable!(),
                }
            }
            _ => TKind::Int(number as i64, 64),
        };
        let end = self.cursor.progress();
        let value = self.cursor.data.sub(start..end);
        Some(Token::new(kind, value, line_data))
    }

    fn char_or_label(&mut self) -> Option<Token> {
        let line_data = self.line_data();
        let start = self.cursor.progress();
        self.cursor.advance()?;
        let current = self.cursor.advance()?;

        let (char, may_be_label) = if current == '\\' {
            (self.char_escape()?, false)
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
            let value = self.cursor.data.sub(start..end);
            Some(Token::new(TKind::Char(char), value, line_data))
        } else {
            while self.cursor.peek().unwrap_or('\0').is_alphanumeric() {
                self.cursor.advance();
            }
            let end = self.cursor.progress();
            let value = self.cursor.data.sub(start..end);
            Some(Token::new(TKind::Label, value, line_data))
        }
    }

    fn char_escape(&mut self) -> Option<char> {
        self.cursor.advance();
        let current = self.cursor.advance().unwrap_or('\0');
        Some(match current {
            'a' | 'b' | 'e' | 'f' | 'n' | 'r' | 't' | 'v' | '\\' | '\'' | '"' => {
                match current {
                    'a' => '\x07',
                    'b' => '\x08',
                    'e' => '\x1b',
                    'f' => '\x0c',
                    'v' => '\x0b',
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    _ => current,
                }
            }
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
                // SAFETY: TODO: check that the value is valid
                unsafe { char::from_u32_unchecked(res) }
            }
            _ => return None,
        })
    }

    fn line_data(&self) -> LineData {
        LineData {
            file_name: StrRef::whole(&self.file_name),
            line: self.cursor.line,
            column: self.cursor.progress() - self.cursor.last_n_line,
        }
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
            self.cursor.data.sub(start..start + 1),
            line_data,
        ))
    }
}

struct Cursor {
    data: StrRef,
    chars: Chars<'static>,
    line: usize,
    last_n_line: usize,
}

impl Cursor {
    fn new(data: StrRef) -> Self {
        Cursor {
            //SAFETY: cursor disposes data only upon drop
            chars: unsafe { data.get_static_ref().chars() },
            data,
            line: 1,
            last_n_line: 0,
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }

    fn peek_n(&self, n: usize) -> Option<char> {
        self.chars.clone().nth(n)
    }

    fn progress(&self) -> usize {
        self.data.len() - self.chars.as_str().len()
    }

    #[inline]
    fn advance(&mut self) -> Option<char> {
        let char = self.chars.next();
        if char == Some('\n') {
            self.line += 1;
            self.last_n_line = self.progress();
        }
        char
    }
}

#[derive(Debug, Clone, Default)]
pub struct Token {
    pub kind: TKind,
    pub value: StrRef,
    pub line_data: LineData,
}

impl Token {
    pub fn builtin(value: &'static str) -> Self {
        Token {
            kind: TKind::Ident,
            value: StrRef::infinite(value),
            line_data: LineData::default(),
        }
    }

    pub fn new(kind: TKind, value: StrRef, line_data: LineData) -> Self {
        Token {
            kind,
            value,
            line_data,
        }
    }

    pub fn eof() -> Self {
        Token {
            kind: TKind::Eof,
            value: StrRef::empty(),
            line_data: LineData::default(),
        }
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {:?}", self.kind, self.value)?;
        Ok(())
    }
}

impl PartialEq<TKind> for Token {
    fn eq(&self, other: &TKind) -> bool {
        self.kind == *other
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TKind {
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
    Comma,
    RArrow,
    Hash,
    Dot,

    Int(i64, u16),
    Uint(u64, u16),
    Bool(bool),
    Char(char),

    Indent(usize),

    UnknownCharacter(char),
    Eof,
    None,
}

impl std::fmt::Display for TKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match *self {
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
            TKind::Label => "'label'",
            TKind::Ident => "identifier",
            TKind::Op => "operator",
            TKind::LPar => "'('",
            TKind::RPar => "')'",
            TKind::LCurly => "'{'",
            TKind::RCurly => "'}'",
            TKind::LBra => "'['",
            TKind::RBra => "']'",
            TKind::Colon => "':'",
            TKind::Comma => "','",
            TKind::RArrow => "'->'",
            TKind::Dot => "'.'",
            TKind::Hash => "'#'",
            TKind::Indent(_) => "indentation",
            TKind::Int(..) => "integer",
            TKind::Uint(..) => "unsigned integer",
            TKind::Bool(_) => "boolean",
            TKind::Char(_) => "character",
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
    pub file_name: StrRef,
}

#[derive(Clone, PartialEq)]
pub struct StrRef {
    rc: Option<Rc<String>>,
    string: *const str,
}

impl StrRef {
    pub fn new(rc: &Rc<String>, range: Range<usize>) -> Self {
        StrRef {
            rc: Some(rc.clone()),
            string: &rc[range] as *const str,
        }
    }

    pub fn whole(rc: &Rc<String>) -> Self {
        StrRef {
            rc: Some(rc.clone()),
            string: &rc[..] as *const str,
        }
    }

    pub fn infinite(str: &'static str) -> Self {
        StrRef {
            rc: None,
            string: str,
        }
    }

    pub fn empty() -> Self {
        StrRef {
            rc: None,
            string: "" as *const str,
        }
    }

    pub fn sub(&self, range: Range<usize>) -> Self {
        StrRef {
            rc: self.rc.clone(),
            string: &self[range] as *const str,
        }
    }

    unsafe fn get_static_ref(&self) -> &'static str {
        &*self.string as &'static str
    }
}

impl Default for StrRef {
    fn default() -> Self {
        StrRef::empty()
    }
}

impl Debug for StrRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.deref())
    }
}

impl Deref for StrRef {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        //SAFETY: instance holds ref-count to string
        unsafe { &*self.string }
    }
}

//SAFETY: instance holds ref-count to string
unsafe impl Send for StrRef {}

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
