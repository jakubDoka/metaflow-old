use std::{fmt::Debug, ops::{Deref, Range}, str::Chars, sync::Arc};

pub struct Lexer {
    cursor: Cursor,
    file: Arc<String>,
    file_name: Arc<String>,
    last_n_line: usize,
    line: usize,
}

impl Lexer {
    pub fn new(file_name: String, file: String) -> Lexer {
        let file = Arc::new(file);
        let file_name = Arc::new(file_name);
        Lexer {
            cursor: Cursor::new(StrRef::whole(&file)),
            file,
            file_name,
            last_n_line: 0,
            line: 1,
        }
    }

    fn ident(&mut self) -> Option<Token> {
        let line_data = self.line_data();
        let start = self.cursor.progress();
        while self.cursor.peek().unwrap_or('\0').is_alphanumeric() {
            self.cursor.advance();
        }
        let end = self.cursor.progress();
        let value = self.cursor.data.sub(start..end);
        let kind = match value.deref() {
            "fun" => TKind::Fun,
            "pass" => TKind::Pass,
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
            _ => TKind::Op,
        };
        Some(Token::new(kind, value, line_data))
    }

    fn indent(&mut self) -> Option<Token> {
        let line_data = self.line_data();
        let start = self.cursor.progress();
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
                _ => {
                    self.cursor.advance();
                    break
                },
            }
        }
        let end = self.cursor.progress();
        let value = self.cursor.data.sub(start..end);
        Some(Token::new(TKind::Indent(indentation / 2), value, line_data))
    }

    fn line_data(&self) -> LineData {
        LineData {
            file_name: StrRef::whole(&self.file_name),
            line: self.line,
            column: self.cursor.progress() - self.last_n_line,
        }
    }
}

impl<'a> Iterator for Lexer {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        
        let char = self.cursor.peek()?;
        println!("{:?}", char);
        if char.is_alphabetic() {
            return self.ident();
        }
        if char.is_operator() {
            return self.op();
        }

        let kind = match char {
            '\n' => return self.indent(),
            ' ' => {
                while self.cursor.peek()?.is_whitespace() {
                    self.cursor.advance();
                }
                return self.next();
            }
            ':' => TKind::Colon,
            ',' => TKind::Comma,
            '(' => TKind::LPar,
            ')' => TKind::RPar,
            _ => todo!("error handling"),
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
}

impl Cursor {
    fn new(data: StrRef) -> Self {
        Cursor {
            //SAFETY: cursor disposes data only upon drop
            chars: unsafe { data.get_static_ref().chars() },
            data,
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
        self.chars.next()
    }
}

#[derive(Debug)]
pub struct Token {
    pub kind: TKind,
    pub value: StrRef,
    pub line_data: LineData,
}

impl Token {
    pub fn new(kind: TKind, value: StrRef, line_data: LineData) -> Self {
        Token {
            kind,
            value,
            line_data,
        }
    }
}

#[derive(Debug)]
pub enum TKind {
    Fun,
    Pass,

    Ident,
    Op,

    LPar,
    RPar,
    Colon,
    Comma,

    Indent(usize),
}

#[derive(Debug)]
pub struct LineData {
    pub line: usize,
    pub column: usize,
    pub file_name: StrRef,
}

#[derive(Clone)]
pub struct StrRef {
    rc: Arc<String>,
    string: *mut str,
}

impl StrRef {
    pub fn new(rc: &Arc<String>, range: Range<usize>) -> Self {
        StrRef {
            rc: rc.clone(),
            string: &rc[range] as *const str as *mut str,
        }
    }

    pub fn whole(rc: &Arc<String>) -> Self {
        StrRef {
            rc: rc.clone(),
            string: &rc[..] as *const str as *mut str,
        }
    }

    pub fn sub(&self, range: Range<usize>) -> Self {
        Self::new(&self.rc, range)
    }

    unsafe fn get_static_ref(&self) -> &'static str {
        &*self.string as &'static str
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
            '+' | '-' | '*' | '/' | '%' | '^' | '=' | '<' | '>' | '!' | '&' | '|' | '?' | ':'
        )
    }
}

pub trait IsOperator {
    fn is_operator(&self) -> bool;
}

//#[cfg(feature = "testing")]
pub fn test() {
    let text_1 = r#"
fn main: pass

fn main(): pass

fn main(a: i8, b: i8): pass

fn main: 
    pass
    "#
    .to_string();

    let mut lexer = Lexer::new("text_1.pmh".to_string(), text_1);

    lexer.for_each(|token| println!("{:?}", token));
}
