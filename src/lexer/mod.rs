//! Module lexer defines lexing machinery. Structures are defined to not allocate
//! memory on the heap and just prepare markers referring to source code. [`Token`]
//! is designed to be as small as possible. Lexer it self is not meant to be stored
//! but construct whenever token is needed.
use quick_proc::{QuickDefault, QuickSer, RealQuickSer};

use cranelift::entity::EntityRef;

use crate::{
    entities::Source,
    util::{sdbm::ID, storage::Map},
};
use cranelift::entity::PrimaryMap;
use std::{fmt::Debug, ops::Range, time::SystemTime};

pub use line_data::LineData;
pub use span::Span;
pub use token::{Token, TokenDisplay};
pub use error::Error;
pub use state::State;
pub use sources::Sources;
pub use source_ent::SourceEnt;

type Result<T = Token> = std::result::Result<T, Error>;

/// Next token parses one token from `source` based of `state`.
pub fn next_token(source: &str, state: &mut State) -> Result {
    Lexer::new(source, state).next()
}

/// Lexer modifies [`LState`] and yields token. If you want to peek,
/// just pass clone of [`LState`] and discard it. Whitespace is ignored
/// except for newlines and continuos whitespace that follows it.
#[derive(Debug)]
pub struct Lexer<'a> {
    source: &'a str,
    state: &'a mut State,
}

impl<'a> Lexer<'a> {
    /// Create lexer from source and state. No modifications to state are performed.
    pub fn new(source: &'a str, state: &'a mut State) -> Self {
        Lexer { source, state }
    }

    /// Next parses next token, returning it and preparing state for next token.
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

            let start = self.progress();

            let kind = match char {
                '\n' => return self.indent(),
                ' ' | '\r' | '\t' => {
                    while matches!(self.peek(), Some(' ' | '\t' | '\r')) {
                        self.advance();
                    }
                    continue;
                }
                '\'' => return self.char_or_tag(),
                '"' => return self.string(),
                '#' => {
                    let comment = self.comment()?;
                    if comment.kind() == token::Kind::Comment(false) {
                        continue;
                    }
                    return Ok(comment);
                }
                ',' => token::Kind::Comma,
                '(' => token::Kind::LPar,
                ')' => token::Kind::RPar,
                '{' => token::Kind::LCurly,
                '}' => token::Kind::RCurly,
                '[' => token::Kind::LBra,
                ']' => token::Kind::RBra,
                '.' => token::Kind::Dot,
                '\0' => token::Kind::Eof,
                _ => return Err(self.error(error::Kind::UnknownCharacter, start..start + 1)),
            };

            self.advance();
            return Ok(self.token(kind, start));
        }
    }

    /// Parses identifier token, but can return keyword token or
    /// even operator for some reserved words.
    /// ```regex
    /// \b[a-zA-Z_][a-zA-Z0-9_]+\b
    /// ```
    fn ident(&mut self) -> Result<Token> {
        let start = self.progress();
        loop {
            let char = self.peek().unwrap_or('\0');
            if !char.is_alphanumeric() && char != '_' {
                break;
            }
            self.advance();
        }
        let kind = match &self.source[start..self.progress()] {
            "priv" => token::Kind::Priv,
            "pub" => token::Kind::Pub,
            "use" => token::Kind::Use,
            "fun" => token::Kind::Fun,
            "attr" => token::Kind::Attr,
            "pass" => token::Kind::Pass,
            "return" => token::Kind::Return,
            "if" => token::Kind::If,
            "elif" => token::Kind::Elif,
            "else" => token::Kind::Else,
            "let" => token::Kind::Let,
            "var" => token::Kind::Var,
            "for" => token::Kind::For,
            "break" => token::Kind::Break,
            "continue" => token::Kind::Continue,
            "struct" => token::Kind::Struct,
            "embed" => token::Kind::Embed,
            "impl" => token::Kind::Impl,
            "enum" => token::Kind::Enum,
            "union" => token::Kind::Union,
            "max" | "min" | "as" | "abs" => token::Kind::Op,
            "true" => token::Kind::Bool(true),
            "false" => token::Kind::Bool(false),
            _ => token::Kind::Ident,
        };
        Ok(self.token(kind, start))
    }

    /// Parses operator token but can return keyword token.
    /// ```regex
    /// \b[+-*/%^=<>!&|?|:~]+\b
    /// ```
    fn op(&mut self) -> Result<Token> {
        let start = self.progress();
        while self.peek().unwrap_or('\0').is_operator() {
            self.advance();
        }
        let kind = match &self.source[start..self.progress()] {
            ":" => token::Kind::Colon,
            "::" => token::Kind::DoubleColon,
            "->" => token::Kind::RArrow,
            _ => token::Kind::Op,
        };
        Ok(self.token(kind, start))
    }

    /// Indent parses indent token, all of the characters of ident are
    /// navigation and space characters. Indentation value of ' ' is 0.5 and
    /// '\t' is 1 and sum is floored.
    /// ```regex
    /// \n[ \t]*
    /// ```
    fn indent(&mut self) -> Result<Token> {
        let start = self.progress();
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
        Ok(self.token(token::Kind::Indent(indentation / 2), start))
    }

    /// Parses number token. Literals allow underscores,
    /// hex and bin literals are also supported. After the
    /// value, type can also be specified.
    /// ```regex
    /// ([0-9_]+([0-9_])?|0x[0-9a-fA-F_]+|0b[01_]+)((i|u|f)[0-9]{0, 2})?
    /// ```
    fn number(&mut self) -> Result {
        let start = self.progress();
        let number = self.parse_number_err(10)?.0;
        let (fraction, _, is_float) = match self.peek() {
            Some('.') => {
                self.advance();
                let (f, e) = self.parse_number_err(10)?;
                (f, e, true)
            }
            Some('x') if number == 0 => {
                self.advance();
                self.parse_number_err(16)?;
                (0, 0, false)
            }
            Some('b') if number == 0 => {
                self.advance();
                self.parse_number_err(2)?;
                (0, 0, false)
            }
            _ => (0, 0, false),
        };
        let next_char = self.peek().unwrap_or('\0');
        let kind = match next_char {
            'i' | 'u' | 'f' => {
                self.advance();
                let base = self.parse_number_err(10)?.0 as u16;
                match next_char {
                    'i' => token::Kind::Int(base),
                    'u' => token::Kind::Uint(base),
                    'f' => token::Kind::Float(base),
                    _ => unreachable!(),
                }
            }
            _ => {
                if fraction == 0 && !is_float {
                    token::Kind::Int(0)
                } else {
                    token::Kind::Float(64)
                }
            }
        };
        Ok(self.token(kind, start))
    }

    /// Calls [`Self::parse_number`] and maps None to error.
    fn parse_number_err(&mut self, base: u64) -> Result<(u64, u64)> {
        let start = self.progress();
        self.parse_number(base)
            .ok_or_else(|| self.error(error::Kind::InvalidCharacter, start..self.progress()))
    }

    /// Parses simple integer number with underscores. Second value is
    /// exponent of the number, which is closes power of 10
    /// smaller the first element.
    /// ```regex
    /// [0-9_]+
    /// ```
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

            let char = self.peek().map(|d| d.to_digit(base32)).flatten();
            if char.is_none() {
                return Some((number, exponent));
            }
            self.advance();

            number = number * base + char.unwrap() as u64;
            exponent *= base;
        }
    }

    /// Parses character or label. Character can be escaped. `<char_escape>` refers
    /// to [`Self::char_escape`].
    /// ```regex
    /// '(<char_escape>'|ident)
    /// ```
    fn char_or_tag(&mut self) -> Result {
        let start = self.progress();
        self.advance();
        let current = self.peek().unwrap_or('\0');

        let may_be_label = if current == '\\' {
            let start = self.progress();
            if self.char_escape().is_none() {
                let end = self.progress();
                return Err(self.error(error::Kind::InvalidCharacter, start..end));
            }
            false
        } else {
            self.advance();
            true
        };

        let next = self.peek().unwrap_or('\0');

        if !may_be_label && next != '\'' {
            return Err(self.error(error::Kind::UnclosedCharacter, start..self.progress()));
        }

        let kind = if next == '\'' {
            self.advance();
            token::Kind::Char
        } else {
            while self.peek().unwrap_or('\0').is_alphanumeric() {
                self.advance();
            }

            token::Kind::Tag
        };
        Ok(self.token(kind, start))
    }

    /// Parses comment token. As long as [`str::chars`] can iterate over the characters,
    /// commend content is valid.
    fn comment(&mut self) -> Result {
        let start = self.progress();
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

        Ok(self.token(token::Kind::Comment(is_doc), start))
    }

    /// Parses the string literal, literal can be on multiple lines.
    /// ```regex
    /// "([^"]|<char_escape>)*"
    /// ```
    fn string(&mut self) -> Result<Token> {
        let start = self.progress();
        self.advance();

        loop {
            match self.peek() {
                Some('\\') => {
                    let start = self.progress();
                    match self.char_escape() {
                        Some(_) => (),
                        None => {
                            let end = self.progress();
                            return Err(self.error(error::Kind::InvalidCharacter, start..end));
                        }
                    }
                }
                Some('"') => {
                    self.advance();
                    break;
                }
                Some(_) => {
                    self.advance().unwrap();
                }
                None => {
                    return Err(self.error(error::Kind::UnclosedString, start..self.progress()));
                }
            }
        }

        Ok(self.token(token::Kind::String, start))
    }

    /// Parses character whether it is escaped or not.
    /// ```regex
    /// ([^\\']|\\([ abefnrtv\\'"0]|[0-7]{3}|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|U[0-9a-fA-F]{8}))
    fn char_escape(&mut self) -> Option<char> {
        self.advance();
        let current = self.advance().unwrap_or('\0');
        Some(match current {
            'a' | 'b' | 'e' | 'f' | 'n' | 'r' | 't' | 'v' | '\\' | '\'' | '"' | '0' | ' ' => {
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
                    ' ' => ' ',
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

    /// Peeks a character
    fn peek(&self) -> Option<char> {
        self.source[self.progress()..].chars().next()
    }

    /// Advances the progress by one character and returns if any.
    fn advance(&mut self) -> Option<char> {
        let char = self.peek();

        if let Some(ch) = char {
            if ch == '\n' {
                self.state.newline();
            }
            self.state.advance(ch.len_utf8());
        }

        char
    }

    /// Error constructor utility.
    fn error(&self, kind: error::Kind, range: Range<usize>) -> Error {
        Error::new(kind, self.span(range), self.line_data())
    }

    /// Token constructor utility.
    fn token(&self, kind: token::Kind, start: usize) -> Token {
        Token::new(kind, self.span(start..self.progress()), self.line_data())
    }

    /// LineData constructor utility.
    fn line_data(&self) -> LineData {
        self.state.line_data()
    }

    /// Span constructor utility.
    fn span(&self, range: Range<usize>) -> Span {
        Span::new(self.state.source(), range)
    }

    /// Progress getter.
    fn progress(&self) -> usize {
        self.state.progress()
    }
}

impl IsOperator for char {
    fn to_char(&self) -> char {
        *self
    }
}

/// Trait provides method to determinate wether something is a operator character.
pub trait IsOperator {
    /// Returns char that is used for matching.
    fn to_char(&self) -> char;

    /// Returns true if the character is an operator.
    fn is_operator(&self) -> bool {
        matches!(
            self.to_char(),
            '+' | '-' | '*' | '/' | '%' | '^' | '=' | '<' | '>' | '!' | '&' | '|' | '?' | ':' | '~'
        )
    }
}

mod state {
    use super::*;

    /// State holds the current progress of the lexer. It is small 
    /// and fast to copy.
    #[derive(Default, Debug, Clone, Copy, RealQuickSer)]
    pub struct State {
        source: Source,
        progress: u32,
        line: u32,
        last_n_line: u32,
    }
    
    impl State {
        /// Creates a new state with source.
        pub fn new(source: Source) -> Self {
            Self {
                source,
                progress: 0,
                line: 1,
                last_n_line: 0,
            }
        }
    
        /// Returns line data corresponding to current position.
        pub fn line_data(&self) -> LineData {
            LineData::new(
                self.line as usize,
                (self.progress - self.last_n_line) as usize,
            )
        }
    
        /// Source getter.
        pub fn source(&self) -> Source {
            self.source
        }
    
        /// Progress getter.
        pub fn progress(&self) -> usize {
            self.progress as usize
        }
    
        /// Notifies the state that a newline has been encountered.
        pub fn newline(&mut self) {
            self.line += 1;
            self.last_n_line = self.progress;
        }
    
        /// Advances the progress by the given amount.
        pub fn advance(&mut self, amount: usize) {
            self.progress += amount as u32;
        }
    }
}


mod sources {
    use super::*;
    
    /// Struct manages builtin spans and sores file contents.
    /// Files are not serialized though and are should be cleared.
    #[derive(Debug, Clone, QuickSer)]
    pub struct Sources {
        sources: PrimaryMap<Source, SourceEnt>,
        builtin_source: Source,
        builtin_spans: Map<(u32, u32)>,
    }

    impl Sources {
        /// Constructor allocate builtin source to push spans.
        pub fn new() -> Self {
            let mut sources = PrimaryMap::new();
            let builtin_source = sources.push(SourceEnt::new(
                String::from("builtin_spans.mf"),
                String::new(),
                SystemTime::UNIX_EPOCH,
            ));

            Sources {
                sources,
                builtin_source,
                builtin_spans: Map::new(),
            }
        }

        /// Adds source to state and returns the.
        pub fn add_source(&mut self, source: SourceEnt) -> Source {
            self.sources.push(source)
        }

        /// Returns string that token points to.
        pub fn display_token(&self, token: Token) -> &str {
            self.display(token.span())
        }

        /// Returns string that span points to.
        pub fn display(&self, span: Span) -> &str {
            &self.sources[span.source()].display(span.range())
        }

        /// Allocates builtin span and returns the reference.
        /// This method first looks for the span in the builtin
        /// source and returns already allocated one if possible.
        pub fn builtin_span(&mut self, name: &str) -> Span {
            let hash = ID::new(name);
            let builtin = &mut self.sources[self.builtin_source];
            let range = if let Some(&range) = self.builtin_spans.get(hash) {
                range.0 as usize..range.1 as usize
            } else {
                let start = builtin.size();
                builtin.push(name);
                let end = builtin.size();
                self.builtin_spans.insert(hash, (start as u32, end as u32));
                start..end
            };
            Span::new(self.builtin_source, range)
        }

        /// Calls [`next_token`], providing source string.
        pub fn token<'a>(&'a self, state: &'a mut State) -> Result<Token> {
            next_token(self.sources[state.source()].content(), state)
        }

        /// Frees the content of all sources. Should be called to 
        /// prepare sources for serialization.
        pub fn clear_sources(&mut self) {
            for (_, source) in self.sources.iter_mut() {
                source.clear();
            }
        }

        /// Source getter.
        pub fn source(&self, source: Source) -> &SourceEnt {
            &self.sources[source]
        }
    }

    impl Default for Sources {
        fn default() -> Self {
            Self::new()
        }
    }
}


mod source_ent {
    use super::*;

    /// Struct stores file related data. This ensures no string allocations are done
    /// and all structures can refer to source with [`Span`].
    #[derive(Debug, Clone, QuickDefault, QuickSer)]
    pub struct SourceEnt {
        name: String,
        content: String,
        #[default(SystemTime::UNIX_EPOCH)]
        modified: SystemTime,
    }
    
    impl SourceEnt {
        /// Because of private fields.
        pub fn new(name: String, content: String, modified: SystemTime) -> Self {
            SourceEnt {
                name,
                content,
                modified,
            }
        }
    
        /// Updates the content and modified time.
        pub fn modify(&mut self, content: String, modified: SystemTime) {
            self.content = content;
            self.modified = modified;
        }
    
        /// Updates the content.
        pub fn reload(&mut self, content: String) {
            self.content = content;
        }
    
        /// Returns the name/path of/to file.
        pub fn name(&self) -> &str {
            &self.name
        }
    
        /// Returns the content of the file.
        pub fn content(&self) -> &str {
            &self.content
        }
    
        /// Slices into content with range.
        pub fn display(&self, range: Range<usize>) -> &str {
            &self.content[range]
        }
    
        /// Returns the modified time of the file.
        pub fn modified(&self) -> SystemTime {
            self.modified
        }

        /// Pushes string to the end of content. Used for builtin source.
        pub fn push(&mut self, str: &str) {
            self.content.push_str(str);
        }

        /// Returns the size of content.
        pub fn size(&self) -> usize {
            self.content.len()
        }

        /// Clears the content.
        pub fn clear(&mut self) {
            self.content.clear()
        }
    }
}

/// Module provides namespace for token kind.
pub mod token {
    use super::*;

    /// Token is basic lex element that points to the sequence of source code.
    /// It preserves line information and span.
    #[derive(Debug, Clone, Copy, Default, RealQuickSer)]
    pub struct Token {
        kind: token::Kind,
        span: Span,
        line_data: LineData,
    }
    
    impl Token {
        /// Because of private fields.
        pub fn new(kind: token::Kind, span: Span, line_data: LineData) -> Self {
            Token {
                kind,
                span,
                line_data,
            }
        }
    
        /// Returns kind of the token.
        pub fn kind(&self) -> token::Kind {
            self.kind
        }
    
        /// Returns span of the token.
        pub fn span(&self) -> Span {
            self.span
        }
    
        /// Returns the source this token is from.
        pub fn source(&self) -> Source {
            self.span.source()
        }
    
        /// Returns range withing source code, this token points to.
        pub fn range(&self) -> Range<usize> {
            self.span.range()
        }
    
        /// Returns length of the string token points to.
        pub fn len(&self) -> usize {
            self.span.len()
        }
    
        /// Returns line_data of token
        pub fn line_data(&self) -> LineData {
            self.line_data
        }
    
        /// Returns line token is on.
        pub fn line(&self) -> usize {
            self.line_data.line()
        }
    
        /// returns column token is on.
        pub fn column(&self) -> usize {
            self.line_data.column()
        }
    
        /// Joins two tokens by making union of their spans.
        pub fn join(&self, other: Token) -> Token {
            self.join_low(other, false)
        }
    
        /// Joins two tokens by making union of their spans but not
        /// including content of `other`.
        pub fn join_trimmed(&self, other: Token) -> Token {
            self.join_low(other, true)
        }
    
        /// Joins two tokens by making union of their spans. If trim is true
        /// then content of `other` is not included.
        fn join_low(&self, other: Token, trim: bool) -> Token {
            Self::new(
                self.kind(),
                self.span().join(other.span(), trim),
                self.line_data(),
            )
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
    
    impl PartialEq<token::Kind> for Token {
        fn eq(&self, other: &token::Kind) -> bool {
            self.kind == *other
        }
    }
    
    /// Enum holds the kind of a token. It has size of 4 and it should stay that way.
    #[derive(Debug, Clone, Copy, PartialEq, RealQuickSer)]
    pub enum Kind {
        /// Keyword 'pub' indicates package exported items.
        Pub,
        /// Keyword 'priv' indicates file private items.
        Priv,
        /// Keyword 'use' indicates dependant modules as 
        /// a first statement in the file.
        Use,
        /// Keyword 'fun' indicates start of function 
        /// definition or function pointer type.
        Fun,
        /// Keyword 'attr' indicates attribute definition.
        Attr,
        /// Keyword 'pass' does nothing but makes 
        /// defining empty block possible.
        Pass,
        /// Keyword 'return' indicates return statement.
        Return,
        /// Keyword 'if' indicates if statement.
        If,
        /// Keyword 'elif' indicates chained branch 
        /// of if statement.
        Elif,
        /// Keyword 'else' indicates optional else 
        /// branch of if statement.
        Else,
        /// Keyword 'var' indicates mutable variable, 
        /// global state or pointer
        Var,
        /// Keyword 'let' indicates immutable variable
        /// or local state
        Let,
        /// Keyword 'for' indicates any loop.
        For,
        /// Keyword 'break' indicates break statement but also file break.
        Break,
        /// Keyword 'continue' indicates continue statement.
        Continue,
        /// Keyword 'struct' indicates struct declaration.
        Struct,
        /// Keyword 'embed' indicates embed field.
        Embed,
        /// Keyword 'impl' indicates block of type related items.
        Impl,
        /// Keyword 'enum' indicates enum declaration.
        Enum,
        /// Keyword 'union' indicates union declaration.
        Union,
    
        /// Anything matching [`Lexer::char_or_tag()`] regex.
        Tag,
        /// Anything matching [`Lexer::ident()`] regex.
        Ident,
        /// Anything matching [`Lexer::op()`] regex.
        Op,
    
        /// '('
        LPar,
        /// ')'
        RPar,
        /// '{'
        LCurly,
        /// '}'
        RCurly,
        /// '['
        LBra,
        /// ']'
        RBra,
        /// ':'
        Colon,
        /// '::'
        DoubleColon,
        /// ','
        Comma,
        /// '->'
        RArrow,
        /// '.'
        Dot,
    
        /// integer literal
        Int(u16),
        /// unsigned integer literal
        Uint(u16),
        /// float literal
        Float(u16),
        /// boolean literal
        Bool(bool),
        /// character literal
        Char,
        /// string literal
        String,
    
        /// Comment can be Documentation comment (true) or juts ignored comment (false).
        Comment(bool),
        /// Everything that matches [`Lexer::indent()`] regex.
        Indent(u16),        
    
        /// End of file.
        Eof,
        /// Some Error.
        Error,
        /// Indicates default value. Used to check if token is present.
        None,
    }
    
    impl std::fmt::Display for token::Kind {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str(match *self {
                token::Kind::Priv => "'priv'",
                token::Kind::Pub => "'pub'",
                token::Kind::Use => "'use'",
                token::Kind::Fun => "'fun'",
                token::Kind::Attr => "'attr'",
                token::Kind::Pass => "'pass'",
                token::Kind::Return => "'return'",
                token::Kind::If => "'if'",
                token::Kind::Elif => "'elif'",
                token::Kind::Else => "'else'",
                token::Kind::Var => "'var'",
                token::Kind::Let => "'let'",
                token::Kind::For => "'for'",
                token::Kind::Break => "'break'",
                token::Kind::Continue => "'continue'",
                token::Kind::Struct => "'struct'",
                token::Kind::Embed => "'embed'",
                token::Kind::Tag => "'label'",
                token::Kind::Impl => "'impl'",
                token::Kind::Enum => "'enum'",
                token::Kind::Union => "'ident'",
    
                token::Kind::Ident => "ident",
                token::Kind::Op => "operator",
                token::Kind::LPar => "'('",
                token::Kind::RPar => "')'",
                token::Kind::LCurly => "'{'",
                token::Kind::RCurly => "'}'",
                token::Kind::LBra => "'['",
                token::Kind::RBra => "']'",
                token::Kind::Colon => "':'",
                token::Kind::DoubleColon => "'::'",
                token::Kind::Comma => "','",
                token::Kind::RArrow => "'->'",
                token::Kind::Dot => "'.'",
                token::Kind::Indent(_) => "indentation",
                token::Kind::Comment(_) => "comment",
                token::Kind::Int(..) => "integer",
                token::Kind::Uint(..) => "unsigned integer",
                token::Kind::Float(..) => "float",
                token::Kind::Bool(_) => "boolean",
                token::Kind::Char => "character",
                token::Kind::String => "string",
                token::Kind::Eof => "end of file",
                token::Kind::None => "nothing",
                token::Kind::Error => "error",
            })
        }
    }
    
    impl Default for token::Kind {
        fn default() -> Self {
            token::Kind::None
        }
    }
    
    /// TokenDisplay can pretty print tokens.
    pub struct TokenDisplay<'a> {
        state: &'a Sources,
        token: &'a Token,
    }
    
    impl<'a> TokenDisplay<'a> {
        /// Because of private fields.
        pub fn new(state: &'a Sources, token: &'a Token) -> Self {
            TokenDisplay { state, token }
        }
    }
    
    impl std::fmt::Display for TokenDisplay<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if self.token.kind() == token::Kind::None {
                return Ok(());
            }
    
            let mut range = self.token  .range();
            let string = &self.state.source(self.token.source()).content();
            if string[range.start..range.end].starts_with("\n") {
                range.start += 1;
            }
    
            writeln!(
                f,
                "|> {}:{}:{}",
                self.state.source(self.token.source()).name(),
                self.token.line(),
                self.token.column()
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
    
            if let token::Kind::Indent(_) = self.token.kind {
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
}


/// Module offers name space for [`Kind`].
pub mod error {
    use super::*;

    impl ErrorDisplayState<Error> for Sources {
        fn fmt(&self, e: &Error, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match e.kind() {
                Kind::InvalidCharacter => {
                    write!(f, "invalid character literal")?;
                },
                Kind::UnknownCharacter => {
                    write!(f, "lexer does not recognize this character")?;
                },
                Kind::UnclosedCharacter => {
                    writeln!(f, "unclosed character literal")?;
                },
                Kind::UnclosedString => {
                    writeln!(f, "unclosed string literal")?;
                },
            }

            Ok(())
        }

        fn sources(&self) -> &Sources {
            self
        }
    }

    /// Error returned by lexer.
    #[derive(Debug)]
    pub struct Error {
        kind: Kind,
        token: Token,
    }

    impl Error {
        /// Because of private fields. (keeping encapsulation)
        pub fn new(kind: Kind, span: Span, line_data: LineData) -> Self {
            Self {
                kind,
                token: Token::new(token::Kind::Error, span, line_data),
            }
        }

        /// Returns the kind of the error.
        pub fn kind(&self) -> Kind {
            self.kind
        }

        /// Returns the token that caused the error.
        pub fn token(&self) -> Token {
            self.token
        }
    }

    impl DisplayError for Error {
        fn token(&self) -> Token {
            self.token
        }
    }

    /// Kind of error that was encountered.
    #[derive(Debug, Clone, Copy)]
    pub enum Kind {
        /// Invalid character literal.
        InvalidCharacter,
        /// Unknown character.
        UnknownCharacter,
        /// Unclosed character literal.
        UnclosedCharacter,
        /// Unclosed string literal.
        UnclosedString,
    }
}


mod span {
    use super::*;

    /// Span points to a string inside a source file.
    #[derive(Debug, Clone, Copy, QuickDefault, PartialEq, Eq, RealQuickSer)]
    pub struct Span {
        #[default(Source::new(0))]
        source: Source,
        start: u32,
        end: u32,
    }
    
    impl Span {
        /// Because of private fields.
        pub fn new(source: Source, range: Range<usize>) -> Self {
            Self {
                source,
                start: range.start as u32,
                end: range.end as u32,
            }
        }
    
        /// performs slicing operation on the span.
        pub fn slice(&self, range: Range<usize>) -> Span {
            Self {
                source: self.source,
                start: range.start as u32 + self.start,
                end: range.end as u32 + self.start,
            }
        }
    
        /// Returns source from where this span is.
        pub fn source(&self) -> Source {
            self.source
        }
    
        /// Returns length of string the span points to.
        pub fn len(&self) -> usize {
            (self.end - self.start) as usize
        }
    
        /// Returns range of string the span points to.
        pub fn range(&self) -> Range<usize> {
            self.start as usize..self.end as usize
        }
    
        /// Creates union of two spans, if trim is true, content of `other` is not included.
        pub fn join(&self, span: Span, trim: bool) -> Span {
            debug_assert!(self.source == span.source);
            Self {
                source: self.source,
                start: self.start.min(span.start),
                end: self.end.max(if trim { span.start } else { span.end }),
            }
        }
    }
}

mod line_data {
    use quick_proc::RealQuickSer;

    /// LineData holds information for the programmer. This could be calculated from the span, but
    /// it would take significant amount of time when working with large files and generating
    /// stack trace.
    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq, RealQuickSer)]
    pub struct LineData {
        line: u32,
        column: u32,
    }

    impl LineData {
        /// Because of private fields.
        pub fn new(line: usize, column: usize) -> Self {
            Self {
                line: line as u32,
                column: column as u32,
            }
        }

        /// Returns line number.
        pub fn line(&self) -> usize {
            self.line as usize
        }

        /// Returns column number.
        pub fn column(&self) -> usize {
            self.column as usize
        }
    }
}

/// Allows displaying errors based of error state.
pub struct ErrorDisplay<'a, E: DisplayError, S: ErrorDisplayState<E>> {
    state: &'a S,
    error: &'a E,
}

impl<'a, E: DisplayError, S: ErrorDisplayState<E>> ErrorDisplay<'a, E, S> {
    /// Because of private fields.
    pub fn new(state: &'a S, error: &'a E) -> Self {
        Self {
            state,
            error,
        }
    }
}

impl<'a, E: DisplayError, S: ErrorDisplayState<E>> std::fmt::Display for ErrorDisplay<'a, E, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let token = self.error.token();

        if token.kind() != token::Kind::None {
            write!(f, "{}", TokenDisplay::new(self.state.sources(), &token))?;
        }

        self.state.fmt(self.error, f)
    }
}

/// State that should display the error.
pub trait ErrorDisplayState<E: DisplayError> {
    /// Additional display after error token.
    fn fmt(&self, e: &E, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
    /// Sources provide data for displaying error token.
    fn sources(&self) -> &Sources;
}

/// Any error ctaht can ne displayed.
pub trait DisplayError {
    /// Getter of error token.
    fn token(&self) -> Token;
}

/// Module test.
pub fn test() {
    let mut main_state = Sources::new();
    let source_ent = SourceEnt::new(
        "text_code.mf".to_string(),
        include_str!("lexer_test.mf").to_string(),
        SystemTime::UNIX_EPOCH,
    );
    let source = main_state.add_source(source_ent);
    let mut state = State::new(source);

    loop {
        let token = main_state.token(&mut state).unwrap();
        if token.kind() == token::Kind::Eof {
            break;
        }
        println!("{}", TokenDisplay::new(&main_state, &token));
    }
}
