//! Parser for the Mirage language.

use super::ast::{self, Ast, AstBuilder, AstKind, Position, Type};
use crate::collections::nonemptyvec::NonEmptyVec;
use std::{borrow::Cow, collections::HashSet, fmt};

#[derive(Debug)]
pub struct Error {
    context: String,
    position: Position,
    msg: Cow<'static, str>,
    source: Option<Box<dyn std::error::Error + 'static>>,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}:{}:{}",
            self.context, self.position.row, self.position.column, self.msg
        )
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.source.as_ref().map(Box::as_ref)
    }
}

type Result<T> = std::result::Result<T, Error>;

/// Predicate for characters that can start names.
fn can_start_name(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

/// Predicate for characters that make up names.
fn is_name_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Predicate for characters that make up operator symbols.
fn is_oper_char(c: char) -> bool {
    "=+-*/<>$".contains(c)
}

/// Predicate for delimiter characters
fn is_delimiter(c: char) -> bool {
    c.is_whitespace() || is_oper_char(c) || "(),;:".contains(c)
}

/// Language tokens
#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Arrow,
    Backslash,
    Bool(bool),
    Colon,
    Comma,
    Else,
    End,
    Equals,
    Ident(String),
    Int(i64),
    If,
    In,
    Infix,
    Infixl,
    Infixr,
    LParen,
    Let,
    Letrec,
    Op(String),
    Pound,
    RParen,
    SemiColon,
    Then,
    ThickArrow,
    Unit,
}

impl Token {
    /// Predicate for tokens that can start atomic terms.
    fn starts_atom(&self) -> bool {
        matches!(
            self,
            Token::Bool(_)
                | Token::Ident(_)
                | Token::Int(_)
                | Token::LParen
                | Token::Pound
                | Token::Unit
        )
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Arrow => write!(f, "'->'"),
            Token::Backslash => write!(f, "'\\'"),
            Token::Bool(b) => write!(f, "boolean '{b}'"),
            Token::Colon => write!(f, "':'"),
            Token::Comma => write!(f, "','"),
            Token::Else => write!(f, "keyword 'else'"),
            Token::End => write!(f, "end of input"),
            Token::Equals => write!(f, "'='"),
            Token::Ident(i) => write!(f, "identifier '{i}'"),
            Token::Int(i) => write!(f, "integer '{i}'"),
            Token::If => write!(f, "keyword 'if'"),
            Token::In => write!(f, "keyword 'in'"),
            Token::Infix => write!(f, "keyword 'infix'"),
            Token::Infixl => write!(f, "keyword 'infixl'"),
            Token::Infixr => write!(f, "keyword 'infixr'"),
            Token::Let => write!(f, "keyword 'let'"),
            Token::Letrec => write!(f, "keyword 'letrec'"),
            Token::LParen => write!(f, "'('"),
            Token::Op(o) => write!(f, "operator '{o}'"),
            Token::Pound => write!(f, "'#'"),
            Token::RParen => write!(f, "')'"),
            Token::SemiColon => write!(f, "';'"),
            Token::Then => write!(f, "keyword 'then'"),
            Token::ThickArrow => write!(f, "'=>'"),
            Token::Unit => write!(f, "'()'"),
        }
    }
}

/// Scans the input stream and returns tokens.
#[derive(Debug)]
struct Lexer<I: Iterator<Item = char>> {
    /// Stream of characters with lookahead
    input: std::iter::Peekable<I>,

    /// Context, like file name or REPL
    context: String,

    /// Current position in the input.
    position: Position,
}

impl<I: Iterator<Item = char>> Lexer<I> {
    /// Creates a new Lexer from an iterator over characters.
    fn new(input: I, context: String) -> Lexer<I> {
        Lexer {
            input: input.peekable(),
            context,
            position: Position { column: 0, row: 1 },
        }
    }

    fn err<S: Into<Cow<'static, str>>>(&self, msg: S) -> Error {
        Error {
            context: self.context.clone(),
            position: self.position,
            msg: msg.into(),
            source: None,
        }
    }

    fn next(&mut self) -> Option<char> {
        let oc = self.input.next();
        if let Some(c) = oc {
            if c == '\n' {
                self.position.column = 0;
                self.position.row += 1;
            } else {
                self.position.column += 1;
            };
            Some(c)
        } else {
            None
        }
    }

    /// Consumes all chars until the end of the line
    fn consume_line(&mut self) {
        while let Some(c) = self.next() {
            if c == '\n' {
                break;
            }
        }
    }

    /// Reads a name from the input.
    ///
    /// Names can be either keywords or identifiers.
    fn read_name(&mut self) -> Result<String> {
        let mut res = String::new();

        loop {
            match self.input.peek() {
                Some(&c) if !is_delimiter(c) => {
                    self.next();
                    res.push(c);
                }
                _ => break,
            }
        }

        if res.chars().skip(1).all(is_name_char) {
            Ok(res)
        } else {
            Err(self.err(format!("cannot parse {res} as a name")))
        }
    }

    /// Reads an integer from the input.
    fn read_integer(&mut self, first: char) -> Result<i64> {
        let mut s = String::new();
        s.push(first);

        loop {
            match self.input.peek() {
                Some(&c) if !is_delimiter(c) => {
                    self.next();
                    s.push(c);
                }
                _ => break,
            }
        }

        s.parse()
            .map_err(|err| self.err(format!("cannot parse {s} as integer: {err}")))
    }

    fn read_operator(&mut self, first: char) -> String {
        let mut res = String::new();
        res.push(first);

        loop {
            match self.input.peek() {
                Some(&c) if is_oper_char(c) => {
                    self.next();
                    res.push(c);
                }
                _ => break res,
            }
        }
    }

    /// Consumes whitespace
    fn whitespace(&mut self) {
        loop {
            match self.input.peek() {
                Some(c) if c.is_whitespace() => {
                    self.next();
                }
                _ => break,
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn next_token(&mut self) -> Result<Token> {
        while let Some(&x) = self.input.peek() {
            match x {
                '*' => {
                    self.next();
                    let o = self.read_operator('*');
                    return Ok(Token::Op(o));
                }
                '+' => {
                    self.next();
                    let o = self.read_operator('+');
                    return Ok(Token::Op(o));
                }
                '-' => {
                    self.next();
                    match self.input.peek() {
                        Some('-') => {
                            self.consume_line();
                        }
                        Some('>') => {
                            self.next();
                            return Ok(Token::Arrow);
                        }
                        Some(c) if c.is_ascii_digit() => {
                            let i = self.read_integer('-')?;
                            return Ok(Token::Int(i));
                        }
                        _ => {
                            let op = self.read_operator('-');
                            return Ok(Token::Op(op));
                        }
                    }
                }
                '/' => {
                    self.next();
                    let o = self.read_operator('/');
                    return Ok(Token::Op(o));
                }
                '\\' => {
                    self.next();
                    return Ok(Token::Backslash);
                }
                ':' => {
                    self.next();
                    return Ok(Token::Colon);
                }
                ',' => {
                    self.next();
                    return Ok(Token::Comma);
                }
                '=' => {
                    self.next();
                    match self.input.peek() {
                        Some('>') => {
                            self.next();
                            return Ok(Token::ThickArrow);
                        }
                        Some(c) if c.is_whitespace() => return Ok(Token::Equals),
                        _ => {
                            let op = self.read_operator('=');
                            return Ok(Token::Op(op));
                        }
                    }
                }
                '(' => {
                    self.next();
                    if let Some(')') = self.input.peek() {
                        self.next();
                        return Ok(Token::Unit);
                    }
                    return Ok(Token::LParen);
                }
                '#' => {
                    self.next();
                    return Ok(Token::Pound);
                }
                ')' => {
                    self.next();
                    return Ok(Token::RParen);
                }
                ';' => {
                    self.next();
                    return Ok(Token::SemiColon);
                }
                '<' => {
                    self.next();
                    let o = self.read_operator('<');
                    return Ok(Token::Op(o));
                }
                '>' => {
                    self.next();
                    let o = self.read_operator('>');
                    return Ok(Token::Op(o));
                }
                c if c.is_ascii_digit() => {
                    self.next();
                    let i = self.read_integer(c)?;
                    return Ok(Token::Int(i));
                }
                c if c.is_whitespace() => self.whitespace(),
                c if can_start_name(c) => {
                    let tok = {
                        let ident = self.read_name()?;
                        match ident.as_str() {
                            "else" => Token::Else,
                            "false" => Token::Bool(false),
                            "if" => Token::If,
                            "in" => Token::In,
                            "infix" => Token::Infix,
                            "infixl" => Token::Infixl,
                            "infixr" => Token::Infixr,
                            "let" => Token::Let,
                            "letrec" => Token::Letrec,
                            "then" => Token::Then,
                            "true" => Token::Bool(true),
                            _ => Token::Ident(ident),
                        }
                    };
                    return Ok(tok);
                }
                c if is_oper_char(c) => {
                    self.next();
                    let op = self.read_operator(c);
                    return Ok(Token::Op(op));
                }
                c => return Err(self.err(format!("unrecognised character {c}"))),
            }
        }

        Ok(Token::End)
    }
}

#[derive(Debug)]
pub(crate) struct Module {
    pub(crate) decls: Vec<(NonEmptyVec<String>, Ast)>,
}

impl Module {
    pub fn new() -> Self {
        Self { decls: Vec::new() }
    }
}

/// Operator associativity.
#[derive(Clone, Debug, Eq, PartialEq)]
enum OpAssoc {
    /// Left associativity.
    Left,

    /// No associativity.
    None,

    /// Right associativity.
    Right,
}

/// Information associated with an operator.
#[derive(Clone, Debug)]
struct OpInfo {
    /// Operator associativity.
    assoc: OpAssoc,

    /// Operator precedence.
    prec: u8,
}

#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub struct ParserCtx {
    /// Operator precedence and associativity table.
    table: Vec<(String, OpInfo)>,
}

impl ParserCtx {
    pub fn new() -> Self {
        ParserCtx { table: Vec::new() }
    }
}

#[derive(Debug)]
pub struct Parser<'ctx, I: Iterator<Item = char>> {
    /// Persistent parsing context.
    ctx: &'ctx mut ParserCtx,

    /// Look-ahead token in the input stream.
    la: Option<Token>,

    /// Current position in the input stream.
    position: Position,

    /// Stream of tokens coming from the lexer.
    tokens: Lexer<I>,
}

type Pattern = super::Pattern<String>;

/// Helper to facilitate creating parser errors.
macro_rules! parse_error {
    ($parser:ident, $($args:tt)+) => {
        $crate::lang::parser::Error {
            context: $parser.tokens.context.clone(),
            position: $parser.position,
            msg: match ::std::format_args!($($args)+) {
                args => if let Some(msg) = args.as_str() {
                    msg.into()
                } else {
                    ::std::fmt::format(args).into()
                }
            },
            source: None,
        }
    };
}

impl<'ctx, I: Iterator<Item = char>> Parser<'ctx, I> {
    pub fn new(ctx: &'ctx mut ParserCtx, input: I, input_ctx: String) -> Parser<'ctx, I> {
        Parser {
            ctx,
            la: None,
            position: Position { column: 0, row: 1 },
            tokens: Lexer::new(input, input_ctx),
        }
    }

    fn build_ast(&self, builder: AstBuilder) -> Result<Ast> {
        builder
            .with_context(&self.tokens.context)
            .build()
            .map_err(|err| Error {
                context: self.tokens.context.clone(),
                position: self.position,
                msg: "AST error".into(),
                source: Some(Box::new(err)),
            })
    }

    fn fill(&mut self) -> Result<()> {
        if self.la.is_none() {
            let tok = self.tokens.next_token()?;
            self.la.replace(tok);
        }

        Ok(())
    }

    fn next_token(&mut self) -> Result<Token> {
        self.fill()?;
        self.position = self.tokens.position;

        self.la
            .take()
            .ok_or_else(|| parse_error!(self, "premature end of input"))
    }

    fn peek_token(&mut self) -> Result<Token> {
        self.fill()?;

        self.la
            .as_ref()
            .cloned()
            .ok_or_else(|| parse_error!(self, "unexpected end of input"))
    }

    #[allow(clippy::needless_pass_by_value)]
    fn consume_token(&mut self, tok: Token) -> Result<()> {
        let t = self.next_token()?;
        if t == tok {
            Ok(())
        } else {
            Err(parse_error!(self, "expected {tok}, but got {t} instead",))
        }
    }

    fn consume_identifier(&mut self) -> Result<String> {
        let t = self.next_token()?;
        if let Token::Ident(i) = t {
            Ok(i)
        } else {
            Err(parse_error!(
                self,
                "identifier expected, but got {t} instead",
            ))
        }
    }

    fn consume_integer(&mut self) -> Result<i64> {
        let t = self.next_token()?;
        if let Token::Int(i) = t {
            Ok(i)
        } else {
            Err(parse_error!(self, "integer expected, but got {t} instead",))
        }
    }

    fn consume_operator(&mut self) -> Result<String> {
        let t = self.next_token()?;
        if let Token::Op(o) = t {
            Ok(o)
        } else {
            Err(parse_error!(self, "operator expected, but got {t} instead",))
        }
    }

    // if : IF term THEN term ELSE term
    fn parse_if(&mut self) -> Result<Ast> {
        let begin = self.position;
        self.consume_token(Token::If)?;
        let term1 = self.parse_term()?;
        self.consume_token(Token::Then)?;
        let term2 = self.parse_term()?;
        self.consume_token(Token::Else)?;
        let term3 = self.parse_term()?;
        let end = self.position;

        self.build_ast(ast::new_if(term1, term2, term3).with_span(begin, end))
    }

    // lambda : '\' ident (... ident)* '=>' term
    fn parse_lambda(&mut self) -> Result<Ast> {
        let begin = self.position;
        self.consume_token(Token::Backslash)?;
        let vars = self.parse_unique_identifiers()?;
        self.consume_token(Token::ThickArrow)?;
        let body = self.parse_term()?;
        let end = self.position;

        self.build_ast(ast::new_lambda(vars, body).with_span(begin, end))
    }

    // let : LET pattern (... ident)* = term IN term
    fn parse_let(&mut self) -> Result<Ast> {
        let begin = self.position;
        self.consume_token(Token::Let)?;
        let pat = self.parse_pattern()?;
        let tok = self.peek_token()?;
        match (pat, tok) {
            (Pattern::Var(var), Token::Ident(_)) => {
                // this is actually a lambda declaration
                let vars = self.parse_unique_identifiers()?;

                self.consume_token(Token::Equals)?;
                let expr = self.parse_term()?;
                let lam_end = self.position;

                self.consume_token(Token::In)?;
                let body = self.parse_term()?;
                let end = self.position;

                let lam = self.build_ast(ast::new_lambda(vars, expr).with_span(begin, lam_end))?;
                self.build_ast(ast::new_let(Pattern::Var(var), lam, body).with_span(begin, end))
            }
            (pat, _) => {
                self.consume_token(Token::Equals)?;
                let expr = self.parse_term()?;

                self.consume_token(Token::In)?;
                let body = self.parse_term()?;
                let end = self.position;

                self.build_ast(ast::new_let(pat, expr, body).with_span(begin, end))
            }
        }
    }

    // letrec : LETREC ident : type = term IN term
    fn parse_letrec(&mut self) -> Result<Ast> {
        let begin = self.position;
        self.consume_token(Token::Letrec)?;
        let var = self.consume_identifier()?;

        let vty = if let Token::Colon = self.peek_token()? {
            self.consume_token(Token::Colon)?;
            Some(self.parse_type()?)
        } else {
            None
        };

        self.consume_token(Token::Equals)?;
        let term1 = self.parse_term()?;
        self.consume_token(Token::In)?;
        let term2 = self.parse_term()?;
        let end = self.position;

        self.build_ast(ast::new_letrec(var, vty, term1, term2).with_span(begin, end))
    }

    // atom_seq : atom (atom ...)?
    fn parse_atom_seq(&mut self) -> Result<Ast> {
        let begin = self.position;
        let left = self.parse_atom()?;
        let mut tok = self.peek_token()?;
        if tok.starts_atom() {
            let a = self.parse_atom()?;
            let mut atoms = NonEmptyVec::new(a);
            tok = self.peek_token()?;
            while tok.starts_atom() {
                let a = self.parse_atom()?;
                atoms.push(a);
                tok = self.peek_token()?;
            }
            let end = self.position;

            self.build_ast(ast::new_app(left, atoms).with_span(begin, end))
        } else {
            Ok(left)
        }
    }

    // atom_expr : atom_seq ((oper atom_seq) ...)?
    //
    // the expression parser is based on the precedence climbing
    // technique, but instead of parsing a single atom for the lhs and
    // rhs we parse sequences of atoms to create the effect that
    // function application has the highest precedence of all
    fn parse_atom_expr(&mut self, min_prec: u8) -> Result<Ast> {
        let mut lhs = self.parse_atom_seq()?;

        while let Token::Op(op) = self.peek_token()? {
            let begin = self.position;
            let info = self
                .ctx
                .table
                .iter()
                .find(|(o, _)| *o == op)
                .map(|(_, i)| i.clone())
                .ok_or_else(|| parse_error!(self, "unknown operator {op} found",))?;

            if info.prec < min_prec {
                break;
            }

            let next_min_prec = if info.assoc == OpAssoc::Left {
                info.prec + 1
            } else {
                info.prec
            };

            self.consume_operator()?;

            let rhs = self.parse_atom_expr(next_min_prec)?;
            if let Ast {
                kind: AstKind::BinOp(ast::BinOp { oper: op2, .. }),
                ..
            } = &rhs
            {
                if op == *op2 && info.assoc == OpAssoc::None {
                    return Err(parse_error!(self, "operator {op2} is non-associative",));
                }
            }
            let end = self.position;

            lhs = self.build_ast(ast::new_binop(op, lhs, rhs).with_span(begin, end))?;
        }

        Ok(lhs)
    }

    // term : lambda
    //      | if
    //      | let
    //      | letrec
    //      | atom (atom...)?
    fn parse_term(&mut self) -> Result<Ast> {
        match self.peek_token()? {
            Token::Backslash => self.parse_lambda(),
            Token::If => self.parse_if(),
            Token::Let => self.parse_let(),
            Token::Letrec => self.parse_letrec(),
            tok if tok.starts_atom() => self.parse_atom_expr(0),
            tok => Err(parse_error!(self, "term expected, but got {tok} instead",)),
        }
    }

    //
    // atom : ident
    //      | unit
    //      | boolean
    //      | int
    //      | '(' term ')'
    //      | '(' term ',' term ',' term ... ')'
    //      | '#' int '(' term ')'
    #[allow(clippy::too_many_lines)]
    fn parse_atom(&mut self) -> Result<Ast> {
        match self.peek_token()? {
            Token::Bool(b) => {
                let begin = self.position;
                self.next_token()?;
                let end = self.position;

                self.build_ast(ast::new_bool(b).with_span(begin, end))
            }
            Token::Ident(ident) => {
                let begin = self.position;
                self.next_token()?;
                let end = self.position;

                if ident.starts_with('_') {
                    Err(parse_error!(
                        self,
                        "variable references starting with '_' are not allowed, but {ident} was found",
                    ))
                } else {
                    self.build_ast(ast::new_var(ident).with_span(begin, end))
                }
            }
            Token::LParen => {
                let begin = self.position;
                self.next_token()?;
                let fst = self.parse_term()?;
                let tok = self.peek_token()?;
                if tok == Token::RParen {
                    self.consume_token(Token::RParen)?;
                    Ok(fst)
                } else if tok == Token::Comma {
                    self.consume_token(Token::Comma)?;
                    let snd = self.parse_term()?;
                    let mut rest = Vec::new();
                    loop {
                        match self.peek_token()? {
                            Token::RParen => {
                                self.consume_token(Token::RParen)?;
                                let end = self.position;
                                return self.build_ast(
                                    ast::new_tuple(fst, snd, rest).with_span(begin, end),
                                );
                            }
                            Token::Comma => {
                                self.consume_token(Token::Comma)?;
                                let t = self.parse_term()?;
                                rest.push(t);
                            }
                            tok => {
                                return Err(parse_error!(
                                    self,
                                    "')' or ',' expected, but got {tok} instead",
                                ))
                            }
                        }
                    }
                } else {
                    Err(parse_error!(
                        self,
                        "')' or ',' expected, but got {tok} instead",
                    ))
                }
            }
            Token::Unit => {
                let begin = self.position;
                self.next_token()?;
                let end = self.position;

                self.build_ast(ast::new_unit().with_span(begin, end))
            }
            Token::Int(i) => {
                let begin = self.position;
                self.next_token()?;
                let end = self.position;

                self.build_ast(ast::new_int(i).with_span(begin, end))
            }
            Token::Pound => {
                let begin = self.position;
                self.next_token()?;
                let index = self.consume_integer()?;
                if index >= 0 {
                    self.consume_token(Token::LParen)?;
                    let tuple = self.parse_term()?;
                    self.consume_token(Token::RParen)?;
                    let end = self.position;

                    #[allow(clippy::cast_possible_truncation)]
                    #[allow(clippy::cast_sign_loss)]
                    self.build_ast(ast::new_tupleref(index as usize, tuple).with_span(begin, end))
                } else {
                    Err(parse_error!(
                        self,
                        "tuple accessor must be non-negative, but got {index} found",
                    ))
                }
            }
            tok => Err(parse_error!(
                self,
                "identifier, boolean, integer, '#' or '(' expected, but found {tok} instead",
            )),
        }
    }

    // type : () type'
    //      | ident type'
    //      | '(' type ',' type ',' type... ')' type'
    fn parse_type(&mut self) -> Result<Type> {
        match self.peek_token()? {
            Token::Unit => {
                self.consume_token(Token::Unit)?;
                self.parse_type_prime(Type::Unit)
            }
            Token::Ident(ident) => {
                self.next_token()?;
                self.parse_type_prime(Type::Ident(ident))
            }
            Token::LParen => {
                self.consume_token(Token::LParen)?;
                let fst = self.parse_type()?;
                self.consume_token(Token::Comma)?;
                let snd = self.parse_type()?;
                let mut rest = Vec::new();
                loop {
                    match self.peek_token()? {
                        Token::RParen => {
                            self.consume_token(Token::RParen)?;
                            let ty = Type::Tuple(Box::new(fst), Box::new(snd), rest);
                            return self.parse_type_prime(ty);
                        }
                        Token::Comma => {
                            self.consume_token(Token::Comma)?;
                            let ty = self.parse_type()?;
                            rest.push(ty);
                        }
                        tok => {
                            return Err(parse_error!(
                                self,
                                "')', or ',' expected, but got {tok} instead",
                            ))
                        }
                    }
                }
            }
            tok => Err(parse_error!(
                self,
                "(), identifier or tuple expected, but got {tok} instead",
            )),
        }
    }

    // type' : '->' type
    //       | ϵ
    fn parse_type_prime(&mut self, left: Type) -> Result<Type> {
        if self.peek_token()? == Token::Arrow {
            self.next_token()?;
            let right = self.parse_type()?;
            Ok(Type::Func(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    // fixdecl : infix|infixl|infixr op (, op...)? num
    fn parse_fixdecl(&mut self) -> Result<()> {
        let assoc = match self.next_token()? {
            Token::Infix => OpAssoc::None,
            Token::Infixl => OpAssoc::Left,
            Token::Infixr => OpAssoc::Right,
            _ => unreachable!(),
        };

        #[allow(clippy::cast_possible_truncation)]
        #[allow(clippy::cast_sign_loss)]
        let prec = {
            let i = self.consume_integer()?;
            if (0..=9).contains(&i) {
                10 * i as u8
            } else {
                return Err(parse_error!(
                    self,
                    "operator precedence must be between 0 and 9, but got {i} instead",
                ));
            }
        };

        let info = OpInfo { assoc, prec };

        loop {
            let op = self.consume_operator()?;
            if self.ctx.table.iter().any(|(o, _)| *o == op) {
                return Err(parse_error!(self, "operator {op} was already declared",));
            }
            self.ctx.table.push((op, info.clone()));

            if Token::Comma == self.peek_token()? {
                self.next_token()?;
            } else {
                break;
            }
        }

        Ok(())
    }

    // toplevel : (fixdecl ';' ...)? term
    pub(crate) fn parse(&mut self) -> Result<Ast> {
        let mut tok = self.peek_token()?;
        while tok == Token::Infix || tok == Token::Infixl || tok == Token::Infixr {
            self.parse_fixdecl()?;
            self.consume_token(Token::SemiColon)?;
            tok = self.peek_token()?;
        }

        self.parse_term()
    }

    pub(crate) fn parse_module(&mut self) -> Result<Module> {
        let mut module = Module::new();
        loop {
            let tok = self.peek_token()?;
            match tok {
                Token::Infix | Token::Infixl | Token::Infixr => {
                    self.parse_fixdecl()?;
                    self.consume_token(Token::SemiColon)?;
                }
                Token::Let => {
                    self.consume_token(Token::Let)?;
                    let idents = self.parse_unique_identifiers()?;
                    self.consume_token(Token::Equals)?;
                    let term = self.parse_term()?;
                    self.consume_token(Token::SemiColon)?;
                    module.decls.push((idents, term));
                }
                Token::End => break,
                _ => return Err(parse_error!(self, "Couldn't parse a module declaration",)),
            }
        }

        Ok(module)
    }

    // pattern: variable
    //        | '(' pattern ',' pattern ...')'
    fn parse_pattern(&mut self) -> Result<Pattern> {
        fn parse<J: Iterator<Item = char>>(
            ps: &mut Parser<'_, J>,
            seen: &mut HashSet<String>,
        ) -> Result<Pattern> {
            match ps.peek_token()? {
                Token::Ident(_) => {
                    let var = ps.consume_identifier()?;
                    if seen.contains(&var) {
                        Err(parse_error!(
                            ps,
                            "variable '{var}' appeared more than once in a pattern",
                        ))
                    } else {
                        seen.insert(var.clone());
                        Ok(Pattern::Var(var))
                    }
                }
                Token::LParen => {
                    ps.next_token()?;
                    let fst = parse(ps, seen)?;
                    ps.consume_token(Token::Comma)?;
                    let snd = parse(ps, seen)?;

                    let mut rest = Vec::new();
                    loop {
                        match ps.peek_token()? {
                            Token::Comma => {
                                ps.next_token()?;
                                let pat = parse(ps, seen)?;
                                rest.push(pat);
                            }
                            Token::RParen => {
                                ps.next_token()?;
                                break;
                            }
                            tok => {
                                return Err(parse_error!(
                                    ps,
                                    "unexpected token when reading tuple pattern: {tok}",
                                ))
                            }
                        }
                    }

                    Ok(Pattern::Tuple(Box::new(fst), Box::new(snd), rest))
                }
                tok => Err(parse_error!(ps, "pattern expected, got {tok} instead",)),
            }
        }

        parse(self, &mut HashSet::new())
    }

    fn parse_unique_identifiers(&mut self) -> Result<NonEmptyVec<String>> {
        let var = self.consume_identifier()?;
        let mut vars = NonEmptyVec::new(var);
        while let Token::Ident(ident) = self.peek_token()? {
            self.next_token()?;
            vars.push(ident);
        }

        // check that the identifiers are unique
        let mut vars_ = vars
            .iter()
            .filter(|v| *v != "_")
            .cloned()
            .collect::<Vec<_>>();
        vars_.sort_unstable();
        for w in vars_.windows(2) {
            if w[0] == w[1] {
                return Err(parse_error!(
                    self,
                    "Variable names must be unique but {} was given more than once",
                    w[0],
                ));
            }
        }

        Ok(vars)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lexer() {
        let input = r#"
           let _23all = -23 <**>5 >>= 9+ 8 / 7 - 99
           in let w0w = _23all < -48 <=>(888,false, -6583)
              in let f : Bool -> Bool = \x : Bool => if x == true then y2_y else zyu2ii
                 in f false;
        "#;
        let mut lexer = Lexer::new(input.chars(), "tests".to_string());
        assert_eq!(lexer.next_token().unwrap(), Token::Let);
        assert_eq!(
            lexer.next_token().unwrap(),
            Token::Ident("_23all".to_string())
        );
        assert_eq!(lexer.next_token().unwrap(), Token::Equals);
        assert_eq!(lexer.next_token().unwrap(), Token::Int(-23));
        assert_eq!(lexer.next_token().unwrap(), Token::Op("<**>".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::Int(5));
        assert_eq!(lexer.next_token().unwrap(), Token::Op(">>=".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::Int(9));
        assert_eq!(lexer.next_token().unwrap(), Token::Op("+".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::Int(8));
        assert_eq!(lexer.next_token().unwrap(), Token::Op("/".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::Int(7));
        assert_eq!(lexer.next_token().unwrap(), Token::Op("-".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::Int(99));
        assert_eq!(lexer.next_token().unwrap(), Token::In);
        assert_eq!(lexer.next_token().unwrap(), Token::Let);
        assert_eq!(lexer.next_token().unwrap(), Token::Ident("w0w".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::Equals);
        assert_eq!(
            lexer.next_token().unwrap(),
            Token::Ident("_23all".to_string())
        );
        assert_eq!(lexer.next_token().unwrap(), Token::Op("<".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::Int(-48));
        assert_eq!(lexer.next_token().unwrap(), Token::Op("<=>".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::LParen);
        assert_eq!(lexer.next_token().unwrap(), Token::Int(888));
        assert_eq!(lexer.next_token().unwrap(), Token::Comma);
        assert_eq!(lexer.next_token().unwrap(), Token::Bool(false));
        assert_eq!(lexer.next_token().unwrap(), Token::Comma);
        assert_eq!(lexer.next_token().unwrap(), Token::Int(-6583));
        assert_eq!(lexer.next_token().unwrap(), Token::RParen);
        assert_eq!(lexer.next_token().unwrap(), Token::In);
        assert_eq!(lexer.next_token().unwrap(), Token::Let);
        assert_eq!(lexer.next_token().unwrap(), Token::Ident("f".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::Colon);
        assert_eq!(
            lexer.next_token().unwrap(),
            Token::Ident("Bool".to_string())
        );
        assert_eq!(lexer.next_token().unwrap(), Token::Arrow);
        assert_eq!(
            lexer.next_token().unwrap(),
            Token::Ident("Bool".to_string())
        );
        assert_eq!(lexer.next_token().unwrap(), Token::Equals);
        assert_eq!(lexer.next_token().unwrap(), Token::Backslash);
        assert_eq!(lexer.next_token().unwrap(), Token::Ident("x".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::Colon);
        assert_eq!(
            lexer.next_token().unwrap(),
            Token::Ident("Bool".to_string())
        );
        assert_eq!(lexer.next_token().unwrap(), Token::ThickArrow);
        assert_eq!(lexer.next_token().unwrap(), Token::If);
        assert_eq!(lexer.next_token().unwrap(), Token::Ident("x".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::Op("==".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::Bool(true));
        assert_eq!(lexer.next_token().unwrap(), Token::Then);
        assert_eq!(
            lexer.next_token().unwrap(),
            Token::Ident("y2_y".to_string())
        );
        assert_eq!(lexer.next_token().unwrap(), Token::Else);
        assert_eq!(
            lexer.next_token().unwrap(),
            Token::Ident("zyu2ii".to_string())
        );
        assert_eq!(lexer.next_token().unwrap(), Token::In);
        assert_eq!(lexer.next_token().unwrap(), Token::Ident("f".to_string()));
        assert_eq!(lexer.next_token().unwrap(), Token::Bool(false));
        assert_eq!(lexer.next_token().unwrap(), Token::SemiColon);
        assert_eq!(lexer.next_token().unwrap(), Token::End);
    }

    fn parse_str(s: &str) -> Result<()> {
        let mut ctx = ParserCtx::new();
        let mut parser = Parser::new(&mut ctx, s.chars(), "tests".to_string());
        parser.parse()?;

        Ok(())
    }

    #[test]
    fn test_parser() -> Result<()> {
        parse_str(r#"let f = \x => if g x then gg y2_y else hh zyu2ii in f false"#)?;
        parse_str(r#"let x = (\a => (if a then (b c d) else z)) in x ((a a))"#)?;
        parse_str(r#"let f = \_ => let x = false in if x then false else true in f ()"#)?;
        parse_str(r#"let h = \x y z => if y then x else z in h 42 false 39"#)?;

        let input = r#"
           let f = \x y => if (x y) then 42 else -998
           in let z = -132
              in let g = \_ => true
                 in f g z
        "#;

        parse_str(input)?;

        Ok(())
    }

    #[test]
    fn test_parse_tuple() -> Result<()> {
        let input = r#"
           let x = (false, (), -526)
           in let y = ((), 42191, if true then 0 else 1)
              in let g = \t => if false then t else (true, (), 0)
                 in g x
        "#;
        parse_str(input)?;

        let input = r#"
           let x = ((), false, -99, (), 42)
              in let a = #0(x)
                in let b = #2(x)
                  in (a, b)
        "#;
        parse_str(input)
    }

    #[test]
    fn test_parse_exp() -> Result<()> {
        let input = r#"
           infix 6 <,==;
           infixl 8 +,-;
           infixl 9 *,/;
           let t = abac + 76 *x_3pill - 11 < 91* 3+j
              in t - 14/9 == t+ 78 * 1 + 44
        "#;

        parse_str(input)
    }

    #[test]
    fn test_parse_pattern() -> Result<()> {
        let input = r#"
            let my_var = 2
               in let (v1, v2) = (false, 99)
                     in let (v1, v2, a, b, c) = (1, 1, 1, 1, 1)
                           in let (a, (b, c, d), e, f) = (1, (1, 1, 1), 1, 1) in ()
        "#;
        parse_str(input)
    }

    #[test]
    fn test_parse_pattern_error() {
        let input = "let 42 = 99 in ()";
        assert!(parse_str(input).is_err());

        let input = "let (abc,) = 99 in ()";
        assert!(parse_str(input).is_err());

        let input = "let (a, 42, c) = 99 in ()";
        assert!(parse_str(input).is_err());
    }
}
