use crate::collections::nonemptyvec::NonEmptyVec;
use std::fmt;

pub(crate) fn new_app(oper: Ast, args: NonEmptyVec<Ast>) -> AstBuilder {
    AstBuilder::new(AstKind::App(App::new(oper, args)))
}

pub(crate) fn new_binop(oper: String, lhs: Ast, rhs: Ast) -> AstBuilder {
    AstBuilder::new(AstKind::BinOp(BinOp::new(oper, lhs, rhs)))
}

pub(crate) fn new_bool(val: bool) -> AstBuilder {
    AstBuilder::new(AstKind::Bool(val))
}

pub(crate) fn new_if(cond: Ast, conseq: Ast, alter: Ast) -> AstBuilder {
    AstBuilder::new(AstKind::If(If::new(cond, conseq, alter)))
}

pub(crate) fn new_int(val: i64) -> AstBuilder {
    AstBuilder::new(AstKind::Int(val))
}

pub(crate) fn new_lambda(vars: NonEmptyVec<String>, body: Ast) -> AstBuilder {
    AstBuilder::new(AstKind::Lam(Lambda::new(vars, body)))
}

pub(crate) fn new_let(vars: NonEmptyVec<String>, expr: Ast, body: Ast) -> AstBuilder {
    AstBuilder::new(AstKind::Let(Let::new(vars, expr, body)))
}

pub(crate) fn new_letrec(var: String, vty: Option<Type>, expr: Ast, body: Ast) -> AstBuilder {
    AstBuilder::new(AstKind::Letrec(Letrec::new(var, vty, expr, body)))
}

pub(crate) fn new_tuple(fst: Ast, snd: Ast, rest: Vec<Ast>) -> AstBuilder {
    AstBuilder::new(AstKind::Tuple(Tuple::new(fst, snd, rest)))
}

pub(crate) fn new_tupleref(index: usize, tuple: Ast) -> AstBuilder {
    AstBuilder::new(AstKind::TupleRef(TupleRef::new(index, tuple)))
}

pub(crate) fn new_unit() -> AstBuilder {
    AstBuilder::new(AstKind::Unit)
}

pub(crate) fn new_var(var: String) -> AstBuilder {
    AstBuilder::new(AstKind::Var(var))
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Ast {
    pub kind: AstKind,
    pub span: Span,
}

impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

pub(crate) struct AstBuilder {
    kind: AstKind,
}

impl AstBuilder {
    pub(crate) fn new(kind: AstKind) -> Self {
        Self { kind }
    }

    pub(crate) fn with_span(self, begin: Position, end: Position) -> Ast {
        let span = Span { begin, end };
        Ast {
            kind: self.kind,
            span,
        }
    }
}

/// Abstract syntax tree.
#[derive(Debug, Eq, PartialEq)]
pub(crate) enum AstKind {
    /// ()
    Unit,

    /// Boolean, `true` or `false`
    Bool(bool),

    /// Signed integers.
    Int(i64),

    /// Variables.
    Var(String),

    /// Lambda abstractions.
    Lam(Lambda),

    /// Abstraction application.
    App(App),

    /// Conditional expression.
    If(If),

    /// Let bindings.
    Let(Let),

    /// Letrec bindings.
    Letrec(Letrec),

    /// Heterogeneous collection of values.
    Tuple(Tuple),

    /// Selector of a value inside a tuple.
    TupleRef(TupleRef),

    /// Binary infix operator.
    BinOp(BinOp),
}

impl fmt::Display for AstKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(i) => write!(f, "{i}"),
            Self::Var(v) => write!(f, "{v}"),
            Self::Lam(Lambda { vars, body }) => {
                let (v, vs) = vars.parts();
                write!(f, "λ{v}")?;
                for v in vs {
                    write!(f, " {v}")?;
                }
                write!(f, ". {body}")
            }
            Self::App(App { oper, args }) => {
                write!(f, "({oper}")?;
                for rand in args {
                    write!(f, " {rand}")?;
                }
                write!(f, ")")
            }
            Self::If(If {
                cond,
                conseq,
                alter,
            }) => {
                write!(f, "if {cond} then {conseq} else {alter}")
            }
            Self::Let(Let { vars, expr, body }) => {
                let (v, vs) = vars.parts();
                write!(f, "let {v}")?;
                for v in vs {
                    write!(f, " {v}")?;
                }
                write!(f, " = {expr} in {body}")
            }
            Self::Letrec(Letrec {
                var, expr, body, ..
            }) => {
                write!(f, "letrec {var} = {expr} in {body}")
            }
            Self::Tuple(Tuple { fst, snd, rest }) => {
                write!(f, "({fst}, {snd}")?;
                for t in rest {
                    write!(f, ", {t}")?;
                }
                write!(f, ")")
            }
            Self::TupleRef(TupleRef { index, tuple }) => {
                write!(f, "#{index}({tuple})")
            }
            Self::BinOp(BinOp { oper, lhs, rhs }) => {
                write!(f, "{lhs} {oper} {rhs}")
            }
        }
    }
}

/// Application of an abstraction.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct App {
    /// The application operator.
    pub oper: Box<Ast>,

    /// The operands of the application.
    pub args: NonEmptyVec<Ast>,
}

impl App {
    pub(crate) fn new(oper: Ast, args: NonEmptyVec<Ast>) -> Self {
        Self {
            oper: Box::new(oper),
            args,
        }
    }
}

/// Binary infix operator.
///
/// It's comprised of the operator alongside the left- and
/// right-hand sides.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct BinOp {
    /// The operator.
    pub oper: String,

    /// The left-hand side of the expression.
    pub lhs: Box<Ast>,

    /// The right-hand side of the expression.
    pub rhs: Box<Ast>,
}

impl BinOp {
    pub(crate) fn new(oper: String, lhs: Ast, rhs: Ast) -> Self {
        Self {
            oper,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }
}

/// Conditional expression.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct If {
    /// The condition.
    pub cond: Box<Ast>,

    /// The consequent branch.
    pub conseq: Box<Ast>,

    /// The alternative branch.
    pub alter: Box<Ast>,
}

impl If {
    pub(crate) fn new(cond: Ast, conseq: Ast, alter: Ast) -> Self {
        Self {
            cond: Box::new(cond),
            conseq: Box::new(conseq),
            alter: Box::new(alter),
        }
    }
}

/// Lambda abstractions.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Lambda {
    /// Variable bindinds.
    pub vars: NonEmptyVec<String>,

    /// The abstraction's body.
    pub body: Box<Ast>,
}

impl Lambda {
    pub(crate) fn new(vars: NonEmptyVec<String>, body: Ast) -> Self {
        Self {
            vars,
            body: Box::new(body),
        }
    }
}

/// Let bindings.
///
/// It binds a variable to an expression inside its body. If more
/// than one identifier is given, then the expression is assumed
/// to be the body of a lambda abstraction and the other
/// identifiers are its arguments.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Let {
    /// Variable bindings.
    pub vars: NonEmptyVec<String>,

    /// The expression to be assigned to the binding.
    pub expr: Box<Ast>,

    /// The body where the variable wil be bound.
    pub body: Box<Ast>,
}

impl Let {
    pub(crate) fn new(vars: NonEmptyVec<String>, expr: Ast, body: Ast) -> Self {
        Self {
            vars,
            expr: Box::new(expr),
            body: Box::new(body),
        }
    }
}

/// Letrec bindings.
///
/// Similar to `Let`, but the variable is also in scope inside the
/// expression that gives its own value.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Letrec {
    /// Variable binding.
    pub var: String,

    /// The binding type, if given.
    pub vty: Option<Type>,

    /// The expression to be assigned to the binding.
    pub expr: Box<Ast>,

    /// The body where the variable wil be bound.
    pub body: Box<Ast>,
}

impl Letrec {
    pub(crate) fn new(var: String, vty: Option<Type>, expr: Ast, body: Ast) -> Self {
        Self {
            var,
            vty,
            expr: Box::new(expr),
            body: Box::new(body),
        }
    }
}

/// Heterogeneous collection of values.
///
/// It's comprised of the first and second values, alonside a
/// possibly empty rest of values.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct Tuple {
    /// First element of the tuple.
    pub fst: Box<Ast>,

    /// Second element of the tuple.
    pub snd: Box<Ast>,

    /// Remaining elements of the tuple.
    pub rest: Vec<Ast>,
}

impl Tuple {
    pub(crate) fn new(fst: Ast, snd: Ast, rest: Vec<Ast>) -> Self {
        Self {
            fst: Box::new(fst),
            snd: Box::new(snd),
            rest,
        }
    }
}

/// Selector of a value inside a tuple.
///
/// It's comprised of an index and an expression that must
/// evaluate to a tuple.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct TupleRef {
    /// The index into the tuple.
    pub index: usize,

    /// The tuple expression.
    pub tuple: Box<Ast>,
}

impl TupleRef {
    pub(crate) fn new(index: usize, tuple: Ast) -> Self {
        Self {
            index,
            tuple: Box::new(tuple),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Type {
    Unit,
    Ident(String),
    Func(Box<Type>, Box<Type>),
    Tuple(Box<Type>, Box<Type>, Vec<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Unit => write!(f, "()"),
            Type::Ident(ty) => write!(f, "{}", ty),
            Type::Func(ty1, ty2) => write!(f, "{} → {}", ty1, ty2),
            Type::Tuple(fst, snd, rest) => {
                write!(f, "({}, {}", fst, snd)?;
                for t in rest {
                    write!(f, ", {}", t)?;
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Span {
    pub begin: Position,
    pub end: Position,
}

/// Position of the lexer in the input stream.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Position {
    pub column: usize,
    pub row: usize,
}
