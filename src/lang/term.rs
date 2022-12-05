use super::ast::Span;
use crate::collections::{nonemptyvec::NonEmptyVec, sharedlist::SharedList};
use std::{
    collections::HashSet,
    fmt,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

/// An environment used to keep track of values of bound variables
/// during evaluation.
pub(crate) type Env = SharedList<(Variable, Rc<Term>)>;

/// Kinds of terms of the language.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TermKind {
    Unit,
    Bool(bool),
    Int(i64),
    Var(Variable),
    Lam(Lambda),
    Clo(Closure),
    Fix(Fix),
    App(App),
    If(If),
    Let(Let),
    Tuple(Tuple),
    TupleRef(TupleRef),
    BinOp(BinOp),
}

impl fmt::Display for TermKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermKind::Unit => write!(f, "()"),
            TermKind::Bool(b) => write!(f, "{b}"),
            TermKind::Int(i) => write!(f, "{i}"),
            TermKind::Var(var) => write!(f, "{var}"),
            TermKind::Lam(Lambda { vars, body }) | TermKind::Clo(Closure { vars, body, .. }) => {
                let (head, tail) = vars.parts();
                write!(f, "λ{head}")?;
                for v in tail {
                    write!(f, " {v}")?;
                }
                write!(f, ".{body}")
            }
            TermKind::Fix(Fix { var, body }) => write!(f, "fix(λ{var}. {body})"),
            TermKind::App(App { oper, args }) => {
                write!(f, "({oper}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
            TermKind::If(If {
                cond,
                conseq,
                alter,
            }) => write!(f, "if {cond} then {conseq} else {alter}"),
            TermKind::Let(Let { var, expr, body }) => write!(f, "let {var} = {expr} in {body}"),
            TermKind::Tuple(Tuple { fst, snd, rest }) => {
                write!(f, "({fst}, {snd}")?;
                for t in rest {
                    write!(f, ", {t}")?;
                }
                write!(f, ")")
            }
            TermKind::TupleRef(TupleRef { index, tuple }) => write!(f, "#{index}({tuple})"),
            TermKind::BinOp(BinOp { oper, lhs, rhs }) => write!(f, "{lhs} {oper} {rhs}"),
        }
    }
}

/// Language terms.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Term {
    pub kind: TermKind,
    pub span: Span,
}

impl Term {
    pub fn free_vars(&self) -> HashSet<Variable> {
        match &self.kind {
            TermKind::Unit | TermKind::Bool(_) | TermKind::Int(_) => HashSet::new(),
            TermKind::Var(var) => {
                let mut fv = HashSet::with_capacity(1);
                fv.insert(var.clone());
                fv
            }
            TermKind::Lam(Lambda { vars, body }) | TermKind::Clo(Closure { vars, body, .. }) => {
                let mut fv = body.free_vars();
                for v in vars {
                    fv.remove(v);
                }
                fv
            }
            TermKind::Fix(Fix { var, body }) => {
                let mut fv = body.free_vars();
                fv.remove(var);
                fv
            }
            TermKind::App(App { oper, args }) => {
                let mut fv1 = oper.free_vars();
                for a in args {
                    let fv2 = a.free_vars();
                    fv1.extend(fv2.into_iter());
                }
                fv1
            }
            TermKind::If(If {
                cond,
                conseq,
                alter,
            }) => {
                let mut fv1 = cond.free_vars();
                let fv2 = conseq.free_vars();
                let fv3 = alter.free_vars();
                fv1.extend(fv2.into_iter());
                fv1.extend(fv3.into_iter());
                fv1
            }
            TermKind::Let(Let { var, expr, body }) => {
                let mut fv1 = expr.free_vars();
                let mut fv2 = body.free_vars();
                fv2.remove(var);
                fv1.extend(fv2.into_iter());
                fv1
            }
            TermKind::Tuple(Tuple { fst, snd, rest }) => {
                let mut fv1 = fst.free_vars();
                let fv2 = snd.free_vars();
                let fvs = rest.iter().flat_map(|t| t.free_vars().into_iter());
                fv1.extend(fv2.into_iter());
                fv1.extend(fvs);
                fv1
            }
            TermKind::TupleRef(TupleRef { tuple, .. }) => tuple.free_vars(),
            TermKind::BinOp(BinOp { oper: _, lhs, rhs }) => {
                let mut lfv = lhs.free_vars();
                let rfv = rhs.free_vars();
                lfv.extend(rfv.into_iter());
                lfv
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct App {
    pub oper: Rc<Term>,
    pub args: NonEmptyVec<Rc<Term>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BinOp {
    pub oper: String,
    pub lhs: Rc<Term>,
    pub rhs: Rc<Term>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Closure {
    pub vars: NonEmptyVec<Variable>,
    pub body: Rc<Term>,
    pub env: Env,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Fix {
    pub var: Variable,
    pub body: Rc<Term>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct If {
    pub cond: Rc<Term>,
    pub conseq: Rc<Term>,
    pub alter: Rc<Term>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Lambda {
    pub vars: NonEmptyVec<Variable>,
    pub body: Rc<Term>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Let {
    pub var: Variable,
    pub expr: Rc<Term>,
    pub body: Rc<Term>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Tuple {
    pub fst: Rc<Term>,
    pub snd: Rc<Term>,
    pub rest: Vec<Rc<Term>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TupleRef {
    pub index: usize,
    pub tuple: Rc<Term>,
}

/// Fountain of serial numbers for symbols.
///
/// It starts at 1 because the serial number 0 is reserved for the
/// wildcard `_`.
static SYM_COUNTER: AtomicUsize = AtomicUsize::new(1);

/// Language variables.
///
/// Variables can stand for both values and types.
#[derive(Clone, Eq, Hash, PartialEq)]
pub(crate) enum Variable {
    /// Global variables.
    ///
    /// These don't have a serial number because it's an error to have
    /// more than one global variable with the same name in the same
    /// scope.
    Global(String),

    /// Local variables.
    ///
    /// These are introduced either by an abstraction or a ``let``
    /// term. They have a serial number to avoid the need to
    /// alpha-rename them.
    Local(String, usize),
}

impl Variable {
    pub fn global<S: ToString + ?Sized>(name: &S) -> Variable {
        Self::Global(name.to_string())
    }

    pub fn local<S: ToString + ?Sized>(name: &S) -> Variable {
        let name = name.to_string();
        if name == "_" {
            Variable::Local(name, 0)
        } else {
            Variable::Local(name, SYM_COUNTER.fetch_add(1, Ordering::Relaxed))
        }
    }

    pub fn name(&self) -> &str {
        match self {
            Self::Global(name) | Self::Local(name, _) => name,
        }
    }
}

impl fmt::Debug for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Global(name) => name.fmt(f),
            Self::Local(name, serial) => write!(f, "{name}@{serial}"),
        }
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Global(name) | Self::Local(name, _) => name.fmt(f),
        }
    }
}
