/*!
 * Mirage's built-in programming language.
 */

mod parser;

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::nonemptyvec::*;
use crate::sharedlist::*;


static SYM_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// Language errors.
#[derive(Debug, Eq, PartialEq)]
pub enum ErrorKind {
    InfiniteType,
    ParserError,
    RuntimeError,
    TypeMismatch,
    UnknownOperator,
    VariableNotFound,
}

#[derive(Debug, Eq, PartialEq)]
pub struct Error {
    kind: ErrorKind,
    msg: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl std::error::Error for Error {
    fn description(&self) -> &str {
        &self.msg
    }
}

impl From<parser::Error> for Error {
    fn from(err: parser::Error) -> Error {
        Error {
            kind: ErrorKind::ParserError,
            msg: format!("parser error: {}", err),
        }
    }
}

type Result<A> = std::result::Result<A, Error>;

/// Language variables.
///
/// Variables can stand for both values and types.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Variable {
    /// Variable name given in the source code.
    name: String,

    /// Variables can be renamed to have unique aliases.
    alias: String,
}

impl Variable {
    fn new(name: &str) -> Variable {
        // Generates a new unique symbol using the given name as
        // prefix. `@` is being used here as it should not be part of
        // the input syntax for identifiers.
        let alias = format!("{}@{}", name, SYM_COUNTER.fetch_add(1, Ordering::Relaxed));

        Variable {
            name: name.to_string(),
            alias,
        }
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.alias.fmt(f)
    }
}

/// Language types.
///
/// The variable type is for types that have not been resolved yet.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Type {
    Unit,
    Bool,
    Int,
    Func(Box<Type>, Box<Type>),
    Tuple(Box<Type>, Box<Type>, Vec<Type>),
    Var(Variable),
}

impl Type {
    /// Collect all variables contained in type
    fn vars(&self) -> HashSet<Variable> {
        match self {
            Type::Unit | Type::Bool | Type::Int => HashSet::new(),
            Type::Func(ty1, ty2) => {
                let mut s1 = ty1.vars();
                let mut s2 = ty2.vars();
                s1.extend(s2.drain());
                s1
            },
            Type::Tuple(f, s, r) => {
                let mut fv = f.vars();
                let mut sv = s.vars();
                let mut rv = r.iter().flat_map(|t| t.vars()).collect::<HashSet<_>>();
                fv.extend(sv.drain());
                fv.extend(rv.drain());
                fv
            },
            Type::Var(v) => {
                let mut s = HashSet::with_capacity(1);
                s.insert(v.clone());
                s
            },
        }
    }

    /// Apply a single type substitution.
    fn apply_one(self, var: &Variable, ttype: &Type) -> Type {
        match self {
            Type::Unit | Type::Bool | Type::Int => self,
            Type::Func(ty1, ty2) => Type::Func(
                Box::new(ty1.apply_one(var, ttype)),
                Box::new(ty2.apply_one(var, ttype)),
            ),
            Type::Tuple(fst, snd, rest) => Type::Tuple(
                Box::new(fst.apply_one(var, ttype)),
                Box::new(snd.apply_one(var, ttype)),
                rest.into_iter().map(|ty| ty.apply_one(var, ttype)).collect(),
            ),
            Type::Var(v) => if *var == v {
                ttype.clone()
            } else {
                Type::Var(v)
            },
        }
    }

    /// Applies a type substitution.
    fn apply(self, subst: &TypeSubst) -> Type {
        subst.iter().fold(self, |ttype, (v, ty)| ttype.apply_one(v, ty))
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Unit => write!(f, "()"),
            Type::Bool => write!(f, "Bool"),
            Type::Int => write!(f, "Int"),
            Type::Func(ty1, ty2) => write!(f, "{} -> {}", ty1, ty2),
            Type::Tuple(fst, snd, rest) => {
                write!(f, "({}, {}", fst, snd)?;
                for t in rest {
                    write!(f, ", {}", t)?;
                }
                write!(f, ")" )
            },
            Type::Var(v) => {
                write!(f, "{}", v)
            },
        }
    }
}

/// Type substitutions must be applied in order.
type TypeSubst = Vec<(Variable, Type)>;

/// A type scheme is a polymorphic type with free variables.
#[derive(Clone, Debug)]
struct TypeScheme {
    /// Principal type.
    ptype: Type,

    /// Free type variables.
    vars: Vec<Variable>,
}

impl TypeScheme {
    fn new(t: Type) -> TypeScheme {
        TypeScheme {
            ptype: t,
            vars: Vec::new(),
        }
    }
}

/// A typing context used to keep track of bound variables during type
/// checking.
type Ctx = SharedList<NonEmptyVec<Variable>>;

/// An environment used to keep track of values of bound variables
/// during evaluation.
type Env = SharedList<NonEmptyVec<(Variable, Term)>>;

type ConstrSet = Vec<(Type, Type)>;

/// Applies a type substitution to all types in a constraint set.
fn subst_constraints(constrs: &mut ConstrSet, var: &Variable, ttype: &Type) {
    for (lhs, rhs) in constrs {
        *lhs = lhs.clone().apply_one(var, ttype);
        *rhs = rhs.clone().apply_one(var, ttype);
    }
}

/// Kinds of terms of the language.
#[derive(Clone, Debug, Eq, PartialEq)]
enum TermKind {
    Unit,
    Bool(bool),
    Int(i64),
    Var(Variable),
    Lam(NonEmptyVec<Variable>, Box<Term>),
    Clo(NonEmptyVec<Variable>, Box<Term>, Vec<(Variable, Term)>),
    Fix(Variable, Box<Term>),
    App(Box<Term>, NonEmptyVec<Term>),
    If(Box<Term>, Box<Term>, Box<Term>),
    Let(Variable, Box<Term>, Box<Term>),
    Tuple(Box<Term>, Box<Term>, Vec<Term>),
    TupleRef(usize, Box<Term>),
    BinOp(String, Box<Term>, Box<Term>),
}

impl fmt::Display for TermKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result<> {
        match self {
            TermKind::Unit => write!(f, "()"),
            TermKind::Bool(b) => write!(f, "{}", b),
            TermKind::Int(i) => write!(f, "{}", i),
            TermKind::Var(var) => write!(f, "{}", var),
            TermKind::Lam(vs, t) => {
                let (head, tail) = vs.parts();
                write!(f, "λ{}", head)?;
                for v in tail {
                    write!(f, " {}", v)?;
                }
                write!(f, ".{}", t)
            },
            TermKind::Clo(vs, t, _) => {
                let (head, tail) = vs.parts();
                write!(f, "λ{}", head)?;
                for v in tail {
                    write!(f, " {}", v)?;
                }
                write!(f, ".{}", t)
            },
            TermKind::Fix(v, t) => write!(f, "fix(λ{}. {})", v, t),
            TermKind::App(fun, args) => {
                write!(f, "({}", fun)?;
                for arg in args {
                    write!(f, " {}", arg)?;
                }
                write!(f, ")")
            },
            TermKind::If(t1, t2, t3) => write!(f, "if {} then {} else {}", t1, t2, t3),
            TermKind::Let(v, t1, t2) => write!(f, "let {} = {} in {}", v, t1, t2),
            TermKind::Tuple(fst, snd, rest) => {
                write!(f, "({}, {}", fst, snd)?;
                for t in rest {
                    write!(f, ", {}", t)?;
                }
                write!(f, ")")
            },
            TermKind::TupleRef(i, t) => write!(f, "#{}({})", i, t),
            TermKind::BinOp(op, lhs, rhs) => write!(f, "{} {} {}", lhs, op, rhs),
        }
    }
}

/// Language terms.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Term {
    kind: TermKind,
}

impl Term {
    fn free_vars(&self) -> HashSet<Variable> {
        match &self.kind {
            TermKind::Unit | TermKind::Bool(_) | TermKind::Int(_) => HashSet::new(),
            TermKind::Var(var) => {
                let mut fv = HashSet::with_capacity(1);
                fv.insert(var.clone());
                fv
            },
            TermKind::Lam(vs, t) => {
                let mut fv = t.free_vars();
                for v in vs {
                    fv.remove(&v);
                }
                fv
            },
            TermKind::Clo(vs, t, _) => {
                let mut fv = t.free_vars();
                for v in vs {
                    fv.remove(&v);
                }
                fv
            },
            TermKind::Fix(v, t) => {
                let mut fv = t.free_vars();
                fv.remove(&v);
                fv
            },
            TermKind::App(fun, args) => {
                let mut fv1 = fun.free_vars();
                for a in args {
                    let fv2 = a.free_vars();
                    fv1.extend(fv2.into_iter());
                }
                fv1
            },
            TermKind::If(t1, t2, t3) => {
                let mut fv1 = t1.free_vars();
                let fv2 = t2.free_vars();
                let fv3 = t3.free_vars();
                fv1.extend(fv2.into_iter());
                fv1.extend(fv3.into_iter());
                fv1
            },
            TermKind::Let(v, t1, t2) => {
                let mut fv1 = t1.free_vars();
                let mut fv2 = t2.free_vars();
                fv2.remove(&v);
                fv1.extend(fv2.into_iter());
                fv1
            },
            TermKind::Tuple(t1, t2, ts) => {
                let mut fv1 = t1.free_vars();
                let fv2 = t2.free_vars();
                let fvs = ts.iter().flat_map(|t| t.free_vars().into_iter());
                fv1.extend(fv2.into_iter());
                fv1.extend(fvs);
                fv1
            },
            TermKind::TupleRef(_, t) => {
                t.free_vars()
            },
            TermKind::BinOp(_, lhs, rhs) => {
                let mut lfv = lhs.free_vars();
                let rfv = rhs.free_vars();
                lfv.extend(rfv.into_iter());
                lfv
            },
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result<> {
        self.kind.fmt(f)
    }
}

fn lookup(var: &Variable, env: &Env) -> Option<Term> {
    env.iter().find_map(|rib| rib.into_iter().find(|(v, _)| v == var)).map(|(_, t)| t)
}

// Operators are just functions, but since we don't have
// multi-argument functions yet they will be implemented as special
// primitives for now
#[derive(Clone, Debug)]
struct OpInfo {
    ltype : Type,
    rtype : Type,
    ttype : Type,
}

type OperatorTable = Vec<(&'static str, OpInfo)>;

/// Performs semantic analysis
#[derive(Debug)]
struct Analyser {
    /// Table of known operators.
    oper_table: OperatorTable,

    /// Symbol table with information about identifiers.
    sym_table: HashMap<Variable, TypeScheme>,
}

impl Analyser {
    fn new() -> Analyser {
        Analyser {
            oper_table: vec![
                (
                    "+",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Int,
                    }
                ),
                (
                    "-",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Int,
                    }
                ),
                (
                    "*",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Int,
                    }
                ),
                (
                    "/",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Int,
                    }
                ),
                (
                    "==",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Bool,
                    }
                ),
                (
                    "<",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Bool,
                    }
                ),
                (
                    ">",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Bool,
                    }
                ),
                (
                    "<=",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Bool,
                    }
                ),
                (
                    ">=",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Bool,
                    }
                ),
            ],
            sym_table: HashMap::new(),
        }
    }

    /// Converts type parse trees into actual types.
    fn analyse_type(src: &parser::Type) -> Result<Type> {
        match src {
            parser::Type::Unit => Ok(Type::Unit),
            parser::Type::Ident(ident) => match ident.as_ref() {
                "Bool" => Ok(Type::Bool),
                "Int" => Ok(Type::Int),
                _ => Err(
                    Error {
                        kind: ErrorKind::TypeMismatch,
                        msg: format!("unknown type {}", ident),
                    }
                ),
            },
            parser::Type::Func(ty1, ty2) => Ok(
                Type::Func(
                    Box::new(Analyser::analyse_type(ty1)?),
                    Box::new(Analyser::analyse_type(ty2)?),
                )
            ),
            parser::Type::Tuple(fst, snd, rest) => Ok(
                Type::Tuple(
                    Box::new(Analyser::analyse_type(fst)?),
                    Box::new(Analyser::analyse_type(snd)?),
                    rest.iter().map(|ty| Analyser::analyse_type(ty)).collect::<Result<Vec<_>>>()?,
                )
            ),
        }
    }

    fn apply_subst(&mut self, subst: &TypeSubst) {
        for (_, ts) in self.sym_table.iter_mut() {
            ts.ptype = ts.ptype.clone().apply(subst);
        }
    }

    fn unify(mut constraints: ConstrSet) -> Result<TypeSubst> {
        let mut subst = Vec::new();

        while let Some((lhs, rhs)) = constraints.pop() {
            if lhs != rhs {
                if let Type::Var(v) = lhs {
                    if rhs.vars().contains(&v) {
                        return Err(
                            Error {
                                kind: ErrorKind::InfiniteType,
                                msg: format!("Type variable {} refers to itself", v),
                            }
                        )
                    } else {
                        subst_constraints(&mut constraints, &v, &rhs);
                        subst.push((v, rhs));
                    }
                } else if let Type::Var(v) = rhs {
                    if lhs.vars().contains(&v) {
                        return Err(
                            Error {
                                kind: ErrorKind::InfiniteType,
                                msg: format!("Type variable {} refers to itself", v),
                            }
                        )
                    } else {
                        subst_constraints(&mut constraints, &v, &lhs);
                        subst.push((v, lhs));
                    }
                } else if let Type::Func(lhs1, lhs2) = lhs {
                    if let Type::Func(rhs1, rhs2) = rhs {
                        constraints.push((*lhs1, *rhs1));
                        constraints.push((*lhs2, *rhs2));
                    } else {
                        return Err(
                            Error {
                                kind: ErrorKind::TypeMismatch,
                                msg: format!("{:?} is not a function type", rhs),
                            }
                        )
                    }
                } else if let Type::Tuple(lfst, lsnd, lrest) = lhs {
                    if let Type::Tuple(rfst, rsnd, rrest) = rhs {
                        constraints.push((*lfst, *rfst));
                        constraints.push((*lsnd, *rsnd));
                        for (l, r) in lrest.into_iter().zip(rrest.into_iter()) {
                            constraints.push((l, r));
                        }
                    } else {
                        return Err(
                            Error {
                                kind: ErrorKind::TypeMismatch,
                                msg: format!("{:?} is not a tuple type", rhs),
                            }
                        )
                    }
                } else {
                    return Err(
                        Error {
                            kind: ErrorKind::TypeMismatch,
                            msg: (format!("Cannot unify the types {:?} and {:?}", lhs, rhs)),
                        }
                    )
                }
            }
        }

        Ok(subst)
    }

    fn typecheck(&mut self, sterm: &parser::Term) -> Result<(Term, Type)> {

        fn walk(anal: &mut Analyser, s: &parser::Term, ctx: &Ctx) -> Result<(Term, Type, ConstrSet)> {
            match s {
                parser::Term::Unit => Ok((
                    Term {
                        kind: TermKind::Unit,
                    },
                    Type::Unit,
                    Vec::new(),
                )),
                parser::Term::Bool(b) => Ok((
                    Term {
                        kind: TermKind::Bool(*b),
                    },
                    Type::Bool,
                    Vec::new(),
                )),
                parser::Term::Int(i) => Ok((
                    Term {
                        kind: TermKind::Int(*i),
                    },
                    Type::Int,
                    Vec::new(),
                )),
                parser::Term::Var(n) => {
                    if let Some(var) = ctx.iter().find_map(|vs| vs.into_iter().find(|v| v.name == *n)) {
                        let ts = anal.sym_table.get(&var).ok_or(
                            Error {
                                kind: ErrorKind::VariableNotFound,
                                msg: format!("Variable '{}' was not found in symbol table", var),
                            }
                        )?;

                        let ts = ts.clone();

                        // create fresh type variables for the free
                        // variables to allow polymorphism
                        let subst = ts
                            .vars
                            .into_iter()
                            .map(|v| (v, Type::Var(Variable::new("P"))))
                            .collect();

                        Ok((
                            Term {
                                kind: TermKind::Var(var),
                            },
                            ts.ptype.apply(&subst),
                            Vec::new(),
                        ))
                    } else {
                        Err(
                            Error {
                                kind: ErrorKind::VariableNotFound,
                                msg: format!("Variable {} is not in scope", n),
                            }
                        )
                    }
                },
                parser::Term::Lam(vs, s) => {
                    let rib = vs.map(|v| Variable::new(v));
                    for var in &rib {
                        let ty = Type::Var(Variable::new("X"));
                        let ts = TypeScheme::new(ty);
                        anal.sym_table.insert(var.clone(), ts);
                    }

                    let new_ctx = ctx.cons(rib.clone());
                    let (t, mut ttype, cs) = walk(anal, s, &new_ctx)?;

                    let mut rvec = rib.clone().to_vec();
                    rvec.reverse();
                    for v in rvec {
                        let ptype = anal
                            .sym_table
                            .get(&v)
                            .map(|ts| ts.ptype.clone())
                            .ok_or(
                                Error {
                                    kind: ErrorKind::VariableNotFound,
                                    msg: format!("Variable {} was not found in symbol table", v),
                                }
                            )?;
                        ttype = Type::Func(Box::new(ptype), Box::new(ttype));
                    }
                    Ok((
                        Term {
                            kind: TermKind::Lam(
                                rib,
                                Box::new(t),
                            ),
                        },
                        ttype,
                        cs
                    ))
                },
                parser::Term::App(s1, ss) => {
                    let (t1, ty1, cs1) = walk(anal, s1, ctx)?;

                    let (s2, ss) = ss.parts();
                    let (t2, ty2, cs2) = walk(anal, s2, ctx)?;

                    let mut ts = NonEmptyVec::new(t2);

                    let mut tys = VecDeque::new();
                    tys.push_front(ty2);

                    let mut cs = ConstrSet::new();
                    cs.extend(cs1.into_iter());
                    cs.extend(cs2.into_iter());

                    for s in ss {
                        let (t, ty, c) = walk(anal, s, ctx)?;
                        ts.push(t);
                        tys.push_front(ty);
                        cs.extend(c.into_iter());
                    }

                    let var = Type::Var(Variable::new("Y"));
                    let mut func_ty = var.clone();
                    for ty in tys.into_iter() {
                        func_ty = Type::Func(Box::new(ty), Box::new(func_ty));
                    }

                    cs.push((ty1, func_ty));
                    let subst = Analyser::unify(cs.clone())?;
                    anal.apply_subst(&subst);

                    Ok((
                        Term {
                            kind: TermKind::App(
                                Box::new(t1),
                                ts
                            ),
                        },
                        var.apply(&subst),
                        cs,
                    ))
                },
                parser::Term::If(s1, s2, s3) => {
                    let (t1, ty1, cs1) = walk(anal, s1, ctx)?;
                    let (t2, ty2, cs2) = walk(anal, s2, ctx)?;
                    let (t3, ty3, cs3) = walk(anal, s3, ctx)?;

                    let mut cs = ConstrSet::new();
                    cs.extend(cs1.into_iter());
                    cs.extend(cs2.into_iter());
                    cs.extend(cs3.into_iter());
                    cs.push((ty1, Type::Bool));
                    cs.push((ty2, ty3.clone()));

                    let subst = Analyser::unify(cs.clone())?;
                    anal.apply_subst(&subst);

                    Ok((
                        Term {
                            kind: TermKind::If(
                                Box::new(t1),
                                Box::new(t2),
                                Box::new(t3),
                            ),
                        },
                        ty3.apply(&subst),
                        cs,
                    ))
                },
                parser::Term::Let(v, s1, s2) => {
                    let (t1, ty1, cs1) = walk(anal, s1, ctx)?;
                    let tvars = ty1
                        .vars()
                        .into_iter()
                        .filter(|v1| ctx
                                .iter()
                                .all(|vs| vs.into_iter()
                                     .all(|v2| anal
                                          .sym_table
                                          .get(&v2)
                                          .map(|ts| !ts.ptype.vars().contains(v1))
                                          .unwrap_or(true)
                                     )
                                )
                        )
                        .collect();
                    let var = Variable::new(v);
                    let ts = TypeScheme {
                        ptype: ty1,
                        vars: tvars,
                    };
                    anal.sym_table.insert(var.clone(), ts);

                    let rib = NonEmptyVec::new(var.clone());
                    let (t2, ty2, cs2) = if v.starts_with("_") {
                        walk(anal, s2, ctx)?
                    } else {
                        let new_ctx = ctx.cons(rib);
                        walk(anal, s2, &new_ctx)?
                    };

                    let mut cs = cs1;
                    cs.extend(cs2.into_iter());

                    Ok((
                        Term {
                            kind: TermKind::Let(
                                var,
                                Box::new(t1),
                                Box::new(t2),
                            ),
                        },
                        ty2,
                        cs,
                    ))
                },
                parser::Term::Letrec(v, oty, s1, s2) => {
                    let var = Variable::new(v);
                    let vty = oty
                        .as_ref()
                        .map(|ty| Analyser::analyse_type(ty))
                        .unwrap_or(Ok(Type::Var(Variable::new("F"))))?;
                    let ts = TypeScheme::new(vty.clone());
                    anal.sym_table.insert(var.clone(), ts);

                    let rib = NonEmptyVec::new(var.clone());
                    let new_ctx = ctx.cons(rib);
                    let (t1, ty1, cs1) = walk(anal, s1, &new_ctx)?;
                    let (t2, ty2, cs2) = walk(anal, s2, &new_ctx)?;

                    let mut cs = ConstrSet::new();
                    cs.extend(cs1.into_iter());
                    cs.extend(cs2.into_iter());
                    cs.push((vty, ty1));

                    let subst = Analyser::unify(cs.clone())?;
                    anal.apply_subst(&subst);

                    let fix = Term {
                        kind: TermKind::Fix(var.clone(), Box::new(t1)),
                    };

                    Ok((
                        Term {
                            kind: TermKind::Let(var, Box::new(fix), Box::new(t2)),
                        },
                        ty2.apply(&subst),
                        cs,
                    ))
                },
                parser::Term::Tuple(fst, snd, rest) => {
                    let (t1, ty1, cs1) = walk(anal, fst, ctx)?;
                    let (t2, ty2, cs2) = walk(anal, snd, ctx)?;
                    let ts_tys_css = rest.iter().map(|t| walk(anal, t, ctx)).collect::<Result<Vec<_>>>()?;

                    let mut ts = Vec::new();
                    let mut tys = Vec::new();
                    let mut css = Vec::new();
                    css.extend(cs1.into_iter());
                    css.extend(cs2.into_iter());
                    for (t, ty, cs) in ts_tys_css {
                        ts.push(t);
                        tys.push(ty);
                        css.extend(cs.into_iter());
                    }

                    Ok((
                        Term {
                            kind: TermKind::Tuple(Box::new(t1), Box::new(t2), ts),
                        },
                        Type::Tuple(Box::new(ty1), Box::new(ty2), tys),
                        css,
                    ))
                },
                parser::Term::TupleRef(i, t) => {
                    let (t, ty, mut cs) = walk(anal, t, ctx)?;

                    // create principal tuple type, the size of the
                    // rest vector is just the smallest size that will
                    // typecheck
                    let fst = Type::Var(Variable::new("T"));
                    let snd = Type::Var(Variable::new("T"));
                    let len = (i+1).saturating_sub(2);
                    let mut rest = Vec::with_capacity(len);
                    for _ in 0..len {
                        rest.push(Type::Var(Variable::new("T")))
                    }

                    let ttype = if *i == 0 {
                        fst.clone()
                    } else if *i == 1 {
                        snd.clone()
                    } else {
                        // unwrap is safe because i > 1, so rest is not empty
                        rest.last().map(|ty| ty.clone()).unwrap()
                    };
                    let tuple_type = Type::Tuple(Box::new(fst), Box::new(snd), rest);

                    cs.push((ty, tuple_type));

                    let subst = Analyser::unify(cs.clone())?;
                    anal.apply_subst(&subst);

                    Ok((
                        Term {
                            kind: TermKind::TupleRef(*i, Box::new(t)),
                        },
                        ttype.apply(&subst),
                        cs,
                    ))
                },
                parser::Term::BinOp(op, s1, s2) => {
                    let (t1, ty1, cs1) = walk(anal, s1, ctx)?;
                    let (t2, ty2, cs2) = walk(anal, s2, ctx)?;

                    let info = anal
                        .oper_table
                        .iter()
                        .find(|(o, _)| o == op)
                        .map(|(_, i)| i.clone())
                        .ok_or(
                            Error {
                                kind: ErrorKind::UnknownOperator,
                                msg: format!("Operator {} not found", op),
                            }
                        )?;

                    let mut cs = ConstrSet::new();
                    cs.extend(cs1.into_iter());
                    cs.extend(cs2.into_iter());
                    cs.push((ty1, info.ltype));
                    cs.push((ty2, info.rtype));

                    let subst = Analyser::unify(cs.clone())?;
                    anal.apply_subst(&subst);

                    Ok((
                        Term {
                            kind: TermKind::BinOp(op.clone(), Box::new(t1), Box::new(t2)),
                        },
                        info.ttype,
                        cs,
                    ))
                },
            }
        }

        walk(self, sterm, &SharedList::nil()).map(|(t, ty, _)| (t, ty))
    }

    fn eval(&self, term: &Term) -> Result<Term> {
        fn walk(t: &Term, env: &Env, fenv: &Vec<(Variable, Term)>) -> Result<Term> {
            match &t.kind {
                TermKind::Unit | TermKind::Bool(_) |
                TermKind::Int(_) | TermKind::Clo(_, _, _) => Ok(t.clone()),
                TermKind::Var(v) => {
                    env
                        .iter()
                        .find_map(|rib| rib.into_iter().find(|(var, _)| var == v))
                        .map(|(_, val)| val)
                        .or_else(|| fenv.iter().find(|(var, _)| var == v).map(|(_, val)| val.clone()))
                        .ok_or(
                        Error {
                            kind: ErrorKind::RuntimeError,
                            msg: format!("variable {} not found in environment", v),
                        }
                    )
                },
                TermKind::Lam(v, t1) => {
                    let fv = t.free_vars();
                    let frozen_env = fv.into_iter().map(|v| (v.clone(), lookup(&v, env).unwrap())).collect();
                    Ok(Term {kind: TermKind::Clo(v.clone(), t1.clone(), frozen_env)})
                },
                TermKind::Fix(v, t1) => {
                    let new_env = env.cons(NonEmptyVec::new((v.clone(), t.clone())));
                    walk(t1, &new_env, fenv)
                },
                TermKind::App(fun, args) => {
                    let mut val = walk(fun, env, fenv)?;
                    let mut args_q = args.iter().collect::<VecDeque<_>>();
                    while !args_q.is_empty() {
                        if let TermKind::Clo(vars, body, fenv1) = val.kind {
                            let (v1, vs) = vars.into_parts();
                            let a1 = args_q.pop_front().unwrap();
                            let e1 = walk(a1, env, fenv)?;
                            let mut rib = NonEmptyVec::new((v1, e1));
                            for v in vs {
                                let a = args_q.pop_front().ok_or(
                                    Error {
                                        kind: ErrorKind::RuntimeError,
                                        msg: format!("insufficient number of arguments given to closure"),
                                    }
                                )?;
                                let e = walk(a, env, fenv)?;
                                rib.push((v, e));
                            }
                            let new_env = env.cons(rib);
                            val = walk(&body, &new_env, &fenv1)?;
                        } else {
                            return Err(
                                Error {
                                    kind: ErrorKind::RuntimeError,
                                    msg: format!(
                                        "term {} is not a closure but is being applied",
                                        val
                                    ),
                                }
                            )
                        }
                    };
                    Ok(val)
                },
                TermKind::If(t1, t2, t3) => {
                    let guard = walk(t1, env, fenv)?;
                    if let TermKind::Bool(b) = guard.kind {
                        if b {
                            walk(t2, env, fenv)
                        } else {
                            walk(t3, env, fenv)
                        }
                    } else {
                        Err(
                            Error {
                                kind: ErrorKind::RuntimeError,
                                msg: format!(
                                    "`if` guard must be a boolean, but {:?} was given",
                                    guard
                                ),
                            }
                        )
                    }
                },
                TermKind::Let(v, t1, t2) => {
                    let arg = walk(t1, env, fenv)?;
                    let new_env = env.cons(NonEmptyVec::new((v.clone(), arg)));
                    walk(t2, &new_env, fenv)
                },
                TermKind::Tuple(fst, snd, rest) => {
                    let fst = walk(fst, env, fenv)?;
                    let snd = walk(snd, env, fenv)?;
                    let rest = rest
                        .iter()
                        .map(|t| walk(t, env, fenv))
                        .collect::<Result<Vec<_>>>()?;
                    Ok(
                        Term {
                            kind: TermKind::Tuple(Box::new(fst), Box::new(snd), rest),
                        }
                    )
                },
                TermKind::TupleRef(i, t) => {
                    let v = walk(t, env, fenv)?;
                    if let TermKind::Tuple(fst, snd, mut rest) = v.kind {
                        if *i == 0 {
                            Ok(*fst)
                        } else if *i == 1 {
                            Ok(*snd)
                        } else {
                            Ok(rest.swap_remove(*i - 2))
                        }
                    } else {
                        Err(
                            Error {
                                kind: ErrorKind::RuntimeError,
                                msg: format!("Cannot index non-tuple {:?}", v)
                            }
                        )
                    }
                },
                TermKind::BinOp(op, t1, t2) => {
                    let e1 = walk(t1, env, fenv)?;
                    if let TermKind::Int(lhs) = e1.kind {
                        let e2 = walk(t2, env, fenv)?;
                        if let TermKind::Int(rhs) = e2.kind {
                            match op.as_str() {
                                "+" => Ok(
                                    Term {
                                        kind: TermKind::Int(lhs + rhs),
                                    }
                                ),
                                "-" => Ok(
                                    Term {
                                        kind: TermKind::Int(lhs - rhs),
                                    }
                                ),
                                "*" => Ok(
                                    Term {
                                        kind: TermKind::Int(lhs * rhs),
                                    }
                                ),
                                "/" => Ok(
                                    Term {
                                        kind: TermKind::Int(lhs / rhs),
                                    }
                                ),
                                "==" => Ok(
                                    Term {
                                        kind: TermKind::Bool(lhs == rhs),
                                    }
                                ),
                                "<" => Ok(
                                    Term {
                                        kind: TermKind::Bool(lhs < rhs),
                                    }
                                ),
                                 ">" => Ok(
                                    Term {
                                        kind: TermKind::Bool(lhs > rhs),
                                    }
                                ),
                                "<=" => Ok(
                                    Term {
                                        kind: TermKind::Bool(lhs <= rhs),
                                    }
                                ),
                                 ">=" => Ok(
                                    Term {
                                        kind: TermKind::Bool(lhs >= rhs),
                                    }
                                ),
                               _ => Err(
                                    Error {
                                        kind: ErrorKind::RuntimeError,
                                        msg: format!("Unknown operator {}", op),
                                    }
                                ),
                            }
                        } else {
                            Err(
                                Error {
                                    kind: ErrorKind::RuntimeError,
                                    msg: format!("Right-hand side of operator is not an integer, it's {:?}", e2),
                                }
                            )
                        }
                    } else {
                        Err(
                            Error {
                                kind: ErrorKind::RuntimeError,
                                msg: format!("Left-hand side of operator is not an integer, it's {:?}", e1),
                            }
                        )
                    }
                },
            }
        }

        walk(term, &SharedList::nil(), &Vec::new())
    }
}

pub fn eval_str(src: &str, context: String) -> Result<String> {
    let mut parser = parser::Parser::new(src.chars(), context);
    let sterm = parser.parse()?;

    let mut anal = Analyser::new();
    let (term, _) = anal.typecheck(&sterm)?;

    let val = anal.eval(&term)?;
    Ok(format!("{}", val))
}

#[cfg(test)]
mod test {
    use super::*;

    fn typecheck_str(src: &str) -> Result<Type> {
        let mut parser = parser::Parser::new(src.chars(), "tests".to_string());
        let sterm = parser.parse()?;

        let mut anal = Analyser::new();
        let (_, ttype) = anal.typecheck(&sterm)?;

        Ok(ttype)
    }

    #[test]
    fn test_typecheck() -> Result<()> {
        assert_eq!(typecheck_str("false")?, Type::Bool);
        assert_eq!(typecheck_str("true")?, Type::Bool);

        assert_eq!(typecheck_str("let x = false in x")?, Type::Bool);
        assert_eq!(typecheck_str("let y = true in y")?, Type::Bool);
        assert_eq!(typecheck_str("if false then true else false")?, Type::Bool);

        assert!(
            matches!(
                typecheck_str(r#"if true then \x => false else \z => true"#)?,
                Type::Func(_, _)
            )
        );

        let input = r#"
           let x = false
           in let y = true
              in let z = false
                 in let and = \x y => if x then y else x
                    in if and x y then y else z
         "#;
        assert_eq!(typecheck_str(input)?, Type::Bool);

        let unit = r#"
           let f = \_ => false
           in let g = \x => if x then () else ()
              in g (f ())
        "#;
        assert_eq!(typecheck_str(unit)?, Type::Unit);

        let int = r#"
           let f = \x y => if (x y) then 42 else -998
           in let z = -132
              in let g = \_ => true
                 in f g z
        "#;
        assert_eq!(typecheck_str(int)?, Type::Int);

        Ok(())
    }

    #[test]
    fn test_typecheck_tuple() -> Result<()> {
        let tuple1 = r#"
           let x = (false, (), -526)
           in let y = ((), 42191, if true then 0 else 1)
              in let g = \t => if false then t else (true, (), 0)
                 in g x
        "#;
        assert_eq!(
            typecheck_str(tuple1)?,
            Type::Tuple(Box::new(Type::Bool), Box::new(Type::Unit), vec![Type::Int])
        );

        let tuple2 = r#"
           let f = \x => if #2(x) then #3(x) else #0(x)
           in f (-12132, (), true, 77)
        "#;
        assert_eq!(typecheck_str(tuple2)?, Type::Int);

        Ok(())
    }

    fn eval_str(input: &str) -> Result<Term> {
        let mut parser = parser::Parser::new(input.chars(), "tests".to_string());
        let sterm = parser.parse()?;
        let mut anal = Analyser::new();
        let (term, _) = anal.typecheck(&sterm)?;
        anal.eval(&term)
    }

    #[test]
    fn test_eval() -> Result<()> {
        let i1 = r#"
           let a = (-5411, (), true, 42)
           in let f = \x => if #2(x) then #3(x) else #0(x)
              in f a
        "#;
        let t1 = eval_str(i1)?;
        assert!(matches!(t1.kind, TermKind::Int(i) if i == 42));

        let i2 = r#"
           let x = (true, true, true)
           in letrec f : (Bool, Bool, Bool) -> (Bool, Bool, Bool) = \a =>
                 if #2(a)
                    then f (true, true, false)
                    else if #1(a)
                         then f (true, false, false)
                         else if #0(a)
                                 then f (false, false, false)
                                 else (false, false, false)
              in f x
        "#;
        let t2 = eval_str(i2)?;
        let tfalse = Box::new(Term {kind: TermKind::Bool(false)});
        let rfalse = vec!(Term {kind: TermKind::Bool(false)});
        assert!(
            matches!(
                t2.kind,
                TermKind::Tuple(fst, snd, rest) if fst == tfalse && snd == tfalse && rest == rfalse
            )
        );

        let i3 = r#"
           infix 6 <;
           infixl 8 -;
           infixl 9 *;
           let fact = \n =>
              letrec go = \t =>
                 if #0(t) < 1
                    then #1(t)
                    else go (#0(t) - 1, #0(t) * #1(t))
              in go (n, 1)
           in fact 6
        "#;
        let t3 = eval_str(i3)?;
        assert!(matches!(t3.kind, TermKind::Int(i) if i == 720));

        Ok(())
    }

    #[test]
    fn test_poly() -> Result<()> {
        let input = r#"
           infixl 8 +;
           let id = \a => a
           in let double = \f a => f (f a)
              in let inc = \n => n + 1
                 in let not = \b => if b then false else true
                    in if double not (id false)
                       then id (double inc 3)
                       else double inc (id 7)
        "#;

        assert_eq!(typecheck_str(input)?, Type::Int);
        assert_eq!(eval_str(input)?, Term {kind: TermKind::Int(9)});

        Ok(())
    }

    #[test]
    fn test_free_vars() -> Result<()> {
        let input = r#"
           let f = \a => \b => a b
           in letrec g = \a => if true then g a else f g a
              in ()
        "#;

        let mut parser = parser::Parser::new(input.chars(), "tests".to_string());
        let sterm = parser.parse()?;
        let mut anal = Analyser::new();
        let (term, _) = anal.typecheck(&sterm)?;

        let fv = term.free_vars();
        assert!(fv.is_empty());

        if let TermKind::Let(_, t1, t2) = term.kind {
            let fv1 = t1.free_vars();
            assert!(fv1.is_empty());

            let fv2 = t2.free_vars();
            assert_eq!(fv2.len(), 1);
            assert!(fv2.iter().find(|v| v.name == "f").is_some());
        } else {
            panic!("term must be a 'let'");
        }

        Ok(())
    }
}
