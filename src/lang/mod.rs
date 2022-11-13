//! Mirage's built-in programming language.

pub mod ast;
pub mod interp;
pub mod parser;

use crate::{
    collections::{nonemptyvec::NonEmptyVec, sharedlist::SharedList},
    error::{Error, Result},
};
use ast::{Ast, AstKind};
use std::{
    borrow::Cow,
    collections::{hash_map::Entry, HashMap, HashSet, VecDeque},
    fmt,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

/// Fountain of serial numbers for symbols.
///
/// It starts at 1 because the serial number 0 is reserved for the
/// wildcard `_`.
static SYM_COUNTER: AtomicUsize = AtomicUsize::new(1);

/// Language variables.
///
/// Variables can stand for both values and types.
#[derive(Clone, Eq, Hash, PartialEq)]
pub enum Variable {
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
    fn global<S: ToString + ?Sized>(name: &S) -> Variable {
        Self::Global(name.to_string())
    }

    fn local<S: ToString + ?Sized>(name: &S) -> Variable {
        let name = name.to_string();
        if name == "_" {
            Variable::Local(name, 0)
        } else {
            Variable::Local(name, SYM_COUNTER.fetch_add(1, Ordering::Relaxed))
        }
    }

    fn name(&self) -> &str {
        match self {
            Self::Global(name) | Self::Local(name, _) => name,
        }
    }
}

impl fmt::Debug for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Global(name) => name.fmt(f),
            Self::Local(name, serial) => write!(f, "{}@{}", name, serial),
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

/// Language types.
///
/// The variable type is for types that have not been resolved yet.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Type {
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
                let s2 = ty2.vars();
                s1.extend(s2.into_iter());
                s1
            }
            Type::Tuple(f, s, r) => {
                let mut fv = f.vars();
                let sv = s.vars();
                let rv = r.iter().flat_map(Type::vars).collect::<HashSet<_>>();
                fv.extend(sv.into_iter());
                fv.extend(rv.into_iter());
                fv
            }
            Type::Var(v) => {
                let mut s = HashSet::with_capacity(1);
                s.insert(v.clone());
                s
            }
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
                rest.into_iter()
                    .map(|ty| ty.apply_one(var, ttype))
                    .collect(),
            ),
            Type::Var(v) => {
                if *var == v {
                    ttype.clone()
                } else {
                    Type::Var(v)
                }
            }
        }
    }

    /// Applies a type substitution.
    fn apply(self, subst: &TypeSubst) -> Type {
        subst
            .iter()
            .fold(self, |ttype, (v, ty)| ttype.apply_one(v, ty))
    }

    /// Prettify the type for displaying.
    ///
    /// Type variables are displayed as lowercase letters.
    fn prettify(&self) -> Cow<'static, str> {
        fn walk(ttype: &Type, var_map: &HashMap<Variable, char>) -> Cow<'static, str> {
            match ttype {
                Type::Unit => "()".into(),
                Type::Bool => "Bool".into(),
                Type::Int => "Int".into(),
                Type::Func(ty1, ty2) => {
                    let str1 = walk(ty1.as_ref(), var_map);
                    let str2 = walk(ty2.as_ref(), var_map);
                    if matches!(ty1.as_ref(), &Type::Func(..)) {
                        // function types associate to the right, so
                        // we need to group the left side if it's a
                        // function
                        format!("({str1}) -> {str2}").into()
                    } else {
                        format!("{str1} -> {str2}").into()
                    }
                }
                Type::Tuple(fst, snd, rest) => {
                    let fst = walk(fst.as_ref(), var_map);
                    let snd = walk(snd.as_ref(), var_map);
                    let rest = rest.iter().map(|t| walk(t, var_map));

                    let mut res = format!("({fst}, {snd}");
                    for t in rest {
                        res.push_str(&format!(", {t}"));
                    }
                    res.push(')');
                    res.into()
                }
                Type::Var(v) => {
                    let c = var_map.get(v).unwrap_or(&'?');
                    c.to_string().into()
                }
            }
        }

        walk(self, &self.vars().into_iter().zip('a'..='z').collect())
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.prettify())
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
    fn new(t: Type) -> Self {
        TypeScheme {
            ptype: t,
            vars: Vec::new(),
        }
    }

    fn new_var<S: ToString + ?Sized>(name: &S) -> Self {
        TypeScheme {
            ptype: Type::Var(Variable::local(name)),
            vars: Vec::new(),
        }
    }
}

type Rib = NonEmptyVec<(Variable, TypeScheme)>;

/// A typing context used to keep track of bound variables during type
/// checking.
#[derive(Clone, Debug)]
pub struct Ctx(VecDeque<Rib>);

impl Ctx {
    fn apply_subst(self, subst: &TypeSubst) -> Self {
        self.0
            .into_iter()
            .map(|rib| {
                rib.map(|(var, mut ts)| {
                    ts.ptype = ts.ptype.apply(subst);
                    (var, ts)
                })
            })
            .collect()
    }

    fn extend(&mut self, rib: Rib) {
        self.0.push_front(rib);
    }

    fn extend_one(&mut self, var: Variable, ts: TypeScheme) {
        self.0.push_front(NonEmptyVec::new((var, ts)));
    }

    fn find<F: Fn(&Variable) -> bool>(&self, f: F) -> Option<&(Variable, TypeScheme)> {
        self.iter().find(|(v, _)| f(v))
    }

    fn iter(&self) -> CtxIter<'_> {
        CtxIter {
            rib: None,
            ctx: self.0.iter(),
        }
    }

    fn new() -> Self {
        Self(VecDeque::new())
    }

    fn shrink(&mut self) -> Result<Rib> {
        self.0.pop_front().ok_or(Error::EmptyContext)
    }
}

impl From<Rib> for Ctx {
    fn from(rib: Rib) -> Self {
        Self(VecDeque::from([rib]))
    }
}

impl FromIterator<Rib> for Ctx {
    fn from_iter<T: IntoIterator<Item = Rib>>(iter: T) -> Self {
        Self(VecDeque::from_iter(iter))
    }
}

/// Iterator over variables in the context.
struct CtxIter<'a> {
    /// Iterator over a single rib.
    rib: Option<crate::collections::nonemptyvec::Iter<'a, (Variable, TypeScheme)>>,

    /// Iterator over the full context.
    ctx: ::std::collections::vec_deque::Iter<'a, Rib>,
}

impl<'a> Iterator for CtxIter<'a> {
    type Item = &'a (Variable, TypeScheme);

    fn next(&mut self) -> Option<Self::Item> {
        self.rib.as_mut().and_then(Iterator::next).or_else(|| {
            if let Some(next_rib) = self.ctx.next() {
                let mut iter = next_rib.iter();
                let next = iter.next();
                self.rib = Some(iter);
                next
            } else {
                None
            }
        })
    }
}

/// An environment used to keep track of values of bound variables
/// during evaluation.
pub type Env = SharedList<(Variable, Rc<Term>)>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstrSet(Vec<(Type, Type)>);

impl ConstrSet {
    /// Add a new constraint to the set.
    fn add(&mut self, lhs: Type, rhs: Type) {
        self.0.push((lhs, rhs));
    }

    /// Append all constraints of other set to this one.
    fn append(&mut self, mut cs: ConstrSet) {
        self.0.append(&mut cs.0);
    }

    /// Create a new constraints set.
    fn new() -> Self {
        Self(Vec::new())
    }

    /// Apply a type substitution to all types in a constraints set.
    fn subst_constraints(self, var: &Variable, ttype: &Type) -> Self {
        let vec = self
            .0
            .into_iter()
            .map(|(lhs, rhs)| {
                let lhs = lhs.apply_one(var, ttype);
                let rhs = rhs.apply_one(var, ttype);
                (lhs, rhs)
            })
            .collect();

        Self(vec)
    }

    fn unify(&self) -> Result<TypeSubst> {
        let mut cs = self.clone();
        let mut subst = Vec::new();
        while let Some((lhs, rhs)) = cs.0.pop() {
            if lhs != rhs {
                if let Type::Var(v) = lhs {
                    if rhs.vars().contains(&v) {
                        return Err(Error::InfiniteType(format!(
                            "Type variable {v} refers to itself",
                        )));
                    }
                    cs = cs.subst_constraints(&v, &rhs);
                    subst.push((v, rhs));
                } else if let Type::Var(v) = rhs {
                    if lhs.vars().contains(&v) {
                        return Err(Error::InfiniteType(format!(
                            "Type variable {v} refers to itself",
                        )));
                    }
                    cs = cs.subst_constraints(&v, &lhs);
                    subst.push((v, lhs));
                } else if let Type::Func(lhs1, lhs2) = lhs {
                    if let Type::Func(rhs1, rhs2) = rhs {
                        cs.0.push((*lhs1, *rhs1));
                        cs.0.push((*lhs2, *rhs2));
                    } else {
                        return Err(Error::TypeMismatch(
                            format!("{rhs} is not a function type",),
                        ));
                    }
                } else if let Type::Tuple(lfst, lsnd, lrest) = lhs {
                    if let Type::Tuple(rfst, rsnd, rrest) = rhs {
                        cs.0.push((*lfst, *rfst));
                        cs.0.push((*lsnd, *rsnd));
                        for (l, r) in lrest.into_iter().zip(rrest.into_iter()) {
                            cs.0.push((l, r));
                        }
                    } else {
                        return Err(Error::TypeMismatch(format!("{rhs} is not a tuple type",)));
                    }
                } else {
                    return Err(Error::TypeMismatch(format!(
                        "Cannot unify the types {lhs} and {rhs}",
                    )));
                }
            }
        }

        Ok(subst)
    }
}

type Typing = (Ctx, Rc<Term>, Type, ConstrSet);

/// Kinds of terms of the language.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TermKind {
    Unit,
    Bool(bool),
    Int(i64),
    Var(Variable),
    Lam(NonEmptyVec<Variable>, Rc<Term>),
    Clo(NonEmptyVec<Variable>, Rc<Term>, Env),
    Fix(Variable, Rc<Term>),
    App(Rc<Term>, NonEmptyVec<Rc<Term>>),
    If(Rc<Term>, Rc<Term>, Rc<Term>),
    Let(Variable, Rc<Term>, Rc<Term>),
    Tuple(Rc<Term>, Rc<Term>, Vec<Rc<Term>>),
    TupleRef(usize, Rc<Term>),
    BinOp(String, Rc<Term>, Rc<Term>),
}

impl fmt::Display for TermKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermKind::Unit => write!(f, "()"),
            TermKind::Bool(b) => write!(f, "{b}"),
            TermKind::Int(i) => write!(f, "{i}"),
            TermKind::Var(var) => write!(f, "{var}"),
            TermKind::Lam(vs, t) | TermKind::Clo(vs, t, _) => {
                let (head, tail) = vs.parts();
                write!(f, "λ{head}")?;
                for v in tail {
                    write!(f, " {v}")?;
                }
                write!(f, ".{t}")
            }
            TermKind::Fix(v, t) => write!(f, "fix(λ{v}. {t})"),
            TermKind::App(fun, args) => {
                write!(f, "({fun}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
            TermKind::If(t1, t2, t3) => write!(f, "if {t1} then {t2} else {t3}"),
            TermKind::Let(v, t1, t2) => write!(f, "let {v} = {t1} in {t2}"),
            TermKind::Tuple(fst, snd, rest) => {
                write!(f, "({fst}, {snd}")?;
                for t in rest {
                    write!(f, ", {t}")?;
                }
                write!(f, ")")
            }
            TermKind::TupleRef(i, t) => write!(f, "#{i}({t})"),
            TermKind::BinOp(op, lhs, rhs) => write!(f, "{lhs} {op} {rhs}"),
        }
    }
}

/// Language terms.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Term {
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
            }
            TermKind::Lam(vs, t) | TermKind::Clo(vs, t, _) => {
                let mut fv = t.free_vars();
                for v in vs {
                    fv.remove(v);
                }
                fv
            }
            TermKind::Fix(v, t) => {
                let mut fv = t.free_vars();
                fv.remove(v);
                fv
            }
            TermKind::App(fun, args) => {
                let mut fv1 = fun.free_vars();
                for a in args {
                    let fv2 = a.free_vars();
                    fv1.extend(fv2.into_iter());
                }
                fv1
            }
            TermKind::If(t1, t2, t3) => {
                let mut fv1 = t1.free_vars();
                let fv2 = t2.free_vars();
                let fv3 = t3.free_vars();
                fv1.extend(fv2.into_iter());
                fv1.extend(fv3.into_iter());
                fv1
            }
            TermKind::Let(v, t1, t2) => {
                let mut fv1 = t1.free_vars();
                let mut fv2 = t2.free_vars();
                fv2.remove(v);
                fv1.extend(fv2.into_iter());
                fv1
            }
            TermKind::Tuple(t1, t2, ts) => {
                let mut fv1 = t1.free_vars();
                let fv2 = t2.free_vars();
                let fvs = ts.iter().flat_map(|t| t.free_vars().into_iter());
                fv1.extend(fv2.into_iter());
                fv1.extend(fvs);
                fv1
            }
            TermKind::TupleRef(_, t) => t.free_vars(),
            TermKind::BinOp(_, lhs, rhs) => {
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

// Operators are just functions, but since we don't have
// multi-argument functions yet they will be implemented as special
// primitives for now
#[derive(Clone, Debug)]
struct OpInfo {
    ltype: Type,
    rtype: Type,
    ttype: Type,
}

type OperatorTable = Vec<(&'static str, OpInfo)>;

/// Performs semantic analysis
#[derive(Debug)]
struct Analyser {
    /// Table of known operators.
    oper_table: OperatorTable,
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
                    },
                ),
                (
                    "-",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Int,
                    },
                ),
                (
                    "*",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Int,
                    },
                ),
                (
                    "/",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Int,
                    },
                ),
                (
                    "==",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Bool,
                    },
                ),
                (
                    "<",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Bool,
                    },
                ),
                (
                    ">",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Bool,
                    },
                ),
                (
                    "<=",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Bool,
                    },
                ),
                (
                    ">=",
                    OpInfo {
                        ltype: Type::Int,
                        rtype: Type::Int,
                        ttype: Type::Bool,
                    },
                ),
            ],
        }
    }

    /// Converts type parse trees into actual types.
    fn analyse_type(src: &ast::Type) -> Result<Type> {
        match src {
            ast::Type::Unit => Ok(Type::Unit),
            ast::Type::Ident(ident) => match ident.as_ref() {
                "Bool" => Ok(Type::Bool),
                "Int" => Ok(Type::Int),
                _ => Err(Error::TypeMismatch(format!("Unknown type {}", ident))),
            },
            ast::Type::Func(ty1, ty2) => Ok(Type::Func(
                Box::new(Analyser::analyse_type(ty1)?),
                Box::new(Analyser::analyse_type(ty2)?),
            )),
            ast::Type::Tuple(fst, snd, rest) => Ok(Type::Tuple(
                Box::new(Analyser::analyse_type(fst)?),
                Box::new(Analyser::analyse_type(snd)?),
                rest.iter()
                    .map(Analyser::analyse_type)
                    .collect::<Result<Vec<_>>>()?,
            )),
        }
    }

    fn typecheck(&mut self, ast: &Ast, ctx: Ctx) -> Result<(Rc<Term>, Type)> {
        self.convert_ast(ast, ctx).map(|(_, t, ty, _)| (t, ty))
    }

    #[allow(clippy::too_many_lines)]
    fn convert_ast(&mut self, ast: &Ast, ctx: Ctx) -> Result<Typing> {
        match &ast.kind {
            AstKind::Unit => Ok((
                ctx,
                Rc::new(Term {
                    kind: TermKind::Unit,
                }),
                Type::Unit,
                ConstrSet::new(),
            )),
            AstKind::Bool(b) => Ok((
                ctx,
                Rc::new(Term {
                    kind: TermKind::Bool(*b),
                }),
                Type::Bool,
                ConstrSet::new(),
            )),
            AstKind::Int(i) => Ok((
                ctx,
                Rc::new(Term {
                    kind: TermKind::Int(*i),
                }),
                Type::Int,
                ConstrSet::new(),
            )),
            AstKind::Var(n) => {
                let (var, ts) = ctx.find(|v| v.name() == *n).cloned().ok_or_else(|| {
                    Error::VariableNotFound(format!("Variable '{n}' was not found in context"))
                })?;

                // create fresh type variables for the free
                // variables to allow polymorphism
                let subst = ts
                    .vars
                    .into_iter()
                    .map(|v| (v, Type::Var(Variable::local("P"))))
                    .collect();

                Ok((
                    ctx,
                    Rc::new(Term {
                        kind: TermKind::Var(var),
                    }),
                    ts.ptype.apply(&subst),
                    ConstrSet::new(),
                ))
            }
            AstKind::Lam(ast::Lambda { vars, body }) => {
                let vars = vars.as_ref().map(Variable::local);
                self.convert_lambda(vars, body, ctx)
            }
            AstKind::App(ast::App { oper, args }) => {
                let (ctx, t1, ty1, cs1) = self.convert_ast(oper, ctx)?;

                let (s2, ss) = args.parts();
                let (ctx, t2, ty2, cs2) = self.convert_ast(s2, ctx)?;

                let mut ts = NonEmptyVec::new(t2);

                let mut tys = VecDeque::new();
                tys.push_front(ty2);

                let mut cs = ConstrSet::new();
                cs.append(cs1);
                cs.append(cs2);

                let mut ctx = ctx;
                for s in ss {
                    let (next_ctx, t, ty, c) = self.convert_ast(s, ctx)?;
                    ts.push(t);
                    tys.push_front(ty);
                    cs.append(c);
                    ctx = next_ctx;
                }

                let var = Type::Var(Variable::local("Y"));
                let mut func_ty = var.clone();
                for ty in tys {
                    func_ty = Type::Func(Box::new(ty), Box::new(func_ty));
                }

                cs.add(ty1, func_ty);
                let subst = cs.unify()?;

                Ok((
                    ctx.apply_subst(&subst),
                    Rc::new(Term {
                        kind: TermKind::App(t1, ts),
                    }),
                    var.apply(&subst),
                    cs,
                ))
            }
            AstKind::If(ast::If {
                cond,
                conseq,
                alter,
            }) => {
                let (ctx, t1, ty1, cs1) = self.convert_ast(cond, ctx)?;
                let (ctx, t2, ty2, cs2) = self.convert_ast(conseq, ctx)?;
                let (ctx, t3, ty3, cs3) = self.convert_ast(alter, ctx)?;

                let mut cs = ConstrSet::new();
                cs.append(cs1);
                cs.append(cs2);
                cs.append(cs3);
                cs.add(ty1, Type::Bool);
                cs.add(ty2, ty3.clone());

                let subst = cs.unify()?;

                Ok((
                    ctx.apply_subst(&subst),
                    Rc::new(Term {
                        kind: TermKind::If(t1, t2, t3),
                    }),
                    ty3.apply(&subst),
                    cs,
                ))
            }
            AstKind::Let(ast::Let { vars, expr, body }) => {
                let vars = vars.as_ref().map(Variable::local);
                let (var, mut rest) = vars.into_parts();

                // handle the case where the `let` expression is a lambda abstraction
                let (mut ctx, expr, ty1, mut cs) = if let Some(lvar) = rest.next() {
                    let mut lvars = NonEmptyVec::new(lvar);
                    lvars.extend(rest);
                    self.convert_lambda(lvars, expr, ctx)?
                } else {
                    self.convert_ast(expr, ctx)?
                };

                // Only variables not bound in context can be
                // universally quantified
                let tvars = ty1
                    .vars()
                    .into_iter()
                    .filter(|v| {
                        ctx.find(|v2| v == v2)
                            .map_or(true, |(_, ts)| !ts.ptype.vars().contains(v))
                    })
                    .collect();
                let ts = TypeScheme {
                    ptype: ty1,
                    vars: tvars,
                };

                ctx.extend_one(var.clone(), ts);
                let (mut ctx, body, ty2, cs2) = self.convert_ast(body, ctx)?;
                ctx.shrink()?;

                cs.append(cs2);
                Ok((
                    ctx,
                    Rc::new(Term {
                        kind: TermKind::Let(var, expr, body),
                    }),
                    ty2,
                    cs,
                ))
            }
            AstKind::Letrec(ast::Letrec {
                var,
                vty,
                expr,
                body,
            }) => {
                let var = Variable::local(var);
                let var_type = vty.as_ref().map_or(
                    Ok(Type::Var(Variable::local("FIX"))),
                    Analyser::analyse_type,
                )?;
                let ts = TypeScheme::new(var_type.clone());

                let mut ctx = ctx;
                ctx.extend_one(var.clone(), ts);
                let (ctx, expr, expr_type, expr_cs) = self.convert_ast(expr, ctx)?;
                let (mut ctx, body, body_type, body_cs) = self.convert_ast(body, ctx)?;
                ctx.shrink()?;

                let mut cs = ConstrSet::new();
                cs.append(expr_cs);
                cs.append(body_cs);
                cs.add(var_type, expr_type);
                let subst = cs.unify()?;

                let fix = Rc::new(Term {
                    kind: TermKind::Fix(var.clone(), expr),
                });

                Ok((
                    ctx.apply_subst(&subst),
                    Rc::new(Term {
                        kind: TermKind::Let(var, fix, body),
                    }),
                    body_type.apply(&subst),
                    cs,
                ))
            }
            AstKind::Tuple(ast::Tuple { fst, snd, rest }) => {
                let (ctx, t1, ty1, cs1) = self.convert_ast(fst, ctx)?;
                let (ctx, t2, ty2, cs2) = self.convert_ast(snd, ctx)?;

                let mut css = ConstrSet::new();
                css.append(cs1);
                css.append(cs2);
                let (ctx, ts, tys, css) = rest.iter().try_fold(
                    (ctx, Vec::new(), Vec::new(), css),
                    |(ctx, mut ts, mut tys, mut css), ast| {
                        let (ctx, t, ty, cs) = self.convert_ast(ast, ctx)?;
                        ts.push(t);
                        tys.push(ty);
                        css.append(cs);
                        Ok::<_, Error>((ctx, ts, tys, css))
                    },
                )?;

                Ok((
                    ctx,
                    Rc::new(Term {
                        kind: TermKind::Tuple(t1, t2, ts),
                    }),
                    Type::Tuple(Box::new(ty1), Box::new(ty2), tys),
                    css,
                ))
            }
            AstKind::TupleRef(ast::TupleRef { index, tuple }) => {
                let (ctx, t, ty, mut cs) = self.convert_ast(tuple, ctx)?;

                // create principal tuple type, the size of the
                // rest vector is just the smallest size that will
                // typecheck
                let fst = Type::Var(Variable::local("T"));
                let snd = Type::Var(Variable::local("T"));
                let len = (index + 1).saturating_sub(2);
                let mut rest = Vec::with_capacity(len);
                for _ in 0..len {
                    rest.push(Type::Var(Variable::local("T")));
                }

                let ttype = if *index == 0 {
                    fst.clone()
                } else if *index == 1 {
                    snd.clone()
                } else {
                    // unwrap is safe because i > 1, so rest is not empty
                    rest.last().map(Type::clone).unwrap()
                };
                let tuple_type = Type::Tuple(Box::new(fst), Box::new(snd), rest);

                cs.add(ty, tuple_type);

                let subst = cs.unify()?;

                Ok((
                    ctx.apply_subst(&subst),
                    Rc::new(Term {
                        kind: TermKind::TupleRef(*index, t),
                    }),
                    ttype.apply(&subst),
                    cs,
                ))
            }
            AstKind::BinOp(ast::BinOp { oper, lhs, rhs }) => {
                let (ctx, t1, ty1, cs1) = self.convert_ast(lhs, ctx)?;
                let (ctx, t2, ty2, cs2) = self.convert_ast(rhs, ctx)?;

                let info = self
                    .oper_table
                    .iter()
                    .find(|(o, _)| o == oper)
                    .map(|(_, i)| i.clone())
                    .ok_or_else(|| Error::UnknownOperator(format!("Operator {oper} not found")))?;

                let mut cs = ConstrSet::new();
                cs.append(cs1);
                cs.append(cs2);
                cs.add(ty1, info.ltype);
                cs.add(ty2, info.rtype);

                let subst = cs.unify()?;

                Ok((
                    ctx.apply_subst(&subst),
                    Rc::new(Term {
                        kind: TermKind::BinOp(oper.clone(), t1, t2),
                    }),
                    info.ttype,
                    cs,
                ))
            }
        }
    }

    fn convert_lambda(
        &mut self,
        vars: NonEmptyVec<Variable>,
        body: &Ast,
        mut ctx: Ctx,
    ) -> Result<Typing> {
        let rib = vars.as_ref().map(|v| {
            let ty = Type::Var(Variable::local("X"));
            let ts = TypeScheme::new(ty);
            (v.clone(), ts)
        });
        ctx.extend(rib);
        let (mut ctx, t, mut ttype, cs) = self.convert_ast(body, ctx)?;

        let rib = ctx.shrink()?;
        let mut rvec = rib.into_vec();
        rvec.reverse();
        for (_, ts) in rvec {
            ttype = Type::Func(Box::new(ts.ptype), Box::new(ttype));
        }
        Ok((
            ctx,
            Rc::new(Term {
                kind: TermKind::Lam(vars, t),
            }),
            ttype,
            cs,
        ))
    }
}

#[derive(Clone, Debug)]
pub struct ModuleEntry {
    term: Rc<Term>,
    tscm: TypeScheme,
}

#[derive(Debug)]
pub struct Module {
    items: HashMap<Variable, ModuleEntry>,
}

impl Module {
    fn load(src: &parser::Module) -> Result<Self> {
        let mut scope = HashMap::new();

        // check for duplicate names in the module scope
        for (names, ast) in &src.decls {
            let (name, args) = names.parts();
            let var = Variable::global(name);
            let args = args.map(Variable::local);
            if let Entry::Vacant(e) = scope.entry(var) {
                e.insert((args, ast));
            } else {
                return Err(Error::DuplicateGlobal(name.clone()));
            }
        }

        let mut rib_iter = scope
            .keys()
            .map(|var| (var.clone(), TypeScheme::new_var("M")));

        let items = if let Some((var, ts)) = rib_iter.next() {
            let mut rib = NonEmptyVec::new((var, ts));
            rib.extend(rib_iter);

            let ctx = rib.into();
            let mut anal = Analyser::new();
            let (_, items) = scope.into_iter().try_fold(
                (ctx, HashMap::new()),
                |(ctx, mut items), (var, (mut args, ast))| {
                    let (ctx, expr, ty, _) = if let Some(lvar) = args.next() {
                        let mut lvars = NonEmptyVec::new(lvar);
                        lvars.extend(args);
                        anal.convert_lambda(lvars, ast, ctx)?
                    } else {
                        anal.convert_ast(ast, ctx)?
                    };

                    // Only variables not bound in context can be
                    // universally quantified
                    let tvars = ty
                        .vars()
                        .into_iter()
                        .filter(|v| {
                            ctx.find(|v2| v == v2)
                                .map_or(true, |(_, ts)| !ts.ptype.vars().contains(v))
                        })
                        .collect();
                    let tscm = TypeScheme {
                        ptype: ty,
                        vars: tvars,
                    };

                    // All top-level values can refer to themselves.
                    let term = Rc::new(Term {
                        kind: TermKind::Fix(var.clone(), expr),
                    });
                    let entry = ModuleEntry { term, tscm };
                    items.insert(var, entry);
                    Ok::<_, Error>((ctx, items))
                },
            )?;
            items
        } else {
            HashMap::new()
        };

        Ok(Module { items })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use parser::ParserCtx;

    fn typecheck_str(src: &str) -> Result<Type> {
        let mut ctx = ParserCtx::new();
        let mut parser = parser::Parser::new(&mut ctx, src.chars(), "tests".to_string());
        let sterm = parser.parse()?;

        let mut anal = Analyser::new();
        let (_, ttype) = anal.typecheck(&sterm, Ctx::new())?;

        Ok(ttype)
    }

    #[test]
    fn test_typecheck() -> Result<()> {
        assert_eq!(typecheck_str("false")?, Type::Bool);
        assert_eq!(typecheck_str("true")?, Type::Bool);

        assert_eq!(typecheck_str("let x = false in x")?, Type::Bool);
        assert_eq!(typecheck_str("let y = true in y")?, Type::Bool);
        assert_eq!(typecheck_str("if false then true else false")?, Type::Bool);

        assert!(matches!(
            typecheck_str(r#"if true then \x => false else \z => true"#)?,
            Type::Func(_, _)
        ));

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

    #[test]
    fn test_free_vars() -> Result<()> {
        let input = r#"
           let f = \a => \b => a b
           in letrec g = \a => if true then g a else f g a
              in ()
        "#;

        let mut ctx = ParserCtx::new();
        let mut parser = parser::Parser::new(&mut ctx, input.chars(), "tests".to_string());
        let sterm = parser.parse()?;
        let mut anal = Analyser::new();
        let (term, _) = anal.typecheck(&sterm, Ctx::new())?;

        let fv = term.free_vars();
        assert!(fv.is_empty());

        if let TermKind::Let(_, t1, t2) = &term.kind {
            let fv1 = t1.free_vars();
            assert!(fv1.is_empty());

            let fv2 = t2.free_vars();
            assert_eq!(fv2.len(), 1);
            assert!(fv2.iter().any(|v| v.name() == "f"));
        } else {
            panic!("term must be a 'let'");
        }

        Ok(())
    }
}
