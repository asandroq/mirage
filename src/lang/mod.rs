//! * Mirage's built-in programming language.

pub mod interp;
pub mod parser;

use crate::{
    collections::{nonemptyvec::NonEmptyVec, sharedlist::SharedList},
    error::{Error, Result},
};
use parser::Ast;
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet, VecDeque},
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
pub struct Variable {
    /// Variable name given in the source code.
    name: String,

    /// Serial number for creating unique variables.
    serial: usize,
}

impl Variable {
    fn new<S: ToString + ?Sized>(name: &S) -> Variable {
        let name = name.to_string();
        if name == "_" {
            Variable { name, serial: 0 }
        } else {
            let serial = SYM_COUNTER.fetch_add(1, Ordering::Relaxed);
            Variable { name, serial }
        }
    }

    fn is_unused(&self) -> bool {
        self.name.starts_with('_')
    }
}

impl fmt::Debug for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}@{}", self.name, self.serial)
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.name.fmt(f)
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
    fn new(t: Type) -> TypeScheme {
        TypeScheme {
            ptype: t,
            vars: Vec::new(),
        }
    }
}

/// A typing context used to keep track of bound variables during type
/// checking.
pub type Ctx = SharedList<Variable>;

/// An environment used to keep track of values of bound variables
/// during evaluation.
pub type Env = SharedList<(Variable, Rc<Term>)>;

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
                _ => Err(Error::TypeMismatch(format!("Unknown type {}", ident))),
            },
            parser::Type::Func(ty1, ty2) => Ok(Type::Func(
                Box::new(Analyser::analyse_type(ty1)?),
                Box::new(Analyser::analyse_type(ty2)?),
            )),
            parser::Type::Tuple(fst, snd, rest) => Ok(Type::Tuple(
                Box::new(Analyser::analyse_type(fst)?),
                Box::new(Analyser::analyse_type(snd)?),
                rest.iter()
                    .map(Analyser::analyse_type)
                    .collect::<Result<Vec<_>>>()?,
            )),
        }
    }

    fn apply_subst(&mut self, subst: &TypeSubst) {
        for ts in self.sym_table.values_mut() {
            ts.ptype = ts.ptype.clone().apply(subst);
        }
    }

    fn unify(mut constraints: ConstrSet) -> Result<TypeSubst> {
        let mut subst = Vec::new();

        while let Some((lhs, rhs)) = constraints.pop() {
            if lhs != rhs {
                if let Type::Var(v) = lhs {
                    if rhs.vars().contains(&v) {
                        return Err(Error::InfiniteType(format!(
                            "Type variable {} refers to itself",
                            v
                        )));
                    }
                    subst_constraints(&mut constraints, &v, &rhs);
                    subst.push((v, rhs));
                } else if let Type::Var(v) = rhs {
                    if lhs.vars().contains(&v) {
                        return Err(Error::InfiniteType(format!(
                            "Type variable {} refers to itself",
                            v
                        )));
                    }
                    subst_constraints(&mut constraints, &v, &lhs);
                    subst.push((v, lhs));
                } else if let Type::Func(lhs1, lhs2) = lhs {
                    if let Type::Func(rhs1, rhs2) = rhs {
                        constraints.push((*lhs1, *rhs1));
                        constraints.push((*lhs2, *rhs2));
                    } else {
                        return Err(Error::TypeMismatch(format!(
                            "{:?} is not a function type",
                            rhs
                        )));
                    }
                } else if let Type::Tuple(lfst, lsnd, lrest) = lhs {
                    if let Type::Tuple(rfst, rsnd, rrest) = rhs {
                        constraints.push((*lfst, *rfst));
                        constraints.push((*lsnd, *rsnd));
                        for (l, r) in lrest.into_iter().zip(rrest.into_iter()) {
                            constraints.push((l, r));
                        }
                    } else {
                        return Err(Error::TypeMismatch(format!(
                            "{:?} is not a tuple type",
                            rhs
                        )));
                    }
                } else {
                    return Err(Error::TypeMismatch(format!(
                        "Cannot unify the types {:?} and {:?}",
                        lhs, rhs
                    )));
                }
            }
        }

        Ok(subst)
    }

    fn typecheck(&mut self, ast: &Ast) -> Result<(Rc<Term>, Type)> {
        self.convert_ast(ast, &SharedList::nil())
            .map(|(t, ty, _)| (t, ty))
    }

    fn typecheck_lambda(&mut self, vars: &NonEmptyVec<String>, body: &Ast) -> Result<(Rc<Term>, Type)> {
        let vars = vars.map(Variable::new);
        self.convert_lambda(vars, body, &SharedList::nil()).map(|(term, ttype, _)| (term, ttype))
    }

    #[allow(clippy::too_many_lines)]
    fn convert_ast(&mut self, ast: &Ast, ctx: &Ctx) -> Result<(Rc<Term>, Type, ConstrSet)> {
        match ast {
            Ast::Unit => Ok((
                Rc::new(Term {
                    kind: TermKind::Unit,
                }),
                Type::Unit,
                Vec::new(),
            )),
            Ast::Bool(b) => Ok((
                Rc::new(Term {
                    kind: TermKind::Bool(*b),
                }),
                Type::Bool,
                Vec::new(),
            )),
            Ast::Int(i) => Ok((
                Rc::new(Term {
                    kind: TermKind::Int(*i),
                }),
                Type::Int,
                Vec::new(),
            )),
            Ast::Var(n) => {
                let var = ctx.iter().find(|v| v.name == *n);
                if let Some(var) = var {
                    let ts = self.sym_table.get(&var).ok_or_else(|| {
                        Error::VariableNotFound(format!(
                            "Variable '{var}' was not found in symbol table"
                        ))
                    })?;

                    let ts = ts.clone();

                    // create fresh type variables for the free
                    // variables to allow polymorphism
                    let subst = ts
                        .vars
                        .into_iter()
                        .map(|v| (v, Type::Var(Variable::new("P"))))
                        .collect();

                    Ok((
                        Rc::new(Term {
                            kind: TermKind::Var(var.as_ref().clone()),
                        }),
                        ts.ptype.apply(&subst),
                        Vec::new(),
                    ))
                } else {
                    Err(Error::VariableNotFound(format!(
                        "Variable {n} is not in scope"
                    )))
                }
            }
            Ast::Lam(vars, body) => {
                let vars = vars.map(Variable::new);
                self.convert_lambda(vars, body, ctx)
            }
            Ast::App(s1, ss) => {
                let (t1, ty1, cs1) = self.convert_ast(s1, ctx)?;

                let (s2, ss) = ss.parts();
                let (t2, ty2, cs2) = self.convert_ast(s2, ctx)?;

                let mut ts = NonEmptyVec::new(t2);

                let mut tys = VecDeque::new();
                tys.push_front(ty2);

                let mut cs = ConstrSet::new();
                cs.extend(cs1.into_iter());
                cs.extend(cs2.into_iter());

                for s in ss {
                    let (t, ty, c) = self.convert_ast(s, ctx)?;
                    ts.push(t);
                    tys.push_front(ty);
                    cs.extend(c.into_iter());
                }

                let var = Type::Var(Variable::new("Y"));
                let mut func_ty = var.clone();
                for ty in tys {
                    func_ty = Type::Func(Box::new(ty), Box::new(func_ty));
                }

                cs.push((ty1, func_ty));
                let subst = Analyser::unify(cs.clone())?;
                self.apply_subst(&subst);

                Ok((
                    Rc::new(Term {
                        kind: TermKind::App(t1, ts),
                    }),
                    var.apply(&subst),
                    cs,
                ))
            }
            Ast::If(s1, s2, s3) => {
                let (t1, ty1, cs1) = self.convert_ast(s1, ctx)?;
                let (t2, ty2, cs2) = self.convert_ast(s2, ctx)?;
                let (t3, ty3, cs3) = self.convert_ast(s3, ctx)?;

                let mut cs = ConstrSet::new();
                cs.extend(cs1.into_iter());
                cs.extend(cs2.into_iter());
                cs.extend(cs3.into_iter());
                cs.push((ty1, Type::Bool));
                cs.push((ty2, ty3.clone()));

                let subst = Analyser::unify(cs.clone())?;
                self.apply_subst(&subst);

                Ok((
                    Rc::new(Term {
                        kind: TermKind::If(t1, t2, t3),
                    }),
                    ty3.apply(&subst),
                    cs,
                ))
            }
            Ast::Let(idents, expr, body) => {
                let vars = idents.map(Variable::new);
                let (var, mut rest) = vars.into_parts();

                // handle the case where the `let` expression is a lambda abstraction
                let (expr, ty1, cs1) = if let Some(lvar) = rest.next() {
                    let mut lvars = NonEmptyVec::new(lvar);
                    lvars.extend(rest);
                    self.convert_lambda(lvars, expr, ctx)?
                } else {
                    self.convert_ast(expr, ctx)?
                };

                let tvars = ty1
                    .vars()
                    .into_iter()
                    .filter(|v| {
                        ctx.iter().all(|v1| {
                            self.sym_table
                                .get(&v1)
                                .map_or(true, |ts| !ts.ptype.vars().contains(v))
                        })
                    })
                    .collect();
                let ts = TypeScheme {
                    ptype: ty1,
                    vars: tvars,
                };
                self.sym_table.insert(var.clone(), ts);

                let rib = NonEmptyVec::new(var.clone());
                let (body, ty2, cs2) = if var.is_unused() {
                    self.convert_ast(body, ctx)?
                } else {
                    let new_ctx = ctx.extend(rib.into_iter());
                    self.convert_ast(body, &new_ctx)?
                };

                let mut cs = cs1;
                cs.extend(cs2.into_iter());

                Ok((
                    Rc::new(Term {
                        kind: TermKind::Let(var, expr, body),
                    }),
                    ty2,
                    cs,
                ))
            }
            Ast::Letrec(v, oty, s1, s2) => {
                let var = Variable::new(v);
                let vty = oty
                    .as_ref()
                    .map_or(Ok(Type::Var(Variable::new("F"))), Analyser::analyse_type)?;
                let ts = TypeScheme::new(vty.clone());
                self.sym_table.insert(var.clone(), ts);

                let rib = NonEmptyVec::new(var.clone());
                let new_ctx = ctx.extend(rib.into_iter());
                let (t1, ty1, cs1) = self.convert_ast(s1, &new_ctx)?;
                let (t2, ty2, cs2) = self.convert_ast(s2, &new_ctx)?;

                let mut cs = ConstrSet::new();
                cs.extend(cs1.into_iter());
                cs.extend(cs2.into_iter());
                cs.push((vty, ty1));

                let subst = Analyser::unify(cs.clone())?;
                self.apply_subst(&subst);

                let fix = Rc::new(Term {
                    kind: TermKind::Fix(var.clone(), t1),
                });

                Ok((
                    Rc::new(Term {
                        kind: TermKind::Let(var, fix, t2),
                    }),
                    ty2.apply(&subst),
                    cs,
                ))
            }
            Ast::Tuple(fst, snd, rest) => {
                let (t1, ty1, cs1) = self.convert_ast(fst, ctx)?;
                let (t2, ty2, cs2) = self.convert_ast(snd, ctx)?;
                let ts_tys_css = rest
                    .iter()
                    .map(|t| self.convert_ast(t, ctx))
                    .collect::<Result<Vec<_>>>()?;

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
                    Rc::new(Term {
                        kind: TermKind::Tuple(t1, t2, ts),
                    }),
                    Type::Tuple(Box::new(ty1), Box::new(ty2), tys),
                    css,
                ))
            }
            Ast::TupleRef(i, t) => {
                let (t, ty, mut cs) = self.convert_ast(t, ctx)?;

                // create principal tuple type, the size of the
                // rest vector is just the smallest size that will
                // typecheck
                let fst = Type::Var(Variable::new("T"));
                let snd = Type::Var(Variable::new("T"));
                let len = (i + 1).saturating_sub(2);
                let mut rest = Vec::with_capacity(len);
                for _ in 0..len {
                    rest.push(Type::Var(Variable::new("T")));
                }

                let ttype = if *i == 0 {
                    fst.clone()
                } else if *i == 1 {
                    snd.clone()
                } else {
                    // unwrap is safe because i > 1, so rest is not empty
                    rest.last().map(Type::clone).unwrap()
                };
                let tuple_type = Type::Tuple(Box::new(fst), Box::new(snd), rest);

                cs.push((ty, tuple_type));

                let subst = Analyser::unify(cs.clone())?;
                self.apply_subst(&subst);

                Ok((
                    Rc::new(Term {
                        kind: TermKind::TupleRef(*i, t),
                    }),
                    ttype.apply(&subst),
                    cs,
                ))
            }
            Ast::BinOp(op, s1, s2) => {
                let (t1, ty1, cs1) = self.convert_ast(s1, ctx)?;
                let (t2, ty2, cs2) = self.convert_ast(s2, ctx)?;

                let info = self
                    .oper_table
                    .iter()
                    .find(|(o, _)| o == op)
                    .map(|(_, i)| i.clone())
                    .ok_or_else(|| Error::UnknownOperator(format!("Operator {} not found", op)))?;

                let mut cs = ConstrSet::new();
                cs.extend(cs1.into_iter());
                cs.extend(cs2.into_iter());
                cs.push((ty1, info.ltype));
                cs.push((ty2, info.rtype));

                let subst = Analyser::unify(cs.clone())?;
                self.apply_subst(&subst);

                Ok((
                    Rc::new(Term {
                        kind: TermKind::BinOp(op.clone(), t1, t2),
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
        ctx: &Ctx,
    ) -> Result<(Rc<Term>, Type, ConstrSet)> {
        for var in &vars {
            let ty = Type::Var(Variable::new("X"));
            let ts = TypeScheme::new(ty);
            self.sym_table.insert(var.clone(), ts);
        }
        let new_ctx = ctx.extend(vars.clone().into_iter());
        let (t, mut ttype, cs) = self.convert_ast(body, &new_ctx)?;

        let mut rvec = vars.clone().into_vec();
        rvec.reverse();
        for v in rvec {
            let ptype = self
                .sym_table
                .get(&v)
                .map(|ts| ts.ptype.clone())
                .ok_or_else(|| {
                    Error::VariableNotFound(format!("Variable {} was not found in symbol table", v))
                })?;
            ttype = Type::Func(Box::new(ptype), Box::new(ttype));
        }
        Ok((
            Rc::new(Term {
                kind: TermKind::Lam(vars, t),
            }),
            ttype,
            cs,
        ))
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
        let (term, _) = anal.typecheck(&sterm)?;

        let fv = term.free_vars();
        assert!(fv.is_empty());

        if let TermKind::Let(_, t1, t2) = &term.kind {
            let fv1 = t1.free_vars();
            assert!(fv1.is_empty());

            let fv2 = t2.free_vars();
            assert_eq!(fv2.len(), 1);
            assert!(fv2.iter().any(|v| v.name == "f"));
        } else {
            panic!("term must be a 'let'");
        }

        Ok(())
    }
}
