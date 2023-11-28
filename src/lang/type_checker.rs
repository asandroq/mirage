use super::{
    ast::{self, Ast, AstKind},
    term::{App, BinOp, Fix, If, Lambda, Let, Term, TermKind, Tuple, TupleRef},
    Pattern, Variable,
};
use crate::{
    collections::nonemptyvec::NonEmptyVec,
    error::{Error, Result},
};
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet, VecDeque},
    fmt::{self, Write},
    rc::Rc,
};

pub(crate) struct TypeChecker {
    oper_table: Vec<(&'static str, OpInfo)>,
}

impl TypeChecker {
    pub fn new() -> Self {
        let oper_table =
            vec![
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
            ];

        Self { oper_table }
    }

    pub fn check(&self, ast: &Ast, ctx: Ctx) -> Result<(Ctx, Rc<Term>, Type, ConstrSet)> {
        let (kind, ctx, ty, cs) = match &ast.kind {
            AstKind::Unit => (TermKind::Unit, ctx, Type::Unit, ConstrSet::new()),
            AstKind::Bool(b) => (TermKind::Bool(*b), ctx, Type::Bool, ConstrSet::new()),
            AstKind::Int(int) => (TermKind::Int(*int), ctx, Type::Int, ConstrSet::new()),
            AstKind::Var(name) => {
                let (var, ts) = ctx.find(|v| v.name() == name).cloned().ok_or_else(|| {
                    Error::VariableNotFound(format!("Variable '{name}' was not found in context"))
                })?;

                // create fresh type variables for allowing polymorphism
                let subst = ts
                    .vars
                    .into_iter()
                    .map(|v| (v, Type::Var(Variable::local("P"))))
                    .collect();

                (
                    TermKind::Var(var),
                    ctx,
                    ts.ptype.apply(&subst),
                    ConstrSet::new(),
                )
            }
            AstKind::Lam(ast::Lambda { vars, body }) => {
                let vars = vars.as_ref().map(Variable::local);
                let (ctx, lam, ty, cs) = self.check_lambda(vars, body, ctx)?;
                (TermKind::Lam(lam), ctx, ty, cs)
            }
            AstKind::App(app) => {
                let (ctx, app, ty, cs) = self.check_app(app, ctx)?;
                (TermKind::App(app), ctx, ty, cs)
            }
            AstKind::If(if_) => {
                let (ctx, if_, ty, cs) = self.check_if(if_, ctx)?;
                (TermKind::If(if_), ctx, ty, cs)
            }
            AstKind::Let(let_) => {
                let (ctx, let_, ty, cs) = self.check_let(let_, ctx)?;
                (TermKind::Let(let_), ctx, ty, cs)
            }
            AstKind::Letrec(letrec) => {
                let var = Variable::local(&letrec.var);
                let var_type = letrec
                    .vty
                    .as_ref()
                    .map_or(Ok(Type::Var(Variable::local("FIX"))), Self::convert_type)?;
                let ts = TypeScheme::new(var_type.clone());

                let mut ctx = ctx;
                ctx.extend_one(var.clone(), ts);
                let (ctx, expr, expr_type, expr_cs) = self.check(&letrec.expr, ctx)?;
                let (mut ctx, body, body_type, body_cs) = self.check(&letrec.body, ctx)?;
                ctx.shrink()?;

                let mut cs = ConstrSet::new();
                cs.append(expr_cs);
                cs.append(body_cs);
                cs.add(var_type, expr_type);
                let subst = cs.unify()?;

                let fix = Fix {
                    var: var.clone(),
                    body: expr,
                };
                let expr = Rc::new(Term {
                    kind: TermKind::Fix(fix),
                    span: ast.span,
                });
                let pat = Pattern::Var(var);

                (
                    TermKind::Let(Let { pat, expr, body }),
                    ctx.apply_subst(&subst),
                    body_type.apply(&subst),
                    cs,
                )
            }
            AstKind::Tuple(tuple) => {
                let (ctx, tuple, ty, cs) = self.check_tuple(tuple, ctx)?;
                (TermKind::Tuple(tuple), ctx, ty, cs)
            }
            AstKind::TupleRef(tuple_ref) => {
                let (ctx, tuple_ref, ty, cs) = self.check_tuple_ref(tuple_ref, ctx)?;
                (TermKind::TupleRef(tuple_ref), ctx, ty, cs)
            }
            AstKind::BinOp(bin_op) => {
                let (ctx, bin_op, ty, cs) = self.check_bin_op(bin_op, ctx)?;
                (TermKind::BinOp(bin_op), ctx, ty, cs)
            }
        };

        let term = Rc::new(Term {
            kind,
            span: ast.span,
        });

        Ok((ctx, term, ty, cs))
    }

    pub fn check_app(&self, app: &ast::App, ctx: Ctx) -> Result<(Ctx, App, Type, ConstrSet)> {
        let (ctx, oper, ty1, cs1) = self.check(&app.oper, ctx)?;

        let (first, ss) = app.args.parts();
        let (ctx, first, ty2, cs2) = self.check(first, ctx)?;

        let mut args = NonEmptyVec::new(first);

        let mut tys = VecDeque::new();
        tys.push_front(ty2);

        let mut cs = ConstrSet::new();
        cs.append(cs1);
        cs.append(cs2);

        let mut ctx = ctx;
        for s in ss {
            let (next_ctx, term, ty, c) = self.check(s, ctx)?;
            args.push(term);
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
            App { oper, args },
            var.apply(&subst),
            cs,
        ))
    }

    fn check_bin_op(&self, bin_op: &ast::BinOp, ctx: Ctx) -> Result<(Ctx, BinOp, Type, ConstrSet)> {
        let (ctx, lhs, lhs_ty, cs1) = self.check(&bin_op.lhs, ctx)?;
        let (ctx, rhs, rhs_ty, cs2) = self.check(&bin_op.rhs, ctx)?;

        let oper = bin_op.oper.clone();
        let info = self
            .oper_table
            .iter()
            .find(|(o, _)| *o == bin_op.oper)
            .map(|(_, i)| i.clone())
            .ok_or_else(|| Error::UnknownOperator(format!("Operator {oper} not found")))?;

        let mut cs = ConstrSet::new();
        cs.append(cs1);
        cs.append(cs2);
        cs.add(lhs_ty, info.ltype);
        cs.add(rhs_ty, info.rtype);

        let subst = cs.unify()?;

        Ok((
            ctx.apply_subst(&subst),
            BinOp { oper, lhs, rhs },
            info.ttype,
            cs,
        ))
    }

    fn check_if(&self, if_: &ast::If, ctx: Ctx) -> Result<(Ctx, If, Type, ConstrSet)> {
        let (ctx, cond, cond_ty, cond_cs) = self.check(&if_.cond, ctx)?;
        let (ctx, conseq, conseq_ty, conseq_cs) = self.check(&if_.conseq, ctx)?;
        let (ctx, alter, alter_ty, alter_cs) = self.check(&if_.alter, ctx)?;

        let mut cs = ConstrSet::new();
        cs.append(cond_cs);
        cs.append(conseq_cs);
        cs.append(alter_cs);
        cs.add(cond_ty, Type::Bool);
        cs.add(conseq_ty, alter_ty.clone());

        let subst = cs.unify()?;

        Ok((
            ctx.apply_subst(&subst),
            If {
                cond,
                conseq,
                alter,
            },
            alter_ty.apply(&subst),
            cs,
        ))
    }

    pub fn check_lambda(
        &self,
        vars: NonEmptyVec<Variable>,
        body: &Ast,
        mut ctx: Ctx,
    ) -> Result<(Ctx, Lambda, Type, ConstrSet)> {
        let rib = vars.as_ref().map(|v| {
            let ty = Type::Var(Variable::local("X"));
            let ts = TypeScheme::new(ty);
            (v.clone(), ts)
        });
        ctx.extend(rib);
        let (mut ctx, body, mut ty, cs) = self.check(body, ctx)?;

        let rib = ctx.shrink()?;
        let mut rvec = rib.into_vec();
        rvec.reverse();
        for (_, ts) in rvec {
            ty = Type::Func(Box::new(ts.ptype), Box::new(ty));
        }

        let subst = cs.unify()?;
        let lam = Lambda { vars, body };
        Ok((ctx.apply_subst(&subst), lam, ty.apply(&subst), cs))
    }

    fn check_let(&self, let_: &ast::Let, ctx: Ctx) -> Result<(Ctx, Let, Type, ConstrSet)> {
        let (mut ctx, expr, expr_ty, mut cs) = self.check(&let_.expr, ctx)?;

        let pat = let_.pat.map(Variable::local);
        let (rib, match_cs) = Self::match_pattern(&pat, expr_ty, &ctx)?;
        ctx.extend(rib);
        let (mut ctx, body, body_ty, body_cs) = self.check(&let_.body, ctx)?;
        ctx.shrink()?;

        cs.append(body_cs);
        cs.append(match_cs);
        Ok((ctx, Let { pat, expr, body }, body_ty, cs))
    }

    fn check_tuple(&self, tuple: &ast::Tuple, ctx: Ctx) -> Result<(Ctx, Tuple, Type, ConstrSet)> {
        let (ctx, fst, fst_ty, cs1) = self.check(&tuple.fst, ctx)?;
        let (ctx, snd, snd_ty, cs2) = self.check(&tuple.snd, ctx)?;

        let mut css = ConstrSet::new();
        css.append(cs1);
        css.append(cs2);
        let (ctx, rest, tys, css) =
            tuple.rest.iter().try_fold(
                (ctx, Vec::new(), Vec::new(), css),
                |(ctx, mut ts, mut tys, mut css), ast| {
                    let (ctx, t, ty, cs) = self.check(ast, ctx)?;
                    ts.push(t);
                    tys.push(ty);
                    css.append(cs);
                    Ok::<_, Error>((ctx, ts, tys, css))
                },
            )?;

        Ok((
            ctx,
            Tuple { fst, snd, rest },
            Type::Tuple(Box::new(fst_ty), Box::new(snd_ty), tys),
            css,
        ))
    }

    fn check_tuple_ref(
        &self,
        tuple_ref: &ast::TupleRef,
        ctx: Ctx,
    ) -> Result<(Ctx, TupleRef, Type, ConstrSet)> {
        let (ctx, tuple, tuple_ty, mut cs) = self.check(&tuple_ref.tuple, ctx)?;

        // create principal tuple type, the size of the rest vector is just the smallest size that
        // will typecheck
        let index = tuple_ref.index;
        let fst = Type::Var(Variable::local("T"));
        let snd = Type::Var(Variable::local("T"));
        let len = (index + 1).saturating_sub(2);
        let mut rest = Vec::with_capacity(len);
        for _ in 0..len {
            rest.push(Type::Var(Variable::local("T")));
        }

        let ref_ty = if index == 0 {
            fst.clone()
        } else if index == 1 {
            snd.clone()
        } else {
            // unwrap is safe because index > 1, so rest is not empty
            rest.last().map(Type::clone).unwrap()
        };
        let syn_ty = Type::Tuple(Box::new(fst), Box::new(snd), rest);

        cs.add(tuple_ty, syn_ty);

        let subst = cs.unify()?;

        Ok((
            ctx.apply_subst(&subst),
            TupleRef { index, tuple },
            ref_ty.apply(&subst),
            cs,
        ))
    }

    fn convert_type(ast: &ast::Type) -> Result<Type> {
        match ast {
            ast::Type::Unit => Ok(Type::Unit),
            ast::Type::Ident(ident) => match ident.as_ref() {
                "Bool" => Ok(Type::Bool),
                "Int" => Ok(Type::Int),
                _ => Err(Error::TypeMismatch(format!("Unknown type {ident}"))),
            },
            ast::Type::Func(ty1, ty2) => Ok(Type::Func(
                Box::new(Self::convert_type(ty1)?),
                Box::new(Self::convert_type(ty2)?),
            )),
            ast::Type::Tuple(fst, snd, rest) => Ok(Type::Tuple(
                Box::new(Self::convert_type(fst)?),
                Box::new(Self::convert_type(snd)?),
                rest.iter()
                    .map(Self::convert_type)
                    .collect::<Result<Vec<_>>>()?,
            )),
        }
    }

    fn match_pattern(
        pat: &Pattern<Variable>,
        expr_ty: Type,
        ctx: &Ctx,
    ) -> Result<(NonEmptyVec<(Variable, TypeScheme)>, ConstrSet)> {
        match pat {
            Pattern::Var(var) => {
                // Only variables not bound in context can be
                // universally quantified
                let tvars = expr_ty
                    .vars()
                    .into_iter()
                    .filter(|v| {
                        ctx.find(|v2| v == v2)
                            .map_or(true, |(_, ts)| !ts.ptype.vars().contains(v))
                    })
                    .collect();

                let ts = TypeScheme {
                    ptype: expr_ty,
                    vars: tvars,
                };

                Ok((NonEmptyVec::new((var.clone(), ts)), ConstrSet::new()))
            }
            Pattern::Tuple(fst, snd, rest) => {
                let (fst_ty, snd_ty, rest_ty, mut cs) = match expr_ty {
                    Type::Var(var) => {
                        // create principal tuple type
                        let fst_ty = Type::Var(Variable::local("T"));
                        let snd_ty = Type::Var(Variable::local("T"));
                        let rest_ty = rest
                            .iter()
                            .map(|_| Type::Var(Variable::local("T")))
                            .collect::<Vec<_>>();
                        let tuple_ty = Type::Tuple(
                            Box::new(fst_ty.clone()),
                            Box::new(snd_ty.clone()),
                            rest_ty.clone(),
                        );

                        // Add constraint that `var` is a tuple type
                        let mut cs = ConstrSet::new();
                        cs.add(Type::Var(var), tuple_ty);

                        Ok((fst_ty, snd_ty, rest_ty, cs))
                    }
                    Type::Tuple(fst_ty, snd_ty, rest_ty) => {
                        if rest.len() == rest_ty.len() {
                            Ok((*fst_ty, *snd_ty, rest_ty, ConstrSet::new()))
                        } else {
                            Err(Error::PatternMatch(format!(
                                "Tuple pattern has {} elements but expression type has {}",
                                rest.len() + 2,
                                rest_ty.len() + 2
                            )))
                        }
                    }
                    _ => {
                        Err(Error::PatternMatch("Expression doesn't have a tuple type".to_string()))
                    }
                }?;

                let (mut matches, fst_cs) = Self::match_pattern(fst, fst_ty, ctx)?;
                let (snd_matches, snd_cs) = Self::match_pattern(snd, snd_ty, ctx)?;
                matches.extend(snd_matches);

                cs.append(fst_cs);
                cs.append(snd_cs);

                for (pat, ty) in rest.iter().zip(rest_ty.into_iter()) {
                    let (next_match, next_cs) = Self::match_pattern(pat, ty, ctx)?;
                    matches.extend(next_match);
                    cs.append(next_cs);
                }

                Ok((matches, cs))
            }
        }
    }

    pub fn typecheck(&self, ast: &Ast, ctx: Ctx) -> Result<(Rc<Term>, Type)> {
        let (_, term, ty, _) = self.check(ast, ctx)?;
        Ok((term, ty))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ConstrSet(Vec<(Type, Type)>);

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
        let vec =
            self.0
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
                        return Err(
                            Error::InfiniteType(format!("Type variable {v} refers to itself",))
                        );
                    }
                    cs = cs.subst_constraints(&v, &rhs);
                    subst.push((v, rhs));
                } else if let Type::Var(v) = rhs {
                    if lhs.vars().contains(&v) {
                        return Err(
                            Error::InfiniteType(format!("Type variable {v} refers to itself",))
                        );
                    }
                    cs = cs.subst_constraints(&v, &lhs);
                    subst.push((v, lhs));
                } else if let Type::Func(lhs1, lhs2) = lhs {
                    if let Type::Func(rhs1, rhs2) = rhs {
                        cs.0.push((*lhs1, *rhs1));
                        cs.0.push((*lhs2, *rhs2));
                    } else {
                        return Err(Error::TypeMismatch(format!("{rhs} is not a function type",)));
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
                    return Err(
                        Error::TypeMismatch(format!("Cannot unify the types {lhs} and {rhs}",))
                    );
                }
            }
        }

        Ok(subst)
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

/// Language types.
///
/// The variable type is for types that have not been resolved yet.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Type {
    Unit,
    Bool,
    Int,
    Func(Box<Type>, Box<Type>),
    Tuple(Box<Type>, Box<Type>, Vec<Type>),
    Var(Variable),
}

impl Type {
    /// Collect all variables contained in type
    pub fn vars(&self) -> HashSet<Variable> {
        match self {
            Type::Unit | Type::Bool | Type::Int => HashSet::new(),
            Type::Func(ty1, ty2) => {
                let mut s1 = ty1.vars();
                let s2 = ty2.vars();
                s1.extend(s2);
                s1
            }
            Type::Tuple(f, s, r) => {
                let mut fv = f.vars();
                let sv = s.vars();
                let rv = r.iter().flat_map(Type::vars).collect::<HashSet<_>>();
                fv.extend(sv);
                fv.extend(rv);
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
                        write!(res, ", {t}").expect("Failed to write formatted type into string");
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

/// A type scheme is a polymorphic type with free variables.
#[derive(Clone, Debug)]
pub(crate) struct TypeScheme {
    /// Principal type.
    pub ptype: Type,

    /// Free type variables.
    pub vars: Vec<Variable>,
}

impl TypeScheme {
    fn new(t: Type) -> Self {
        TypeScheme {
            ptype: t,
            vars: Vec::new(),
        }
    }

    pub fn new_var(name: impl Into<String>) -> Self {
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
pub(crate) struct Ctx(VecDeque<Rib>);

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

    pub fn extend(&mut self, rib: Rib) {
        self.0.push_front(rib);
    }

    fn extend_one(&mut self, var: Variable, ts: TypeScheme) {
        self.0.push_front(NonEmptyVec::new((var, ts)));
    }

    pub fn find<F: Fn(&Variable) -> bool>(&self, f: F) -> Option<&(Variable, TypeScheme)> {
        self.iter().find(|(v, _)| f(v))
    }

    fn iter(&self) -> CtxIter<'_> {
        CtxIter {
            rib: None,
            ctx: self.0.iter(),
        }
    }

    pub fn new() -> Self {
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

/// Type substitutions must be applied in order.
pub(crate) type TypeSubst = Vec<(Variable, Type)>;

#[cfg(test)]
mod test {
    use super::{Ctx, Let, TermKind, Type, TypeChecker};
    use crate::{
        error::Result,
        lang::parser::{Parser, ParserCtx},
    };

    fn typecheck_str(src: &str) -> Result<Type> {
        let mut ctx = ParserCtx::new();
        let mut parser = Parser::new(&mut ctx, src.chars(), "tests".to_string());
        let sterm = parser.parse()?;

        let checker = TypeChecker::new();
        let (_, ttype) = checker.typecheck(&sterm, Ctx::new())?;

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
            typecheck_str(r"if true then \x => false else \z => true")?,
            Type::Func(_, _)
        ));

        let input = r"
           let x = false
           in let y = true
              in let z = false
                 in let and = \x y => if x then y else x
                    in if and x y then y else z
         ";
        assert_eq!(typecheck_str(input)?, Type::Bool);

        let unit = r"
           let f = \_ => false
           in let g = \x => if x then () else ()
              in g (f ())
        ";
        assert_eq!(typecheck_str(unit)?, Type::Unit);

        let int = r"
           let f = \x y => if (x y) then 42 else -998
           in let z = -132
              in let g = \_ => true
                 in f g z
        ";
        assert_eq!(typecheck_str(int)?, Type::Int);

        Ok(())
    }

    #[test]
    fn test_typecheck_tuple() -> Result<()> {
        let tuple1 = r"
           let x = (false, (), -526)
           in let y = ((), 42191, if true then 0 else 1)
              in let g = \t => if false then t else (true, (), 0)
                 in g x
        ";
        assert_eq!(
            typecheck_str(tuple1)?,
            Type::Tuple(Box::new(Type::Bool), Box::new(Type::Unit), vec![Type::Int])
        );

        let tuple2 = r"
           let f = \x => if #2(x) then #3(x) else #0(x)
           in f (-12132, (), true, 77)
        ";
        assert_eq!(typecheck_str(tuple2)?, Type::Int);

        Ok(())
    }

    #[test]
    fn test_free_vars() -> Result<()> {
        let input = r"
           let f = \a => \b => a b
           in letrec g = \a => if true then g a else f g a
              in ()
        ";

        let mut ctx = ParserCtx::new();
        let mut parser = Parser::new(&mut ctx, input.chars(), "tests".to_string());
        let sterm = parser.parse()?;
        let checker = TypeChecker::new();
        let (term, _) = checker.typecheck(&sterm, Ctx::new())?;

        let fv = term.free_vars();
        assert!(fv.is_empty());

        if let TermKind::Let(Let { pat: _, expr, body }) = &term.kind {
            let fv1 = expr.free_vars();
            assert!(fv1.is_empty());

            let fv2 = body.free_vars();
            assert_eq!(fv2.len(), 1);
            assert!(fv2.iter().any(|v| v.name() == "f"));
        } else {
            panic!("term must be a 'let'");
        }

        Ok(())
    }
}
