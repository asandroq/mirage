//! Mirage's built-in programming language.

pub mod ast;
pub mod interp;
pub mod parser;
pub mod term;
pub mod type_checker;

use self::{
    term::{Fix, Term, TermKind, Variable},
    type_checker::{Type, TypeChecker, TypeScheme},
};
use crate::{
    collections::nonemptyvec::NonEmptyVec,
    error::{Error, Result},
};
use std::{
    collections::{hash_map::Entry, HashMap, HashSet},
    fmt,
    rc::Rc,
};
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
            let checker = TypeChecker::new();
            let (_, items) = scope.into_iter().try_fold(
                (ctx, HashMap::new()),
                |(ctx, mut items), (var, (mut args, ast))| {
                    let (ctx, expr, ty, _) = if let Some(lvar) = args.next() {
                        let mut lvars = NonEmptyVec::new(lvar);
                        lvars.extend(args);
                        let (ctx, lam, ty, cs) = checker.check_lambda(lvars, ast, ctx)?;
                        let term = Term {
                            kind: TermKind::Lam(lam),
                            span: ast.span,
                        };
                        (ctx, Rc::new(term), ty, cs)
                    } else {
                        checker.check(ast, ctx)?
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
                        kind: TermKind::Fix(Fix {
                            var: var.clone(),
                            body: expr,
                        }),
                        span: ast.span,
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

/// Patterns for recursively binding variables.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Pattern<V> {
    /// A single-variable pattern, always matches.
    Var(V),

    /// A pattern that matches a tuple.
    Tuple(Box<Pattern<V>>, Box<Pattern<V>>, Vec<Pattern<V>>),
}

impl<V: fmt::Display> fmt::Display for Pattern<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pattern::Var(var) => var.fmt(f),
            Pattern::Tuple(fst, snd, rest) => {
                write!(f, "({fst}, {snd}")?;
                for pat in rest {
                    write!(f, ", {pat}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl<V> Pattern<V> {
    fn map<F, U>(&self, f: F) -> Pattern<U>
    where
        F: Copy + Fn(&V) -> U,
    {
        match self {
            Pattern::Var(var) => Pattern::Var(f(var)),
            Pattern::Tuple(fst, snd, rest) => {
                let fst = fst.map(f);
                let snd = snd.map(f);
                let rest = rest.iter().map(|pat| pat.map(f)).collect();

                Pattern::Tuple(Box::new(fst), Box::new(snd), rest)
            }
        }
    }
}

impl<V> Pattern<V>
where
    V: Clone + Eq + ::std::hash::Hash,
{
    fn vars(&self) -> HashSet<V> {
        match self {
            Pattern::Var(var) => {
                let mut set = HashSet::with_capacity(1);
                set.insert(var.clone());
                set
            }
            Pattern::Tuple(fst, snd, rest) => {
                let mut set = fst.vars();
                set.extend(snd.vars());

                for pat in rest {
                    set.extend(pat.vars());
                }

                set
            }
        }
    }
}
