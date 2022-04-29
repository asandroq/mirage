use super::{parser::Ast, Analyser, Term, Type};
use crate::{
    collections::{sharedlist::SharedList, nonemptyvec::NonEmptyVec},
    error::{Error, Result},
    lang::{
        parser::{Parser, ParserCtx},
        Env, TermKind, Variable,
    },
};
use std::{
    collections::{hash_map::Entry,HashMap, VecDeque},
    rc::Rc,
};

#[derive(Debug)]
pub struct Interpreter {
    /// Global namespace.
    globals: HashMap<String, (Rc<Term>, Type)>,

    /// Persistent parser context.
    parser_ctx: ParserCtx,
}

impl Interpreter {
    pub fn new() -> Self {
        Interpreter {
            globals: HashMap::new(),
            parser_ctx: ParserCtx::new(),
        }
    }

    pub fn load_prelude(&mut self) -> Result<()> {
        let mut parser = Parser::new(&mut self.parser_ctx, PRELUDE.chars(), "prelude".to_string());
        let module = parser.parse_module()?;
        let mut anal = Analyser::new();
        for (vars, ast) in module.decls {
            self.load_decl(&mut anal, vars, &ast)?;
        }

        Ok(())
    }

    fn load_decl(&mut self, anal: &mut Analyser, vars: NonEmptyVec<String>, ast: &Ast) -> Result<()> {
        let (var, mut rest) = vars.into_parts();
        if let Entry::Vacant(e) = self.globals.entry(var.clone()) {
            let (term, ttype) = if let Some(lvar) = rest.next() {
                let mut lvars = NonEmptyVec::new(lvar);
                lvars.extend(rest);
                anal.typecheck_lambda(&lvars, ast)?
            } else {
                anal.typecheck(ast)?
            };
            e.insert((term, ttype));
            Ok(())
        } else {
            Err(Error::DuplicateGlobal(var))
        }
    }

    #[allow(clippy::too_many_lines)]
    fn eval_term(&self, term: &Rc<Term>, env: &Env) -> Result<Rc<Term>> {
        match &term.kind {
            TermKind::Unit | TermKind::Bool(..) | TermKind::Int(..) | TermKind::Clo(..) => {
                Ok(Rc::clone(term))
            }
            TermKind::Var(v) => {
                let fix_or_val = lookup(v, env).or_else(|_| {
                    self.globals
                        .get(&v.name)
                        .map(|(term, _)| Rc::clone(term))
                        .ok_or_else(|| Error::RuntimeError(format!("Variable {v} not found")))
                })?;
                if let Term {
                    kind: TermKind::Fix(..),
                } = fix_or_val.as_ref()
                {
                    // Given the "infinite" nature of fix, we need to keep re-evaluating it
                    self.eval_term(&fix_or_val, env)
                } else {
                    Ok(fix_or_val)
                }
            }
            TermKind::Lam(v, body) => {
                let fv = term
                    .free_vars()
                    .into_iter()
                    .map(|var| {
                        let val = lookup(&var, env)?;
                        Ok((var, val))
                    })
                    .collect::<Result<Vec<_>>>()?;
                let clo_env = SharedList::nil().extend(fv.into_iter());
                Ok(Rc::new(Term {
                    kind: TermKind::Clo(v.clone(), Rc::clone(body), clo_env),
                }))
            }
            TermKind::Fix(v, body) => {
                let new_env = env.cons((v.clone(), Rc::clone(term)));
                self.eval_term(body, &new_env)
            }
            TermKind::App(fun, args) => {
                let mut val = self.eval_term(fun, env)?;
                let mut args_q = args.iter().collect::<VecDeque<_>>();
                while !args_q.is_empty() {
                    if let TermKind::Clo(vars, body, clo_env) = &val.kind {
                        let (v1, vs) = vars.parts();
                        let a1 = args_q.pop_front().unwrap();
                        let e1 = self.eval_term(a1, env)?;
                        let mut new_env = clo_env.cons((v1.clone(), e1));
                        for v in vs {
                            let a = args_q.pop_front().ok_or_else(|| {
                                Error::RuntimeError(
                                    "insufficient number of arguments given to closure".to_string(),
                                )
                            })?;
                            let e = self.eval_term(a, env)?;
                            new_env = new_env.cons((v.clone(), e));
                        }
                        val = self.eval_term(body, &new_env)?;
                    } else {
                        return Err(Error::RuntimeError(format!(
                            "term {val} is not a closure but is being applied"
                        )));
                    }
                }
                Ok(val)
            }
            TermKind::If(t1, t2, t3) => {
                let guard = self.eval_term(t1, env)?;
                if let TermKind::Bool(b) = guard.kind {
                    if b {
                        self.eval_term(t2, env)
                    } else {
                        self.eval_term(t3, env)
                    }
                } else {
                    Err(Error::RuntimeError(format!(
                        "`if` guard must be a boolean, but {:?} was given",
                        guard
                    )))
                }
            }
            TermKind::Let(v, expr, body) => {
                let arg = self.eval_term(expr, env)?;
                let new_env = env.cons((v.clone(), arg));
                self.eval_term(body, &new_env)
            }
            TermKind::Tuple(fst, snd, rest) => {
                let fst = self.eval_term(fst, env)?;
                let snd = self.eval_term(snd, env)?;
                let rest = rest
                    .iter()
                    .map(|t| self.eval_term(t, env))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Rc::new(Term {
                    kind: TermKind::Tuple(fst, snd, rest),
                }))
            }
            TermKind::TupleRef(i, t) => {
                let v = self.eval_term(t, env)?;
                if let TermKind::Tuple(fst, snd, rest) = &v.kind {
                    if *i == 0 {
                        Ok(Rc::clone(fst))
                    } else if *i == 1 {
                        Ok(Rc::clone(snd))
                    } else {
                        Ok(Rc::clone(&rest[*i - 2]))
                    }
                } else {
                    Err(Error::RuntimeError(format!(
                        "Cannot index non-tuple {:?}",
                        v
                    )))
                }
            }
            TermKind::BinOp(op, t1, t2) => {
                let e1 = self.eval_term(t1, env)?;
                if let TermKind::Int(lhs) = e1.kind {
                    let e2 = self.eval_term(t2, env)?;
                    if let TermKind::Int(rhs) = e2.kind {
                        match op.as_str() {
                            "+" => Ok(Rc::new(Term {
                                kind: TermKind::Int(lhs + rhs),
                            })),
                            "-" => Ok(Rc::new(Term {
                                kind: TermKind::Int(lhs - rhs),
                            })),
                            "*" => Ok(Rc::new(Term {
                                kind: TermKind::Int(lhs * rhs),
                            })),
                            "/" => Ok(Rc::new(Term {
                                kind: TermKind::Int(lhs / rhs),
                            })),
                            "==" => Ok(Rc::new(Term {
                                kind: TermKind::Bool(lhs == rhs),
                            })),
                            "<" => Ok(Rc::new(Term {
                                kind: TermKind::Bool(lhs < rhs),
                            })),
                            ">" => Ok(Rc::new(Term {
                                kind: TermKind::Bool(lhs > rhs),
                            })),
                            "<=" => Ok(Rc::new(Term {
                                kind: TermKind::Bool(lhs <= rhs),
                            })),
                            ">=" => Ok(Rc::new(Term {
                                kind: TermKind::Bool(lhs >= rhs),
                            })),
                            _ => Err(Error::RuntimeError(format!("Unknown operator {op}"))),
                        }
                    } else {
                        Err(Error::RuntimeError(format!(
                            "Right-hand side of operator is not an integer, it's {:?}",
                            e2
                        )))
                    }
                } else {
                    Err(Error::RuntimeError(format!(
                        "Left-hand side of operator is not an integer, it's {:?}",
                        e1
                    )))
                }
            }
        }
    }

    pub fn eval(&mut self, input: &str, input_ctx: String) -> Result<(Term, Type)> {
        let mut parser = Parser::new(&mut self.parser_ctx, input.chars(), input_ctx);
        let sterm = parser.parse()?;
        let mut anal = Analyser::new();
        let (term, ttype) = anal.typecheck(&sterm)?;
        let val = self.eval_term(&term, &SharedList::nil())?;
        Ok((val.as_ref().clone(), ttype))
    }
}

fn lookup(var: &Variable, env: &Env) -> Result<Rc<Term>> {
    env.iter()
        .find_map(|rib| {
            let (v, t) = rib.as_ref();
            if v == var {
                Some(Rc::clone(t))
            } else {
                None
            }
        })
        .ok_or_else(|| Error::RuntimeError(format!("Variable {var} not found in environment")))
}

const PRELUDE: &str = r#"
infix 6 <,==;
infixl 8 +,-;
infixl 9 *,/;

let id x = x;

let twice f x = f (f x);
"#;

#[cfg(test)]
mod test {
    use super::Interpreter;
    use crate::{
        error::Result,
        lang::{Term, TermKind},
    };
    use std::rc::Rc;

    fn eval_str(input: &str) -> Result<Term> {
        let mut interp = Interpreter::new();
        let (val, _) = interp.eval(input, "tests".to_string())?;
        Ok(val)
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
           letrec f : (Bool, Bool, Bool) -> (Bool, Bool, Bool) = \a =>
                 if #2(a)
                    then f (true, true, false)
                    else if #1(a)
                         then f (true, false, false)
                         else if #0(a)
                                 then f (false, false, false)
                                 else (false, false, false)
              in f (true, true, true)
        "#;
        let t2 = eval_str(i2)?;
        let tfalse = Rc::new(Term {
            kind: TermKind::Bool(false),
        });
        let rfalse = vec![Rc::new(Term {
            kind: TermKind::Bool(false),
        })];
        assert!(matches!(
            t2.kind,
            TermKind::Tuple(fst, snd, rest) if fst == tfalse && snd == tfalse && rest == rfalse
        ));

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

        assert_eq!(
            eval_str(input)?,
            Term {
                kind: TermKind::Int(9)
            }
        );

        Ok(())
    }
}
