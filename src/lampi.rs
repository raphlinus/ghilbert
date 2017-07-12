// Copyright 2017 Raph Levien. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Manipulation of lambda-pi terms.

use std::fmt;
use std::collections::BTreeMap;

use lexer::{Lexer, Token};
use parser::{Info, ParseNode};

use self::Term::*;

#[derive(Clone, PartialEq, Eq)]
pub enum Term {
    /// Base case of kind hierarchy
    BaseType,
    /// Reference to constant in pool
    Const(Token),
    /// Reference to variable, 0-based de Bruijn number
    Var(usize),
    /// Type and body, variable is implicit thanks to de Bruijn
    Pi(Box<(Term, Term)>),
    /// Type and body, variable is implicit thanks to de Bruijn
    Lambda(Box<(Term, Term)>),
    /// Application
    App(Box<(Term, Term)>),
}

#[derive(Debug)]
pub enum Error {
    InconsistentParse,
    TypeNotTyped,
    PiBodyMustBeType,
    NotAFunction,
    ConstNotFound,
    TypeMismatch,
    NYI,
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut ctx = Vec::new();
        let mut cur = 0;
        self.fmt_rec(f, &mut ctx, &mut cur, None)
    }
}

impl Term {
    fn is_base_type(&self) -> bool {
        match *self {
            BaseType => true,
            _ => false,
        }
    }

    fn shift(&self, k: usize, n: usize) -> Term {
        match *self {
            Var(v) => {
                if v < k {
                    Var(v)
                } else {
                    Var(v + n)
                }
            }
            Pi(ref t_b) => Pi(Box::new((t_b.0.shift(k, n), t_b.1.shift(k + 1, n)))),
            Lambda(ref t_b) => Lambda(Box::new((t_b.0.shift(k, n), t_b.1.shift(k + 1, n)))),
            App(ref f_a) => App(Box::new((f_a.0.shift(k, n), f_a.1.shift(k, n)))),
            _ => self.clone(),
        }
    }

    fn subst(&self, k: usize, t: &Term) -> Term {
        match *self {
            Var(v) => {
                if v < k {
                    Var(v)
                } else if v == k {
                    t.shift(0, k)
                } else {
                    Var(v - 1)
                }
            }
            Pi(ref t_b) => Pi(Box::new((t_b.0.subst(k, t), t_b.1.subst(k + 1, t)))),
            Lambda(ref t_b) => Lambda(Box::new((t_b.0.subst(k, t), t_b.1.subst(k + 1, t)))),
            App(ref f_a) => App(Box::new((f_a.0.subst(k, t), f_a.1.subst(k, t)))),
            _ => self.clone(),
        }
    }

    fn fmt_rec(&self, f: &mut fmt::Formatter, ctx: &mut Vec<usize>, cur: &mut usize,
        lexer: Option<&Lexer>) -> fmt::Result
    {
        match *self {
            BaseType => write!(f, "Type"),
            Const(c) => {
                if let Some(l) = lexer {
                    write!(f, "{}", l.tok_str(c))
                } else {
                    write!(f, "c{}", c)
                }
            }
            Var(v) => {
                if v < ctx.len() {
                    write!(f, "x{}", ctx[ctx.len() - 1 - v])
                } else {
                    write!(f, "g{}", v - ctx.len())
                }
            }
            Pi(ref t_b) => {
                let vnum = *cur;
                *cur += 1;
                write!(f, "Πx{}:", vnum)?;
                t_b.0.fmt_rec(f, ctx, cur, lexer)?;
                write!(f, ".")?;
                ctx.push(vnum);
                t_b.1.fmt_rec(f, ctx, cur, lexer)?;
                ctx.pop();
                Ok(())
            }
            Lambda(ref t_b) => {
                let vnum = *cur;
                *cur += 1;
                write!(f, "λx{}:", vnum)?;
                t_b.0.fmt_rec(f, ctx, cur, lexer)?;
                write!(f, ".")?;
                ctx.push(vnum);
                t_b.1.fmt_rec(f, ctx, cur, lexer)?;
                ctx.pop();
                Ok(())
            }
            App(ref f_a) => {
                write!(f, "(")?;
                f_a.0.fmt_rec(f, ctx, cur, lexer)?;
                write!(f, " ")?;
                f_a.1.fmt_rec(f, ctx, cur, lexer)?;
                write!(f, ")")
            }
        }
    }

    pub fn from_parse_node(n: &ParseNode) -> Result<Term, Error> {
        let mut stack = Vec::new();
        Self::from_parse_node_rec(n, &mut stack)
    }

    fn from_parse_node_rec(n: &ParseNode, stack: &mut Vec<Token>) -> Result<Term, Error> {
        match n.info {
            Info::BaseType => Ok(BaseType),
            Info::Atom(a) => {
                let mut t = if let Some(v) = stack.iter().rev().position(|x| *x == a) {
                    Var(v)
                } else {
                    Const(a)
                };
                for child in &n.children {
                    let c = Self::from_parse_node_rec(child, stack)?;
                    t = App(Box::new((t, c)));
                }
                Ok(t)
            }
            Info::Lambda => {
                let var_name = get_var(&n.children[0])?;
                let ty = Self::from_parse_node_rec(&n.children[1], stack)?;
                stack.push(var_name);
                let body = Self::from_parse_node_rec(&n.children[2], stack)?;
                let _ = stack.pop();
                Ok(Lambda(Box::new((ty, body))))
            }
            Info::Pi => {
                let var_name = get_var(&n.children[0])?;
                let ty = Self::from_parse_node_rec(&n.children[1], stack)?;
                stack.push(var_name);
                let body = Self::from_parse_node_rec(&n.children[2], stack)?;
                let _ = stack.pop();
                Ok(Pi(Box::new((ty, body))))
            }
            _ => Err(Error::NYI)
        }
    }
}

pub fn check_type(term: &Term, consts: &BTreeMap<Token, Term>, stack: &mut Vec<Term>)
    -> Result<Term, Error>
{
    match *term {
        BaseType => Err(Error::TypeNotTyped),
        Const(c) => {
            if let Some(t) = consts.get(&c) {
                Ok(t.clone())
            } else {
                Err(Error::ConstNotFound)
            }
        }
        Var(v) => Ok(stack[stack.len() - v - 1].shift(0, v + 1)),
        Pi(ref t_b) => {
            stack.push(t_b.0.clone());
            let body_type = check_type(&t_b.1, consts, stack)?;
            let _ = stack.pop().unwrap();
            if body_type.is_base_type() {
                Ok(BaseType)
            } else {
                Err(Error::PiBodyMustBeType)
            }
        }
        Lambda(ref t_b) => {
            stack.push(t_b.0.clone());
            let body_type = check_type(&t_b.1, consts, stack)?;
            let arg_type = stack.pop().unwrap();
            Ok(Pi(Box::new((arg_type, body_type))))
        }
        App (ref f_a) => {
            let func_type = check_type(&f_a.0, consts, stack)?;
            let arg_type = check_type(&f_a.1, consts, stack)?;
            match func_type {
                Pi(ref t_b) => {
                    if arg_type != t_b.0 {
                        println!("type mismatch {:?} {:?}", &arg_type, &t_b.0);
                        return Err(Error::TypeMismatch);
                    }
                    Ok(t_b.1.subst(0, &f_a.1))
                }
                _ => {
                    Err(Error::NotAFunction)
                }
            }
        }
    }
}

/*
fn main() {
    let mut consts = Vec::new();
    let mut stack = Vec::new();
    consts.push(BaseType);  // nat
    consts.push(Const(0));  // 0
    consts.push(Pi(Box::new((Const(0), Const(0)))));  // succ
    let term = Lambda(Box::new((BaseType, 
        Lambda(Box::new((BaseType,
            Lambda(Box::new((Var(1),
                Lambda(Box::new((Const(0), Const(1))))
            )))
        )))
    )));
    println!("{:?}", check_type(&term, &consts, &mut stack));
}
*/

// should probably be a ParseNode method
fn get_var(node: &ParseNode) -> Result<Token, Error> {
    match node.info {
        Info::Var(tok) => Ok(tok),
        _ => Err(Error::InconsistentParse),
    }
}

fn get_atom(node: &ParseNode) -> Result<Token, Error> {
    match node.info {
        Info::Atom(tok) => Ok(tok),
        _ => Err(Error::InconsistentParse),
    }
}

pub struct Print<'a>(pub &'a Term, pub &'a Lexer<'a>);

impl<'a> fmt::Debug for Print<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut ctx = Vec::new();
        let mut cur = 0;
        self.0.fmt_rec(f, &mut ctx, &mut cur, Some(self.1))
    }
}
