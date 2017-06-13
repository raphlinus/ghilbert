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

//! State for a session (currently just a pass through a single proof file).

use std::collections::{BTreeMap, BTreeSet};

use lexer::Token;
use parser::{self, Info, Parser, ParseNode};
use unify::{self, Expr, Stmt};

/// Errors. This will get a lot more sophisticated, with reporting on
/// the location of the error in the file, details of the error, etc.
#[derive(Debug)]
pub enum Error {
    UnknownCommand,
    DuplicateKind,
    DuplicateVar,
    DuplicateTerm,
    DuplicateStmt,
    VarNotFound,
    ArityMismatch,
    KindMismatch,
    InconsistentParse,
    ParseError(parser::Error),
    UnifyError(unify::Error),
}

impl From<parser::Error> for Error {
    fn from(err: parser::Error) -> Error {
        Error::ParseError(err)
    }
}

impl From<unify::Error> for Error {
    fn from(err: unify::Error) -> Error {
        Error::UnifyError(err)
    }
}

type KindName = Token;

// We'll generalize this in some way to handle bound variables.
type TermArg = KindName;

pub struct Session<'a> {
    verbose: bool,
    parser: Parser<'a>,
    kinds: BTreeSet<KindName>,
    vars: BTreeMap<Token, KindName>,
    terms: BTreeMap<Token, (Vec<TermArg>, KindName)>,
    stmts: BTreeMap<Token, Stmt>,
}

// Should the following accessors be methods on ParseNode?

fn get_kind(node: &ParseNode) -> Result<KindName, Error> {
    match node.info {
        Info::Kind(tok) => Ok(tok),
        _ => Err(Error::InconsistentParse),
    }
}

fn get_var(node: &ParseNode) -> Result<Token, Error> {
    match node.info {
        Info::Var(tok) => Ok(tok),
        _ => Err(Error::InconsistentParse),
    }
}

fn get_const(node: &ParseNode) -> Result<Token, Error> {
    match node.info {
        Info::Const(tok) => Ok(tok),
        _ => Err(Error::InconsistentParse),
    }
}

fn get_step(node: &ParseNode) -> Result<Token, Error> {
    match node.info {
        Info::Step(tok) => Ok(tok),
        _ => Err(Error::InconsistentParse),
    }
}

fn get_atom(node: &ParseNode) -> Result<Token, Error> {
    match node.info {
        Info::Atom(tok) => Ok(tok),
        _ => Err(Error::InconsistentParse),
    }
}

impl<'a> Session<'a> {
    pub fn new(parser: Parser<'a>) -> Session<'a> {
        Session {
            verbose: true,
            parser,
            kinds: BTreeSet::new(),
            vars: BTreeMap::new(),
            terms: BTreeMap::new(),
            stmts: BTreeMap::new(),
        }
    }

    pub fn run(&mut self) -> Result<(), Error> {
        loop {
            match self.parser.parse_cmd() {
                Ok(cmd) => self.do_cmd(&cmd)?,
                Err(parser::Error::Eof) => return Ok(()),
                Err(e) => return Err(From::from(e)),
            }
        }
    }

    fn do_cmd(&mut self, cmd: &ParseNode) -> Result<(), Error> {
        if self.verbose {
            self.parser.dump_tree(cmd);
        }
        match cmd.info {
            Info::KindCmd => self.do_kind(&cmd.children)?,
            Info::VarCmd => self.do_var(&cmd.children)?,
            Info::TermCmd => self.do_term(&cmd.children)?,
            Info::AxiomCmd => self.do_axiom(&cmd.children)?,
            _ => return Err(Error::UnknownCommand),
        }
        Ok(())
    }

    fn do_kind(&mut self, children: &[ParseNode]) -> Result<(), Error> {
        let kind = get_kind(&children[0])?;
        if self.kinds.contains(&kind) {
            if self.verbose {
                println!("Duplicate kind {}", self.parser.tok_str(kind));
            }
            return Err(Error::DuplicateKind);
        }
        self.kinds.insert(kind);
        Ok(())
    }

    fn do_var(&mut self, children: &[ParseNode]) -> Result<(), Error> {
        let kind = get_kind(&children[1])?;
        for child in &children[0].children {
            let var = get_var(child)?;
            if self.vars.contains_key(&var) {
                if self.verbose {
                    println!("Duplicate var {}", self.parser.tok_str(var));
                }
                return Err(Error::DuplicateVar);
            }
            self.vars.insert(var, kind);
        }
        Ok(())
    }

    fn do_term(&mut self, children: &[ParseNode]) -> Result<(), Error> {
        let con = get_const(&children[0])?;
        if self.terms.contains_key(&con) {
            if self.verbose {
                println!("Duplicate term {}", self.parser.tok_str(con));
            }
            return Err(Error::DuplicateTerm);
        }
        // TODO: might also want to check for collisions between term and var namespaces
        let mut args = Vec::with_capacity(children[1].children.len());
        for arg in &children[1].children {
            // Discussion question: do we want the arg to be a var or a kind?
            // One reason we've used var is to distinguish bound from term vars.
            let var = get_var(arg)?;
            let kind = self.vars.get(&var).ok_or(Error::VarNotFound)?;
            args.push(*kind);
        }
        let kind = get_kind(&children[2])?;
        self.terms.insert(con, (args, kind));
        Ok(())
    }

    fn do_axiom(&mut self, children: &[ParseNode]) -> Result<(), Error> {
        let step = get_step(&children[0])?;
        if self.stmts.contains_key(&step) {
            if self.verbose {
                println!("Duplicate stmt {}", self.parser.tok_str(step));
            }
            return Err(Error::DuplicateStmt);
        }
        let mut hyps = Vec::with_capacity(children[1].children.len());
        let mut var_map = BTreeMap::new();
        for hyp in &children[1].children {
            let (expr, _kind) = self.term_to_expr(hyp, &mut var_map)?;
            hyps.push(expr);
        }
        let (concl, _kind) = self.term_to_expr(&children[2], &mut var_map)?;
        let n_var = var_map.len();
        let stmt = Stmt { n_var, hyps, concl };
        if self.verbose {
            println!("adding stmt {}: {:?}", self.parser.tok_str(step), &stmt);
        }
        self.stmts.insert(step, stmt);
        Ok(())
    }

    // Convert a term (as parse node) to an expr suitable for unification. This method also
    // verifies well-formedness.
    fn term_to_expr(&self, node: &ParseNode, var_map: &mut BTreeMap<Token, usize>)
        -> Result<(Expr, KindName), Error>
    {
        let atom = get_atom(node)?;
        if let Some(kind) = self.vars.get(&atom) {
            if !node.children.is_empty() {
                return Err(Error::ArityMismatch);
            }
            let new_var_id = var_map.len();
            let id = *var_map.entry(atom).or_insert(new_var_id);
            Ok((Expr::Var(id), *kind))
        } else if let Some(term) = self.terms.get(&atom) {
            let (ref args, kind) = *term;
            if node.children.len() != args.len() {
                return Err(Error::ArityMismatch);
            }
            let mut expr_args = Vec::with_capacity(args.len());
            for (arg, child) in args.iter().zip(node.children.iter()) {
                let (expr, kind) = self.term_to_expr(child, var_map)?;
                if kind != *arg {
                    return Err(Error::KindMismatch);
                }
                expr_args.push(expr);
            }
            Ok((Expr::Term { constructor: atom, children: expr_args }, kind))
        } else {
            Err(Error::InconsistentParse)
        }
    }
}
