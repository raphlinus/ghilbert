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
use prooflistener::{ProofListener};
use unify::{self, Definition, Expr, Graph, Stmt};

/// Errors. This will get a lot more sophisticated, with reporting on
/// the location of the error in the file, details of the error, etc.
#[derive(Debug)]
pub enum Error {
    UnknownCommand,
    DuplicateKind,
    DuplicateVar,
    DuplicateTerm,
    DuplicateStmt,
    DuplicateStep,
    VarNotFound,
    ArityMismatch,
    TypeMismatch,
    EmptyProof,
    StepNotFound,
    InconsistentParse,
    LambdaArgMustBind,
    NoRawBoundVars,
    NoTermMatching,
    DefCantBeLambda,
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

#[derive(Clone, Copy)]
enum VarType {
    TermVar(KindName),
    BoundVar(KindName),
}

/// The type a term can have.
///
/// A few notes. First, the naming is odd here, the base case should
/// probably not be called "kind". Second, this is purposefully a pretty
/// limited family of types for now; I hope to expand it.
#[derive(PartialEq, Eq)]
enum Type {
    Base(KindName),
    Arrow(KindName, Box<Type>),
}

pub struct Session<'a> {
    verbose: bool,
    parser: Parser<'a>,
    kinds: BTreeSet<KindName>,
    vars: BTreeMap<Token, VarType>,
    terms: BTreeMap<Token, (Vec<Type>, KindName)>,
    stmts: BTreeMap<Token, Stmt>,
    defs: BTreeMap<Token, Definition>,
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

fn get_type(node: &ParseNode) -> Result<Type, Error> {
    match node.info {
        Info::Kind(tok) => Ok(Type::Base(tok)),
        Info::Arrow => {
            let arg_kind = get_kind(&node.children[0])?;
            let result_ty = get_type(&node.children[1])?;
            Ok(Type::Arrow(arg_kind, Box::new(result_ty)))
        }
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
            defs: BTreeMap::new(),
        }
    }

    pub fn get_parser(&self) -> &Parser {
        &self.parser
    }

    pub fn run<L: ProofListener>(&mut self, listener: &mut L) -> Result<(), Error> {
        loop {
            match self.parser.parse_cmd() {
                Ok(cmd) => self.do_cmd(&cmd, listener)?,
                Err(parser::Error::Eof) => return Ok(()),
                Err(e) => return Err(From::from(e)),
            }
        }
    }

    fn do_cmd<L: ProofListener>(&mut self, cmd: &ParseNode, listener: &mut L)
        -> Result<(), Error>
    {
        if self.verbose {
            self.parser.dump_tree(cmd);
        }
        match cmd.info {
            Info::KindCmd => self.do_kind(&cmd.children)?,
            Info::VarCmd => self.do_var(&cmd.children, false)?,
            Info::BoundCmd => self.do_var(&cmd.children, true)?,
            Info::TermCmd => self.do_term(&cmd.children)?,
            Info::DefCmd => self.do_def(&cmd.children)?,
            Info::AxiomCmd => self.do_axiom(&cmd.children)?,
            Info::TheoremCmd => self.do_theorem(&cmd.children, listener)?,
            Info::SyntaxCmd => (),  // effect is done in parser
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

    fn do_var(&mut self, children: &[ParseNode], is_bound: bool) -> Result<(), Error> {
        let kind = get_kind(&children[1])?;
        let var_type = if is_bound {
            VarType::BoundVar(kind)
        } else {
            VarType::TermVar(kind)
        };
        for child in &children[0].children {
            let var = get_var(child)?;
            if self.vars.contains_key(&var) {
                if self.verbose {
                    println!("Duplicate var {}", self.parser.tok_str(var));
                }
                return Err(Error::DuplicateVar);
            }
            self.vars.insert(var, var_type);
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
            let ty = get_type(arg)?;
            args.push(ty);
        }
        let kind = get_kind(&children[2])?;
        self.terms.insert(con, (args, kind));
        Ok(())
    }

    fn do_def(&mut self, children: &[ParseNode]) -> Result<(), Error> {
        let con = get_const(&children[0])?;
        if self.terms.contains_key(&con) {
            if self.verbose {
                println!("Duplicate term {}", self.parser.tok_str(con));
            }
            return Err(Error::DuplicateTerm);
        }
        let args = &children[1];
        let rhs = &children[2];
        let (def, (args, kind)) = self.mk_def(con, args, rhs)?;
        self.defs.insert(con, def);
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
        let stmt = self.mk_stmt(&children[1], &children[2], &children[3])?;
        if self.verbose {
            println!("adding stmt {}: {:?}", self.parser.tok_str(step), &stmt);
        }
        self.stmts.insert(step, stmt);
        Ok(())
    }

    fn do_theorem<L: ProofListener>(&mut self, children: &[ParseNode], listener: &mut L)
        -> Result<(), Error>
    {
        let step = get_step(&children[0])?;
        if self.stmts.contains_key(&step) {
            if self.verbose {
                println!("Duplicate stmt {}", self.parser.tok_str(step));
            }
            return Err(Error::DuplicateStmt);
        }
        listener.start_proof(&children[0]);
        let mut stmt = self.mk_stmt(&children[2], &children[3], &children[4])?;
        let mut graph = Graph::new(&self.defs, self.parser.backslash());
        let (hyps, mut vars, mut bound_vars) = graph.add_hyps(&stmt)?;
        // Result lines can add new binding variables, but those won't affect the stmt.
        let mut bound_map = stmt.bound_map.clone();
        let mut steps = BTreeMap::new();
        for (hyp_name, hyp) in children[1].children.iter().zip(hyps.into_iter()) {
            steps.insert(get_step(hyp_name)?, hyp);
        }
        let concl_node = self.apply_proof(&children[5], &mut graph, &mut steps,
            &mut stmt.var_map, &mut bound_map, &mut vars, &mut bound_vars, listener)?;
        graph.unify_expr(concl_node, &stmt.concl, &mut vars, &mut bound_vars)?;
        // Make sure all variables in hyps and concl are general, and other properties.
        graph.validate(&vars, &bound_vars)?;
        graph.validate_notfree(&vars, &bound_vars, &stmt.notfree)?;
        listener.end_proof();
        if self.verbose {
            println!("adding stmt {}: {:?}", self.parser.tok_str(step), &stmt);
        }
        self.stmts.insert(step, stmt);
        Ok(())
    }

    // The `proof` argument is a list of lines.
    // `var_map` maps variable name (Token) to 0..n_vars index.
    // `var_ix_to_node` maps that index to node index in graph.
    // TODO: with these many args, should have a ProofCtx struct to hold them
    fn apply_proof<L: ProofListener>(&self, proof: &ParseNode, graph: &mut Graph,
        steps: &mut BTreeMap<Token, usize>,
        var_map: &mut BTreeMap<Token, usize>,
        bound_map: &mut BTreeMap<Token, usize>,
        var_ix_to_node: &mut Vec<Option<usize>>,
        bound_ix_to_node: &mut Vec<Option<usize>>,
        listener: &mut L) -> Result<usize, Error>
    {
        let mut last_line = None;
        for line in &proof.children {
            if line.info != Info::Line {
                return Err(Error::InconsistentParse);
            }
            let step_node = &line.children[1];
            let step = get_step(step_node)?;
            let mut hyps = Vec::with_capacity(line.children[2].children.len());
            for arg in &line.children[2].children {
                let hyp = match arg.info {
                    Info::List => self.apply_proof(arg, graph, steps, var_map,
                        bound_map, var_ix_to_node, bound_ix_to_node, listener)?,
                    Info::Dummy => last_line.ok_or(Error::StepNotFound)?,
                    Info::Step(arg_step) => {
                        if let Some(r) = steps.get(&arg_step) {
                            *r
                        } else if let Some(arg_stmt) = self.stmts.get(&arg_step) {
                            if !arg_stmt.hyps.is_empty() {
                                return Err(Error::ArityMismatch);
                            }
                            graph.apply_stmt(arg_stmt, &[])?.0
                        } else {
                            return Err(Error::StepNotFound);
                        }
                    }
                    _ => return Err(Error::InconsistentParse),
                };
                listener.step(arg, hyp);
                hyps.push(hyp);
            }
            let result;
            if let Some(r) = steps.get(&step) {
                if !hyps.is_empty() {
                    return Err(Error::ArityMismatch);
                }
                result = *r;
            } else if let Some(stmt) = self.stmts.get(&step) {
                if hyps.len() != stmt.hyps.len() {
                    return Err(Error::ArityMismatch);
                }
                result = graph.apply_stmt(stmt, &hyps)?.0;
            } else {
                return Err(Error::StepNotFound);
            }
            listener.step(step_node, result);
            // Unify result line if present.
            let res_line = &line.children[3];
            if res_line.info != Info::Dummy {
                listener.result(res_line, result);
                let (result_line, _kind) = self.term_to_expr(res_line, var_map,
                    bound_map, true)?;
                graph.unify_expr(result, &result_line, var_ix_to_node, bound_ix_to_node)?;
            }
            if let Info::Step(label) = line.children[0].info {
                if steps.insert(label, result).is_some() {
                    return Err(Error::DuplicateStep);
                }
            }
            last_line = Some(result);
        }
        last_line.ok_or(Error::EmptyProof)
    }

    fn mk_stmt(&self, hyps_pn: &ParseNode, nf_pn: &ParseNode, concl: &ParseNode)
        -> Result<Stmt, Error>
    {
        let mut hyps = Vec::with_capacity(hyps_pn.children.len());
        let mut var_map = BTreeMap::new();
        let mut bound_map = BTreeMap::new();
        for hyp in &hyps_pn.children {
            let (expr, _kind) = self.term_to_expr(hyp, &mut var_map, &mut bound_map, false)?;
            hyps.push(expr);
        }
        let (concl, _kind) = self.term_to_expr(concl, &mut var_map, &mut bound_map, false)?;
        let mut notfree = Vec::new();
        for constraint in &nf_pn.children {
            if constraint.info != Info::NotFree {
                return Err(Error::InconsistentParse);
            }
            let tvar = get_var(&constraint.children[1])?;
            let tvar_ix = *var_map.get(&tvar).ok_or(Error::VarNotFound)?;
            for var_node in &constraint.children[0].children {
                let var = get_var(var_node)?;
                let var_ix = *bound_map.get(&var).ok_or(Error::VarNotFound)?;
                notfree.push((var_ix, tvar_ix));
            }
        }
        Ok(Stmt { var_map, bound_map, notfree, hyps, concl })
    }

    // Convert a term (as parse node) to an expr suitable for unification. This method also
    // verifies well-formedness.
    //
    // The `is_res` parameter controls whether the term is a result line, or whether it is
    // a hypothesis or conclusion (in either an axiom or theorem). Result lines can't
    // introduce new term variables (so `var_map` is effectively non-mut).
    //
    // TODO: result lines should also be able to contain dummy sub-terms. Actually, as a
    // language design decision, a case can be made that hyps and concl in theorems can
    // also contain dummy sub-terms, as long as they're assigned during unification. But
    // that would require synthesizing the `Expr` back from the graph, which would
    // basically be the inverse operation as this method.
    fn term_to_expr(&self, node: &ParseNode, var_map: &mut BTreeMap<Token, usize>,
        bound_map: &mut BTreeMap<Token, usize>, is_res: bool)
        -> Result<(Expr, Type), Error>
    {
        if node.info == Info::Lambda {
            let bound_var = get_var(&node.children[0])?;
            let (body, ty) = self.term_to_expr(&node.children[1], var_map, bound_map, is_res)?;
            let var_type = self.vars.get(&bound_var).ok_or(Error::VarNotFound)?;
            let bound_var_ty = match *var_type {
                VarType::BoundVar(kind) => kind,
                _ => return Err(Error::LambdaArgMustBind),
            };
            let ty = Type::Arrow(bound_var_ty, Box::new(ty));
            let id = find_or_insert(bound_map, bound_var);
            let children = vec![Expr::BoundVar(id), body];
            return Ok((Expr::Term { constructor: self.parser.backslash(), children }, ty));
        }
        let atom = get_atom(node)?;
        if let Some(var_type) = self.vars.get(&atom) {
            if !node.children.is_empty() {
                return Err(Error::ArityMismatch);
            }
            match *var_type {
                VarType::TermVar(kind) => {
                    let id = if is_res {
                        *var_map.get(&atom).ok_or(Error::VarNotFound)?
                    } else {
                        find_or_insert(var_map, atom)
                    };
                    Ok((Expr::Var(id), Type::Base(kind)))
                }
                VarType::BoundVar(kind) => {
                    let id = find_or_insert(bound_map, atom);
                    Ok((Expr::BoundVar(id), Type::Base(kind)))
                }
            }
        } else if let Some(term) = self.terms.get(&atom) {
            let (ref args, kind) = *term;
            if node.children.len() != args.len() {
                if self.verbose {
                    println!("expected {} got {} for term {}",
                        args.len(), node.children.len(), self.parser.tok_str(atom));
                    self.parser.dump_tree(node);
                }
                return Err(Error::ArityMismatch);
            }
            let mut expr_args = Vec::with_capacity(args.len());
            for (arg, child) in args.iter().zip(node.children.iter()) {
                let (expr, ty) = self.term_to_expr(child, var_map, bound_map, is_res)?;
                if ty != *arg {
                    return Err(Error::TypeMismatch);
                }
                expr_args.push(expr);
            }
            let ty = Type::Base(kind);
            Ok((Expr::Term { constructor: atom, children: expr_args }, ty))
        } else {
            Err(Error::InconsistentParse)
        }
    }

    /// Makes an expr from a parse node representing a def argument.
    fn def_arg_to_expr(&self, node: &ParseNode, var_map: &mut BTreeMap<Token, usize>,
        bound_map: &mut BTreeMap<Token, usize>) -> Result<(Expr, Type), Error>
    {
        if node.info == Info::Lambda {
            let bound_var = get_var(&node.children[0])?;
            let (body, ty) = self.def_arg_to_expr(&node.children[1], var_map, bound_map)?;
            let var_type = self.vars.get(&bound_var).ok_or(Error::VarNotFound)?;
            let bound_var_ty = match *var_type {
                VarType::BoundVar(kind) => kind,
                _ => return Err(Error::LambdaArgMustBind),
            };
            let ty = Type::Arrow(bound_var_ty, Box::new(ty));
            let id = add_unique(bound_map, bound_var)?;
            let children = vec![Expr::BoundVar(id), body];
            return Ok((Expr::Term { constructor: self.parser.backslash(), children }, ty));
        }
        let atom = get_atom(node)?;
        if let Some(var_type) = self.vars.get(&atom) {
            if !node.children.is_empty() {
                return Err(Error::ArityMismatch);
            }
            match *var_type {
                VarType::TermVar(kind) => {
                    let id = add_unique(var_map, atom)?;
                    Ok((Expr::Var(id), Type::Base(kind)))
                }
                VarType::BoundVar(_) => {
                    Err(Error::NoRawBoundVars)
                }
            }
        } else {
            Err(Error::NoTermMatching)
        }
    }

    fn mk_def(&self, con: Token, args: &ParseNode, rhs_node: &ParseNode)
        -> Result<(Definition, (Vec<Type>, KindName)), Error>
    {
        let index = self.defs.len();
        let mut var_map = BTreeMap::new();
        let mut bound_map = BTreeMap::new();
        let mut children = Vec::new();
        let mut arg_types = Vec::new();
        for arg in &args.children {
            let (arg_expr, arg_ty) = self.def_arg_to_expr(arg, &mut var_map, &mut bound_map)?;
            children.push(arg_expr);
            arg_types.push(arg_ty);
        }
        let lhs = Expr::Term { constructor: con, children: children };
        let (rhs, ty) = self.term_to_expr(rhs_node, &mut var_map, &mut bound_map, true)?;
        let kind = match ty {
            Type::Base(kind) => kind,
            _ => return Err(Error::DefCantBeLambda),
        };
        let def = Definition { index, var_map, bound_map, lhs, rhs };
        Ok((def, (arg_types, kind)))
    }
}

fn find_or_insert(map: &mut BTreeMap<Token, usize>, tok: Token) -> usize {
    let new_val = map.len();
    *map.entry(tok).or_insert(new_val)
}

fn insert_unique<T>(map: &mut BTreeMap<Token, T>, key: Token, val: T) -> Option<()> {
    // TODO: rewriting in terms of entry would no doubt be more efficient
    if map.contains_key(&key) {
        None
    } else {
        map.insert(key, val);
        Some(())
    }
}

/// Adds a unique variable mapping, returning error if duplicate.
fn add_unique(map: &mut BTreeMap<Token, usize>, tok: Token) -> Result<usize, Error> {
    let new_val = map.len();
    insert_unique(map, tok, new_val).map(|_| new_val).ok_or(Error::DuplicateVar)
}
