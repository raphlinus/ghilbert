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

//! Unification of terms, the core of the verification step.

use std::collections::{BTreeMap, BTreeSet};
use std::mem;

use union_find::{QuickUnionUf, UnionByRank, UnionFind};

use lexer::Token;

type Const = Token;

#[derive(Debug, Clone)]
pub enum Expr {
    Var(usize),
    BoundVar(usize),
    // Note: Term also represents lambda expressions
    Term {
        constructor: Const,
        children: Vec<Expr>,
    },
}

#[derive(Debug)]
pub struct Stmt {
    /// Map from variable name to index, same as arg to Expr::Var
    pub var_map: BTreeMap<Token, usize>,
    /// Map from variable name to index, same as arg to Expr::BoundVar
    pub bound_map: BTreeMap<Token, usize>,
    /// Not-free-in constraint is pair of bound var and term var.
    pub notfree: Vec<(usize, usize)>,
    pub hyps: Vec<Expr>,
    pub concl: Expr,
}

pub struct Definition {
    pub index: usize,
    /// Map from variable name to index, same as arg to Expr::Var
    pub var_map: BTreeMap<Token, usize>,
    /// Map from variable name to index, same as arg to Expr::BoundVar
    pub bound_map: BTreeMap<Token, usize>,
    pub lhs: Expr,
    pub rhs: Expr,
}


#[derive(Clone, Debug)]
struct GraphNodeInfo {
    constructor: Const,
    children: Vec<usize>,  // indices to graph nodes
}

pub struct Graph<'a> {
    defs: &'a BTreeMap<Token, Definition>,
    infos: Vec<Option<GraphNodeInfo>>,
    uf: QuickUnionUf<UnionByRank>,
    /// Term vars of proof steps, for occurs and not-general checks.
    queue: Vec<usize>,
    /// Bound vars of proofs steps, for distinctness check.
    bound_var_sets: Vec<Vec<usize>>,
    /// Pair of node ix of bound var, node ix of term var
    nfi_constraints: Vec<(usize, usize)>,
    /// Identifier for backslash so that we can identify lambda
    backslash: Const,
}

#[derive(Debug)]
pub enum Error {
    /// Two terms were attempted to be unified with different constructors.
    ConstructorNoMatch,
    /// A variable in the theorem to be proved was specialized.
    NotGeneral,
    /// Two variables in the theorem were unified.
    BadUnification,
    /// Graph contains a cycle, so a term is infinite.
    OccursCheck,
    /// An intermediate variable was left general.
    CannotSynthesize,
    /// Bound variables were unified so are not distinct.
    NotDistinct,
    /// A not-free-in constraint was violated.
    NotFreeIn,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum State {
    Unvisited,
    Visiting,
    Visited,
    Bound,
}

impl<'a> Graph<'a> {
    pub fn new(defs: &BTreeMap<Token, Definition>, backslash: Const) -> Graph {
        Graph {
            defs,
            infos: Vec::new(),
            uf: QuickUnionUf::new(0),
            queue: Vec::new(),
            bound_var_sets: Vec::new(),
            nfi_constraints: Vec::new(),
            backslash,
        }
    }

    /// Create a new node with no associated info.
    pub fn new_node(&mut self) -> usize {
        let vec_result = self.infos.len();
        self.infos.push(None);
        let uf_result = self.uf.insert(Default::default());
        debug_assert!(vec_result == uf_result);
        uf_result
    }

    /// Apply a proof step, performing unification.
    ///
    /// Return node index of conclusion if successful, as well as assignment of
    /// variables to node indices.
    // TODO: probably don't need to return vars, rather logging the constraints
    // for validation later. In any case, bound_vars and vars should share fate.
    pub fn apply_stmt(&mut self, stmt: &Stmt, hyps: &[usize])
        -> Result<(usize, Vec<Option<usize>>), Error>
    {
        let mut vars = vec![None; stmt.var_map.len()];
        let mut bound_vars = vec![None; stmt.bound_map.len()];
        for (i, expr) in stmt.hyps.iter().enumerate() {
            self.unify_expr(hyps[i], expr, &mut vars, &mut bound_vars)?;
        }
        let concl = self.new_node();
        self.unify_expr(concl, &stmt.concl, &mut vars, &mut bound_vars)?;
        for opt_node in &vars {
            if let Some(node) = *opt_node {
                self.queue.push(node);
            }
        }
        for &(bound_var, var) in &stmt.notfree {
            // The variables must be assigned after unification.
            let bound_var_ix = bound_vars[bound_var].unwrap();
            let var_ix = vars[var].unwrap();
            self.nfi_constraints.push((bound_var_ix, var_ix));
        }
        self.distinct_bound_vars(bound_vars);
        Ok((concl, vars))
    }

    /// Add hypotheses for a theorem being proved.
    ///
    /// Return a vector of nodes corresponding to the hypotheses, as well
    /// as the variable assignments for term and binding variables.
    pub fn add_hyps(&mut self, stmt: &Stmt)
        -> Result<(Vec<usize>, Vec<Option<usize>>, Vec<Option<usize>>), Error>
    {
        let mut vars = vec![None; stmt.var_map.len()];
        let mut bound_vars = vec![None; stmt.bound_map.len()];
        let mut hyp_nodes = Vec::with_capacity(stmt.hyps.len());
        for expr in &stmt.hyps {
            let hyp_node = self.new_node();
            self.unify_expr(hyp_node, expr, &mut vars, &mut bound_vars)?;
            hyp_nodes.push(hyp_node);
        }
        Ok((hyp_nodes, vars, bound_vars))
    }

    /// Unifies an expression with the given node in the graph.
    ///
    /// The `vars` argument maps var index (same space as Var variant in Expr) to
    /// node number. Similarly `bound_vars` maps BoundVar index to node.
    pub fn unify_expr(&mut self, node: usize, expr: &Expr, vars: &mut Vec<Option<usize>>,
        bound_vars: &mut Vec<Option<usize>>)
        -> Result<(), Error>
    {
        match *expr {
            Expr::Var(ix) => {
                if let Some(vnode) = vars[ix] {
                    self.unify_nodes(node, vnode)?;
                } else {
                    vars[ix] = Some(node);
                }
            }
            Expr::BoundVar(ix) => {
                if let Some(vnode) = bound_vars[ix] {
                    self.unify_nodes(node, vnode)?;
                } else {
                    bound_vars[ix] = Some(node);
                }
            }
            Expr::Term { constructor, ref children } => {
                let nfind = self.uf.find(node);
                if self.infos[nfind].is_none() {
                    let mut child_nodes = Vec::new();
                    for _ in 0..children.len() {
                        let child_node = self.new_node();
                        child_nodes.push(child_node);
                    }
                    let info = GraphNodeInfo {
                        constructor: constructor,
                        children: child_nodes,
                    };
                    self.infos[nfind] = Some(info);
                }
                let info = self.infos[nfind].as_ref().unwrap().clone();
                if info.constructor != constructor {
                    // Might be a definition to expand, so let node unification handle it
                    // (and return an error if it still doesn't unify).
                    let term_node = self.new_node();
                    self.unify_expr(term_node, expr, vars, bound_vars)?;
                    return self.unify_nodes(node, term_node);
                }
                for (i, child) in children.iter().enumerate() {
                    self.unify_expr(info.children[i], child, vars, bound_vars)?;
                }
            }
        }
        Ok(())
    }

    fn unify_nodes(&mut self, a: usize, b: usize) -> Result<(), Error> {
        let afind = self.uf.find(a);
        let bfind = self.uf.find(b);
        if afind == bfind {
            // Nodes are already the same.
            return Ok(());
        }
        let def_info = if let (Some(ainfo), Some(binfo)) =
            (self.infos[afind].as_ref(), self.infos[bfind].as_ref())
        {
            if ainfo.constructor != binfo.constructor {
                match (self.defs.get(&ainfo.constructor), self.defs.get(&binfo.constructor)) {
                    (Some(adef), Some(bdef)) => {
                        // Expand the more recent definition.
                        if adef.index > bdef.index {
                            Some((afind, adef))
                        } else {
                            Some((bfind, bdef))
                        }
                    }
                    (Some(adef), None) => Some((afind, adef)),
                    (None, Some(bdef)) => Some((bfind, bdef)),
                    _ => None,  // No definitions to expand, this will fail below.
                }
            } else {
                None  // Constructors match.
            }
        } else {
            None  // One or both nodes is general.
        };
        if let Some((node, def)) = def_info {
            self.expand_def(node, def)?;
        }
        let _ = self.uf.union(a, b);
        let root = self.uf.find(afind);
        debug_assert!(root == afind || root == bfind);
        if self.infos[afind].is_none() && self.infos[bfind].is_none() {
            // nothing to do
        } else if self.infos[afind].is_none() && self.infos[bfind].is_some() {
            if root == afind {
                self.infos[afind] = self.infos[bfind].take();
            }
        } else if self.infos[afind].is_some() && self.infos[bfind].is_none() {
            if root == bfind {
                self.infos[bfind] = self.infos[afind].take();
            }
        } else {
            let (ainfo, binfo) = if root == afind {
                (self.infos[afind].clone().unwrap(), self.infos[bfind].take().unwrap())
            } else {
                (self.infos[afind].take().unwrap(), self.infos[bfind].clone().unwrap())
            };
            if ainfo.constructor != binfo.constructor {
                return Err(Error::ConstructorNoMatch);
            }
            for (&achild, &bchild) in ainfo.children.iter().zip(binfo.children.iter()) {
                self.unify_nodes(achild, bchild)?;
            }
        }
        Ok(())
    }

    /// Expands the definition at the specified node, replacing its info.
    fn expand_def(&mut self, node: usize, def: &Definition) -> Result<(), Error> {
        let mut vars = vec![None; def.var_map.len()];
        let mut bound_vars = vec![None; def.bound_map.len()];
        self.unify_expr(node, &def.lhs, &mut vars, &mut bound_vars)?;
        self.infos[node] = None;
        self.unify_expr(node, &def.rhs, &mut vars, &mut bound_vars)?;
        //println!("expanding {}, vars={:?} {:?}", node, vars, self.infos[node]);
        self.distinct_bound_vars(bound_vars);
        Ok(())
    }

    /// Registers the set of bound variables so that they'll be validated as all
    /// distinct later.
    fn distinct_bound_vars(&mut self, bound_vars: Vec<Option<usize>>) {
        if !bound_vars.is_empty() {
            let bound_var_set = bound_vars.iter().filter_map(|o| *o).collect();
            self.bound_var_sets.push(bound_var_set);
        }
    }

    /// Dumps graph, for debugging.
    #[allow(dead_code)]
    fn dump_graph(&mut self) {
        for i in 0..self.infos.len() {
            print!("info {}->{}", i, self.uf.find(i));
            if let Some(info) = self.infos[i].as_ref() {
                print!(": [{}]", info.constructor);
                for child in &info.children {
                    print!(" {}", child);
                }
            }
            println!("");
        }
    }

    /// Validates the graph, given variables of the theorem being proved.
    ///
    /// This method checks a number of correctness conditions, including:
    /// * All given variables are general.
    /// * No two given variables have been unified.
    /// * The graph contains no cycles (occurs check).
    /// * No subterms (other than the given variables) have been left general.
    pub fn validate(&mut self, var_map: &[Option<usize>], bound_var_map: &[Option<usize>])
        -> Result<(), Error>
    {
        let mut states = vec![State::Unvisited; self.infos.len()];
        // Ensure that the term variables appearing in hyps and concl of theorem
        // being proved are distinct and general.
        for opt_node in var_map {
            if let Some(node) = *opt_node {
                let nfind = self.uf.find(node);
                if states[nfind] != State::Unvisited {
                    return Err(Error::BadUnification);
                }
                states[nfind] = State::Visited;
                if self.infos[nfind].is_some() {
                    return Err(Error::NotGeneral);
                }
            }
        }
        // Ensure that all of the nodes in each bound var set are distinct,
        // general, and not unified with a term variable appearing in hyps or
        // concl of theorem being proved.
        for bound_var_set in &self.bound_var_sets {
            for node in bound_var_set {
                let nfind = self.uf.find(*node);
                if states[nfind] == State::Visited {
                    return Err(Error::NotDistinct);
                }
                states[nfind] = State::Visited;
                if self.infos[nfind].is_some() {
                    return Err(Error::NotGeneral);
                }
            }
            for node in bound_var_set {
                // could store the results of find from the first round...
                let nfind = self.uf.find(*node);
                states[nfind] = State::Bound;
            }
        }
        // Ensure that the bound variables appearing in hyps, concl, and result
        // lines of theorem being proved are distinct and general.
        for opt_node in bound_var_map {
            if let Some(node) = *opt_node {
                let nfind = self.uf.find(node);
                if states[nfind] == State::Visited {
                    return Err(Error::NotDistinct);
                }
                states[nfind] = State::Bound;
                if self.infos[nfind].is_some() {
                    return Err(Error::NotGeneral);
                }
            }
        }

        // Note: this traversal could probably be made faster.
        while let Some(node) = self.queue.pop() {
            let nfind = self.uf.find(node);
            //println!("running {}->{} ({:?})", node, nfind, states[nfind]);
            match states[nfind] {
                State::Unvisited => {
                    states[nfind] = State::Visiting;
                    self.queue.push(nfind);
                    if let Some(ref info) = self.infos[nfind] {
                        for child in &info.children {
                            let cfind = self.uf.find(*child);
                            match states[cfind] {
                                State::Unvisited => self.queue.push(cfind),
                                State::Visiting => return Err(Error::OccursCheck),
                                State::Visited | State::Bound => (),
                            }
                        }
                    } else {
                        println!("cannot synthesize {}", nfind);
                        return Err(Error::CannotSynthesize);
                    }
                }
                State::Visiting => states[nfind] = State::Visited,
                State::Visited | State::Bound => (),
            }
        }
        Ok(())
    }

    /// Validates the not-free-in constraints of the proof steps.
    ///
    /// The `notfree` argument is in the same form as `Stmt::notfree`.
    pub fn validate_notfree(&mut self, var_map: &[Option<usize>],
        bound_var_map: &[Option<usize>], notfree: &[(usize, usize)])
        -> Result<(), Error>
    {
        if self.nfi_constraints.is_empty() {
            return Ok(())
        }
        let mut term_var_set = BTreeSet::new();
        for opt_var in var_map {
            if let Some(var) = *opt_var {
                term_var_set.insert(self.uf.find(var));
            }
        }
        /// Maps node of bound var to set of term var nodes it can appear free in.
        let mut free_set = BTreeMap::new();
        for opt_bound_var in bound_var_map {
            if let Some(bound_var) = *opt_bound_var {
                let bfind = self.uf.find(bound_var);
                free_set.insert(bfind, term_var_set.clone());
            }
        }
        for &(bound_var, var) in notfree {
            let bfind = self.uf.find(bound_var_map[bound_var].unwrap());
            let vfind = self.uf.find(var_map[var].unwrap());
            free_set.get_mut(&bfind).unwrap().remove(&vfind);
        }
        // We take it out to make the borrow checker happy. Alternatively we could
        // make this method `&self` and put `uf` in a `RefCell`.
        let nfi_constraints = mem::replace(&mut self.nfi_constraints, Vec::new());
        let mut result = Ok(());
        for &(bound_var, var) in &nfi_constraints {
            let bfind = self.uf.find(bound_var);
            if self.is_free_in(bfind, var, free_set.get(&bfind)) {
                result = Err(Error::NotFreeIn);
                break;
            }
        }
        self.nfi_constraints = nfi_constraints;
        result
    }

    /// Checks whether a given bound variable is free in the expression corresponding
    /// to a graph node.
    ///
    /// The `bfind` parameter is the bound variable node, resolved with `uf.find()`.
    // TODO (performance): should probably memoize the queries, otherwise this can be
    // susceptible to exponential blowup.
    fn is_free_in(&mut self, bfind: usize, var: usize,
        free_set: Option<&BTreeSet<usize>>)
        -> bool
    {
        // Note: could take a scratch stack as an argument to improve reuse and
        // decrease allocation.
        let mut stack = vec![var];
        while let Some(var) = stack.pop() {
            let vfind = self.uf.find(var);
            if bfind == vfind {
                return true;
            }
            if let Some(ref info) = self.infos[vfind] {
                if info.constructor == self.backslash {
                    let child_bound_var = self.uf.find(info.children[0]);
                    if child_bound_var != bfind {
                        stack.push(info.children[1])
                    }
                } else {
                    stack.extend_from_slice(&info.children);
                }
            } else if let Some(free_set) = free_set {
                if free_set.contains(&vfind) {
                    return true;
                }
            }
        }
        false
    }
}

pub struct ReconstructCtx {
    var_map: BTreeMap<usize, Expr>,
}

impl<'a> Graph<'a> {
    pub fn mk_reconstruct(&mut self, var_ix_to_node: &[Option<usize>],
        bound_ix_to_node: &[Option<usize>]) -> ReconstructCtx
    {
        let mut result = BTreeMap::new();
        for (i, opt_ix) in var_ix_to_node.iter().enumerate() {
            if let Some(ix) = *opt_ix {
                result.insert(self.uf.find(ix), Expr::Var(i));
            }
        }
        for (i, opt_ix) in bound_ix_to_node.iter().enumerate() {
            if let Some(ix) = *opt_ix {
                result.insert(self.uf.find(ix), Expr::BoundVar(i));
            }
        }
        ReconstructCtx { var_map: result }
    }

    pub fn reconstruct_expr(&mut self, ctx: &ReconstructCtx, node: usize) -> Option<Expr> {
        let nfind = self.uf.find(node);
        if let Some(expr) = ctx.var_map.get(&nfind) {
            return Some(expr.clone());
        }
        if let Some(info) = self.infos[nfind].clone() {
            let mut children = Vec::new();
            for child in info.children {
                if let Some(child_expr) = self.reconstruct_expr(ctx, child) {
                    children.push(child_expr);
                } else {
                    return None;
                }
            }
            Some(Expr::Term { constructor: info.constructor, children })
        } else {
            None
        }
    }
}
