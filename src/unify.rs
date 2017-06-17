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

use union_find::{QuickUnionUf, UnionByRank, UnionFind};

use lexer::Token;

type Const = Token;

#[derive(Debug)]
pub enum Expr {
	Var(usize),
	Term {
		constructor: Const,
		children: Vec<Expr>,
	}
}

#[derive(Debug)]
pub struct Stmt {
	pub n_var: usize,  // TODO: might become more info, like names
	pub hyps: Vec<Expr>,
	pub concl: Expr,
}

#[derive(Clone)]
struct GraphNodeInfo {
	constructor: Const,
	children: Vec<usize>,  // indices to graph nodes
}

pub struct Graph {
	infos: Vec<Option<GraphNodeInfo>>,
	uf: QuickUnionUf<UnionByRank>,
}

#[derive(Debug)]
pub enum Error {
	ConstructorNoMatch,
	NotGeneral,
}

impl Graph {
	pub fn new() -> Graph {
		Graph {
			infos: Vec::new(),
			uf: QuickUnionUf::new(0),
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
	pub fn apply_stmt(&mut self, stmt: &Stmt, hyps: &[usize])
		-> Result<(usize, Vec<Option<usize>>), Error>
	{
		let mut vars = vec![None; stmt.n_var];
		for (i, expr) in stmt.hyps.iter().enumerate() {
			self.unify_expr(hyps[i], expr, &mut vars)?;
		}
		let concl = self.new_node();
		self.unify_expr(concl, &stmt.concl, &mut vars)?;
		Ok((concl, vars))
	}

	/// Add hypotheses for a theorem being proved.
	///
	/// Return a vector of nodes corresponding to the hypotheses, as well
	/// as the variable assignment.
	pub fn add_hyps(&mut self, stmt: &Stmt)
		-> Result<(Vec<usize>, Vec<Option<usize>>), Error>
	{
		let mut vars = vec![None; stmt.n_var];
		let mut hyp_nodes = Vec::with_capacity(stmt.hyps.len());
		for expr in &stmt.hyps {
			let hyp_node = self.new_node();
			self.unify_expr(hyp_node, expr, &mut vars)?;
			hyp_nodes.push(hyp_node);
		}
		Ok((hyp_nodes, vars))
	}

	pub fn unify_expr(&mut self, node: usize, expr: &Expr, vars: &mut Vec<Option<usize>>)
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
			Expr::Term { constructor, ref children } => {
				if self.infos[node].is_none() {
					let mut child_nodes = Vec::new();
					for _ in 0..children.len() {
						let child_node = self.new_node();
						child_nodes.push(child_node);
					}
					let info = GraphNodeInfo {
						constructor: constructor,
						children: child_nodes,
					};
					self.infos[node] = Some(info);
				}
				let info = self.infos[node].as_ref().unwrap().clone();
				if info.constructor != constructor {
					return Err(Error::ConstructorNoMatch);
				}
				for (i, child) in children.iter().enumerate() {
					self.unify_expr(info.children[i], child, vars)?;
				}
			}
		}
		Ok(())
	}

	fn unify_nodes(&mut self, a: usize, b: usize) -> Result<(), Error> {
		// TODO: unify node info
		let afind = self.uf.find(a);
		let bfind = self.uf.find(b);
		if afind == bfind {
			// Nodes are already the same.
			return Ok(());
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

	/// Checks whether the node can be assigned any value of its kind.
	pub fn check_general(&self, node: usize) -> Result<(), Error> {
		if self.infos[node].is_some() {
			Err(Error::NotGeneral)
		} else {
			Ok(())
		}
	}
}
