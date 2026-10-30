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

//! Parsing of Metamath expressions into trees, using the syntax axioms.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Debug)]
pub enum Tree<'a> {
    Var(&'a str),
    /// Index of syntax axiom, and one child per variable in its pattern.
    App(usize, Vec<Rc<Tree<'a>>>),
}

pub struct SyntaxAx<'a> {
    pub tc: &'a str,
    pub pattern: Vec<&'a str>,
    /// For each pattern element, its typecode if it is a variable.
    pub var_tc: Vec<Option<&'a str>>,
}

impl<'a> SyntaxAx<'a> {
    /// The variables of the pattern, in order, with their typecodes.
    pub fn vars(&self) -> Vec<(&'a str, &'a str)> {
        self.pattern.iter().zip(self.var_tc.iter())
            .filter_map(|(&v, tc)| tc.map(|tc| (v, tc)))
            .collect()
    }
}

#[derive(Default)]
pub struct Grammar<'a> {
    pub axioms: Vec<SyntaxAx<'a>>,
    by_tc: HashMap<&'a str, Vec<usize>>,
    tokens: HashSet<&'a str>,
}

type Parses<'a> = Rc<Vec<(Rc<Tree<'a>>, usize)>>;

struct Ctx<'a, 'b> {
    toks: &'b [&'a str],
    vars: &'b HashMap<&'a str, &'a str>,
    memo: HashMap<(&'a str, usize), Parses<'a>>,
}

impl<'a> Grammar<'a> {
    pub fn add(&mut self, ax: SyntaxAx<'a>) -> usize {
        let ix = self.axioms.len();
        self.by_tc.entry(ax.tc).or_insert_with(Vec::new).push(ix);
        self.tokens.extend(ax.pattern.iter().cloned());
        self.axioms.push(ax);
        ix
    }

    /// Gets the given token, if it's in a syntax axiom.
    pub fn token(&self, tok: &str) -> Option<&'a str> {
        self.tokens.get(tok).cloned()
    }

    /// Finds a constant of the given typecode.
    pub fn constant(&self, tc: &str) -> Option<&'a str> {
        self.by_tc.get(tc)?.iter().map(|&ix| &self.axioms[ix])
            .find(|ax| ax.pattern.len() == 1 && ax.var_tc[0].is_none())
            .map(|ax| ax.pattern[0])
    }

    /// Parses the tokens as a complete expression of the given typecode.
    ///
    /// The `vars` argument maps variables in scope to their typecodes.
    pub fn parse(&self, toks: &[&'a str], tc: &'a str, vars: &HashMap<&'a str, &'a str>)
        -> Option<Rc<Tree<'a>>>
    {
        let mut ctx = Ctx { toks, vars, memo: HashMap::new() };
        let parses = self.parse_at(&mut ctx, tc, 0);
        parses.iter().find(|&&(_, end)| end == toks.len()).map(|(t, _)| t.clone())
    }

    // Packrat parser returning all parses starting at `pos`. The grammar of
    // set.mm is not left-recursive, but the memo entry is seeded with an empty
    // result anyway so that a cycle terminates.
    fn parse_at(&self, ctx: &mut Ctx<'a, '_>, tc: &'a str, pos: usize) -> Parses<'a> {
        if let Some(r) = ctx.memo.get(&(tc, pos)) {
            return r.clone();
        }
        ctx.memo.insert((tc, pos), Rc::new(Vec::new()));
        let mut results = Vec::new();
        if pos < ctx.toks.len() && ctx.vars.get(ctx.toks[pos]) == Some(&tc) {
            results.push((Rc::new(Tree::Var(ctx.toks[pos])), pos + 1));
        }
        if let Some(ixs) = self.by_tc.get(tc) {
            for &ix in ixs {
                let ax = &self.axioms[ix];
                if let (Some(&first), None) = (ax.pattern.first(), ax.var_tc[0]) {
                    if pos >= ctx.toks.len() || ctx.toks[pos] != first {
                        continue;
                    }
                }
                let mut states = vec![(Vec::new(), pos)];
                for (&el, &vtc) in ax.pattern.iter().zip(ax.var_tc.iter()) {
                    let mut next = Vec::new();
                    for (kids, p) in states {
                        match vtc {
                            None => if p < ctx.toks.len() && ctx.toks[p] == el {
                                next.push((kids, p + 1));
                            },
                            Some(vtc) => {
                                for &(ref t, end) in self.parse_at(ctx, vtc, p).iter() {
                                    let mut kids = kids.clone();
                                    kids.push(t.clone());
                                    next.push((kids, end));
                                }
                            }
                        }
                    }
                    states = next;
                    if states.is_empty() {
                        break;
                    }
                }
                for (kids, end) in states {
                    results.push((Rc::new(Tree::App(ix, kids)), end));
                }
            }
        }
        let results = Rc::new(results);
        ctx.memo.insert((tc, pos), results.clone());
        results
    }
}
