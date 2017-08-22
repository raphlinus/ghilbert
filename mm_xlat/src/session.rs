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

//! Processing of a Metamath proof file for the purpose of translation.

use std::collections::BTreeSet;
use std::collections::HashMap;

use parser::{Parser, Statement, Compressed};
use proofout::{ProofOut, StepId};
use script::{Command, Script};

struct Block {
    e_ix: usize,
    f_ix: usize,
}

#[derive(Debug)]
struct Entry {
    mand_vars: Vec<usize>,  // index to Session.f
    n_hyps: usize,
    is_judg: bool,  // indicate whether the conclusion is a judgment
    // TODO: actually have hyps and concl
}

impl Entry {
    fn new(mand_vars: Vec<usize>, n_hyps: usize, concl: &[&str]) -> Entry {
        Entry {
            mand_vars,
            n_hyps,
            is_judg: concl[0] == "|-",
        }
    }
}

pub struct Session<'a> {
    out: ProofOut,
    labels: HashMap<&'a str, Entry>,
    e: Vec<(&'a str, Vec<&'a str>)>,
    f: Vec<(&'a str, &'a str, &'a str)>,
    blocks: Vec<Block>,
}

fn add_syms<'a>(s: &mut BTreeSet<&'a str>, syms: &[&'a str]) {
    for sym in syms {
        s.insert(sym);
    }
}

/// This is what's stored on the RPN stack
#[derive(Clone, Debug)]
enum El {
    /// A previous step in the proof
    Ostep(StepId),
    /// a syntax step, not a judgment, mostly ignored
    NonJudg,
}

impl<'a> Session<'a> {
    pub fn new(out: ProofOut) -> Session<'a> {
        Session {
            out,
            labels: HashMap::new(),
            e: Vec::new(),
            f: Vec::new(),
            blocks: Vec::new(),
        }
    }

    /// Run the input proof up to the given label. Return the command at that label.
    fn run_upto(&mut self, label: &str, parser: &mut Parser<'a>) -> Statement<'a> {
        for stmt in parser {
            match stmt {
                Statement::Proof(l, _, _) if l == label => return stmt,
                _ => self.do_stmt(stmt, false),
            }
        }
        panic!("reached eof in input, expected {}", label);
    }

    fn run_through(&mut self, label: &str, parser: &mut Parser<'a>, skip: bool) {
        let stmt = self.run_upto(label, parser);
        self.do_stmt(stmt, skip);
    }
                
    pub fn run_script(&mut self, script: &mut Script, parser: &mut Parser<'a>) {
        for cmd in script {
            match cmd {
                Command::CopyLine(s) => self.out.write(&s),
                Command::RunThrough(l) => self.run_through(&l, parser, false),
                Command::Skip(l) => self.run_through(&l, parser, true),
            }
        }
        /*
        for stmt in parser {
            self.do_stmt(stmt);
        }
        */
    }

    /// Gather the mandatory variables for the proof step. Result is
    /// indices to `self.f`.
    fn gather_mandatory(&self, concl: &[&str]) -> Vec<usize> {
        let mut sym_set = BTreeSet::new();
        for &(_label, ref hyp) in &self.e {
            add_syms(&mut sym_set, &hyp);
        }
        add_syms(&mut sym_set, concl);
        let mut result = Vec::new();
        for (ix, &(_label, _con, var)) in self.f.iter().enumerate() {
            if sym_set.contains(var) {
                result.push(ix);
            }
        }
        result
    }

    fn do_axiom(&mut self, label: &'a str, concl: Vec<&'a str>) {
        let mand_vars = self.gather_mandatory(&concl);
        self.labels.insert(label, Entry::new(mand_vars, self.e.len(), &concl));
    }

    fn do_proof(&mut self, label: &'a str, concl: Vec<&'a str>, compr: Vec<&'a str>,
        skip: bool)
    {
        let mand = self.gather_mandatory(&concl);
        if !skip {
            self.out.start_thm(label, &self.e, &concl);
            let mut stack: Vec<El> = Vec::new();
            if let Some(pos) = compr.iter().position(|&step| step == ")") {
                let mut saved = Vec::new();
                println!("{}: e = {:?}", label, self.e);
                // total number of mandatory hypotheses
                let m = mand.len() + self.e.len();
                // number of labels inside parentheses
                let n = pos - 1;
                for step in Compressed::new(&compr[pos+1 ..]) {
                    if step == 0 {
                        //println!("step {}: save {}", step, saved.len());
                        saved.push(stack.last().unwrap().clone());
                    } else if step <= mand.len() {
                        //println!("step {}: mand var {}", step, self.f[step - 1].0);
                        stack.push(El::NonJudg);
                    } else if step <= m {
                        let hyp_ix = step - mand.len() - 1;
                        //println!("step {}: hyp {}", step, self.e[hyp_ix].0);
                        let ix = self.out.add_step(self.e[hyp_ix].0, vec![]);
                        stack.push(El::Ostep(ix));
                    } else if step <= m + n {
                        let label = compr[step - m];
                        //println!("step {}: label {}", step, label);
                        if let Some(entry) = self.labels.get(label) {
                            let hyp_start = stack.len() - entry.n_hyps;
                            let new_el;
                            if entry.is_judg {
                                let args = (0 .. entry.n_hyps).map(|i|
                                    match stack[hyp_start + i] {
                                        El::Ostep(id) => id,
                                        El::NonJudg => panic!("didn't expect NonJudg in hyp"),
                                    }
                                ).collect::<Vec<_>>();
                                new_el = El::Ostep(self.out.add_step(label, args));
                            } else {
                                new_el = El::NonJudg;
                            }
                            let new_size = hyp_start - entry.mand_vars.len();
                            stack.truncate(new_size);
                            stack.push(new_el);
                        } else {
                            // Almost certainly a syntax building step
                            stack.push(El::NonJudg);
                        }
                    } else {
                        let save_ix = step - (m + n + 1);
                        //println!("step {}: reuse {}", step, save_ix);
                        stack.push(saved[save_ix].clone());
                    }
                    //println!("stack: {:?}", stack);
                }
            } else {
                panic!("proof {:?} not valid compressed format", compr);
            }
            self.out.end_thm();
            }
        self.labels.insert(label, Entry::new(mand, self.e.len(), &concl));
    }

    pub fn do_stmt(&mut self, stmt: Statement<'a>, skip: bool) {
        match stmt {
            Statement::StartBlock => {
                self.blocks.push(Block {
                    e_ix: self.e.len(),
                    f_ix: self.f.len(),
                });
            }
            Statement::EndBlock => {
                let block = self.blocks.pop().unwrap();
                self.e.truncate(block.e_ix);
                self.f.truncate(block.f_ix);
            }
            Statement::Axiom(label, concl) => {
                self.do_axiom(label, concl);
            }
            Statement::Essential(label, list) => {
                self.e.push((label, list));
            }
            Statement::Floating(label, con, var) => {
                self.f.push((label, con, var));
            }
            Statement::Proof(label, concl, compr) => {
                self.do_proof(label, concl, compr, skip);
            }
            _ => println!("stmt {:?}", stmt),
        }
    }
}
