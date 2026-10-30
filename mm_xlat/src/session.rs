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
//!
//! Syntax axioms become `term` declarations, setvar variables become bound
//! variables, `$d` between a setvar and a wff or class variable becomes a
//! not-free-in constraint, and proofs are replayed so that each step's
//! expression is known (for result lines where unification needs them).

use std::collections::HashMap;
use std::rc::Rc;

use grammar::{Grammar, SyntaxAx, Tree};
use parser::{Parser, Statement, Compressed};
use proofout::ProofOut;
use script::{Command, Script};

#[derive(Clone, Debug)]
enum Hyp<'a> {
    /// Floating hypothesis: typecode, variable.
    F(&'a str, &'a str),
    /// Essential hypothesis: the expression, starting with its typecode.
    E(Vec<&'a str>),
}

#[derive(Debug)]
struct Frame<'a> {
    /// Mandatory hypotheses with labels, in order.
    hyps: Vec<(&'a str, Hyp<'a>)>,
    concl: Vec<&'a str>,
    /// Distinct variable pairs among mandatory variables.
    dv: Vec<(&'a str, &'a str)>,
}

/// A proof, with what's needed to replay it outside of its block.
struct SavedProof<'a> {
    steps: Vec<&'a str>,
    /// The `$f` statements active only in the enclosing blocks.
    floats: Vec<(&'a str, &'a str, &'a str)>,
}

/// How a syntax axiom is written in Ghilbert.
enum Notation {
    Infix(&'static str),
    Prefix(&'static str),
    Binder(&'static str),
    /// Prefix application of a term named by the axiom label.
    Plain,
}

struct TermInfo<'a> {
    name: String,
    notation: Notation,
    /// Left and right binding powers, for operators (as in the Ghilbert parser).
    prec: (u32, u32),
    /// Variables of the pattern, with typecodes and whether each binds.
    vars: Vec<(&'a str, &'a str, bool)>,
    /// For each variable of the pattern, the positions of the binders over it.
    scope: Vec<Vec<usize>>,
}

/// Where a term is printed, for deciding on parentheses.
#[derive(Clone, Copy)]
enum Ctx {
    /// Parsed with this right binding power (an operator's right operand).
    Operand(u32),
    /// Left operand of an infix operator with this left binding power.
    Left(u32),
    /// Argument of a plain term application.
    Arg,
}

/// Syntax axioms written with nice notation in Ghilbert.
fn nice_notation(label: &str) -> Option<(Notation, &'static str, u32)> {
    Some(match label {
        "wi" => (Notation::Infix("->"), "infixr", 25),
        "wn" => (Notation::Prefix("-."), "prefix", 40),
        "wb" => (Notation::Infix("<->"), "infixl", 20),
        "wa" => (Notation::Infix("/\\"), "infixl", 35),
        "wo" => (Notation::Infix("\\/"), "infixl", 30),
        "wal" => (Notation::Binder("A."), "binder", 45),
        "wex" => (Notation::Binder("E."), "binder", 45),
        "wceq" => (Notation::Infix("="), "infixl", 50),
        "wcel" => (Notation::Infix("e."), "infixl", 50),
        _ => return None,
    })
}

/// Setvar arguments (by position among the pattern's variables) that do not
/// bind. All other setvar arguments of a constructor bind all of its wff and
/// class arguments, which is the same default MM0's translation uses.
const NON_BINDING: &[(&str, usize)] = &[
    ("wsb", 0),  // [ y / x ] ph: y is free
    ("wcdeq", 0),  // CondEq ( x = y -> ph ): nothing is bound
    ("wcdeq", 1),
];

/// Wff and class arguments outside the scope of a binder, as positions among
/// the pattern's variables of the argument and the binder. A setvar that occurs
/// free in such an argument also occurs free in the whole term. The default
/// would wrongly make it not free, even though every proof in set.mm would
/// still check.
const UNSCOPED: &[(&str, usize, usize)] = &[
    ("wsbc", 0, 1),  // [. A / x ]. ph
    ("csb", 0, 1),  // [_ A / x ]_ B
    ("csu", 1, 0),  // sum_ k e. A B: A occurs outside the scope of k in df-sum
    ("cprod", 1, 0),  // prod_ k e. A B
    ("cdit", 0, 3),  // S_ [ A -> B ] C _d x: A <_ B occurs outside the integral
    ("cdit", 1, 3),
    ("w2reu", 1, 2),  // E! x e. A , y e. B ph: y isn't bound in E! x e. A
    ("w2reu", 3, 0),
];

const SETVAR: &str = "setvar";

pub struct Session<'a> {
    out: ProofOut,
    frames: HashMap<&'a str, Rc<Frame<'a>>>,
    /// Proofs of the statements read so far, for writing instances of them.
    proofs: HashMap<&'a str, Rc<SavedProof<'a>>>,
    /// Active hypotheses, in order of appearance.
    hyps: Vec<(&'a str, Hyp<'a>)>,
    /// Active variables and their typecodes (from `$f`).
    vars: HashMap<&'a str, &'a str>,
    /// Active `$d` statements.
    dvs: Vec<Vec<&'a str>>,
    /// Saved lengths of `hyps` and `dvs` at block starts.
    blocks: Vec<(usize, usize)>,
    grammar: Grammar<'a>,
    terms: Vec<TermInfo<'a>>,
    /// Variables declared in the output, with their typecodes.
    declared: HashMap<&'a str, &'a str>,
    comment: Option<&'a str>,
    /// Setvar variables of the statement being written that never bind. These
    /// are written as term variables of kind setvar (the variable name with a
    /// prime), so they may coincide when instantiated, as in set.mm.
    free_setvars: Vec<&'a str>,
    /// Statements whose setvar variables are all kept bound, because the proof
    /// needs them distinct.
    bound_form: Vec<String>,
    /// The setvar variables written as term variables in each statement.
    free_by_stmt: HashMap<&'a str, Vec<&'a str>>,
    /// Hand-written proofs of instances that don't follow from a replayed proof
    /// (see `instance`).
    instance_proofs: HashMap<String, String>,
    /// A statement read but not yet processed (see `run_until`).
    pending: Option<Statement<'a>>,
    /// A hand-written proof body for the next statement written (from `prove`).
    manual_proof: Option<String>,
}

impl<'a> Session<'a> {
    pub fn new(mut out: ProofOut) -> Session<'a> {
        out.write("/* Translation of set.mm, generated by mm_xlat */\n\n");
        out.write("kind judg;\nkind wff;\nkind setvar;\nkind class;\n");
        out.write("syntax {\n    prefix |- 5;\n}\nterm |- wff: judg;\n\n");
        Session {
            out,
            frames: HashMap::new(),
            proofs: HashMap::new(),
            hyps: Vec::new(),
            vars: HashMap::new(),
            dvs: Vec::new(),
            blocks: Vec::new(),
            grammar: Grammar::default(),
            terms: Vec::new(),
            declared: HashMap::new(),
            comment: None,
            free_setvars: Vec::new(),
            bound_form: Vec::new(),
            free_by_stmt: HashMap::new(),
            instance_proofs: HashMap::new(),
            pending: None,
            manual_proof: None,
        }
    }

    fn label_of(stmt: &Statement<'a>) -> Option<&'a str> {
        match *stmt {
            Statement::Proof(l, _, _) | Statement::Axiom(l, _) => Some(l),
            _ => None,
        }
    }

    /// Run the input up to the given label. Return the statement at that label.
    fn run_upto(&mut self, label: &str, parser: &mut Parser<'a>) -> Statement<'a> {
        if let Some(stmt) = self.pending.take() {
            if Session::label_of(&stmt) == Some(label) {
                return stmt;
            }
            self.do_stmt(stmt, Mode::Normal);
        }
        while let Some(stmt) = parser.next() {
            if Session::label_of(&stmt) == Some(label) {
                return stmt;
            }
            self.do_stmt(stmt, Mode::Normal);
        }
        panic!("reached eof in input, expected {}", label);
    }

    pub fn run_script(&mut self, script: &mut Script, parser: &mut Parser<'a>) {
        for cmd in script {
            match cmd {
                Command::CopyLine(s) => self.out.write(&s),
                Command::RunThrough(l) => {
                    let stmt = self.run_upto(&l, parser);
                    self.do_stmt(stmt, Mode::Normal);
                }
                Command::RunUntil(l) => {
                    let stmt = self.run_upto(&l, parser);
                    self.pending = Some(stmt);
                }
                Command::Skip(l) => {
                    let stmt = self.run_upto(&l, parser);
                    self.do_stmt(stmt, Mode::Skip);
                }
                Command::BoundForm(labels) => self.bound_form.extend(labels),
                Command::Assume(l) => {
                    let stmt = self.run_upto(&l, parser);
                    self.do_stmt(stmt, Mode::Assume);
                }
                Command::ProveInstance(l, body) => {
                    self.instance_proofs.insert(l, body);
                }
                Command::Prove(l, body) => {
                    let stmt = self.run_upto(&l, parser);
                    self.manual_proof = Some(body);
                    self.do_stmt(stmt, Mode::Assume);
                }
            }
        }
    }

    fn do_stmt(&mut self, stmt: Statement<'a>, mode: Mode) {
        match stmt {
            Statement::Comment(s) => match parse_section(s) {
                Some((level, title)) => {
                    self.comment = None;
                    self.out.write(&format!("/*# {} {} */\n", level, sanitize_comment(&title)));
                }
                None => self.comment = Some(s),
            },
            Statement::StartBlock => self.blocks.push((self.hyps.len(), self.dvs.len())),
            Statement::EndBlock => {
                let (h, d) = self.blocks.pop().unwrap();
                let reset = self.hyps[h..].iter().any(|&(_, ref hyp)| if let Hyp::F(..) = *hyp { true } else { false });
                self.hyps.truncate(h);
                if reset {
                    self.reset_vars();
                }
                self.dvs.truncate(d);
            }
            Statement::Distinct(vars) => self.dvs.push(vars),
            Statement::Floating(label, tc, var) => {
                self.hyps.push((label, Hyp::F(tc, var)));
                self.vars.insert(var, tc);
                self.declare_var(var, tc);
            }
            Statement::Essential(label, expr) => self.hyps.push((label, Hyp::E(expr))),
            Statement::Axiom(label, concl) => {
                let frame = self.make_frame(&concl);
                if concl[0] == "|-" {
                    let comment = self.comment.take();
                    self.write_stmt(label, &frame, comment, None);
                } else {
                    self.comment = None;
                    self.do_syntax(label, &concl);
                }
                self.frames.insert(label, Rc::new(frame));
            }
            Statement::Proof(label, concl, proof) => {
                let frame = self.make_frame(&concl);
                let comment = self.comment.take();
                if concl[0] == "|-" {
                    match mode {
                        Mode::Normal => {
                            let lines = self.replay_proof(label, &frame, &proof, &[]);
                            self.write_stmt(label, &frame, comment, Some(&lines));
                        }
                        Mode::Assume => self.write_stmt(label, &frame, comment, None),
                        Mode::Skip => (),
                    }
                }
                self.frames.insert(label, Rc::new(frame));
                let start = self.blocks.first().map_or(self.hyps.len(), |b| b.0);
                let floats = self.hyps[start..].iter().filter_map(|&(l, ref hyp)| match *hyp {
                    Hyp::F(tc, v) => Some((l, tc, v)),
                    _ => None,
                }).collect();
                self.proofs.insert(label, Rc::new(SavedProof { steps: proof, floats }));
            }
            _ => (),
        }
    }

    /// Makes the active variables those of the active hypotheses.
    fn reset_vars(&mut self) {
        self.vars = self.hyps.iter().filter_map(|&(_, ref hyp)| match *hyp {
            Hyp::F(tc, v) => Some((v, tc)),
            _ => None,
        }).collect();
    }

    fn declare_var(&mut self, var: &'a str, tc: &'a str) {
        if let Some(&old_tc) = self.declared.get(var) {
            if old_tc != tc {
                panic!("variable {} redeclared with typecode {} (was {})", var, tc, old_tc);
            }
            return;
        }
        self.declared.insert(var, tc);
        let name = gh_var(var);
        if tc == SETVAR {
            self.out.write(&format!("bound {}: {};\n", name, tc));
            self.out.write(&format!("var {}': {};\n", name, tc));
        } else {
            self.out.write(&format!("var {}: {};\n", name, tc));
        }
    }

    fn make_frame(&self, concl: &[&'a str]) -> Frame<'a> {
        let mut mand = Vec::new();
        {
            let mut add = |toks: &[&'a str]| for &t in &toks[1..] {
                if self.vars.contains_key(t) && !mand.contains(&t) {
                    mand.push(t);
                }
            };
            for &(_, ref hyp) in &self.hyps {
                if let Hyp::E(ref e) = *hyp {
                    add(e);
                }
            }
            add(concl);
        }
        let hyps = self.hyps.iter().filter(|&&(_, ref hyp)| match *hyp {
            Hyp::F(_, v) => mand.contains(&v),
            Hyp::E(_) => true,
        }).cloned().collect();
        let mut dv = Vec::new();
        for d in &self.dvs {
            for (i, &a) in d.iter().enumerate() {
                for &b in &d[i + 1..] {
                    if mand.contains(&a) && mand.contains(&b) && !dv.contains(&(a, b)) {
                        dv.push((a, b));
                    }
                }
            }
        }
        Frame { hyps, concl: concl.to_vec(), dv }
    }

    fn do_syntax(&mut self, label: &'a str, concl: &[&'a str]) {
        let tc = concl[0];
        let pattern = concl[1..].to_vec();
        let var_tc = pattern.iter().map(|t| self.vars.get(t).cloned()).collect();
        let ax = SyntaxAx { label, tc, pattern, var_tc };
        let pvars = ax.vars();
        let has_body = pvars.iter().any(|&(_, vtc)| vtc != SETVAR);
        let vars: Vec<_> = pvars.iter().enumerate().map(|(i, &(v, vtc))| {
            let binds = vtc == SETVAR && has_body && !NON_BINDING.contains(&(label, i));
            (v, vtc, binds)
        }).collect();
        self.grammar.add(ax);
        let binders: Vec<_> = (0..vars.len()).filter(|&i| vars[i].2).collect();
        let scope: Vec<Vec<_>> = (0..vars.len()).map(|i| {
            binders.iter().cloned().filter(|&b| !UNSCOPED.contains(&(label, i, b))).collect()
        }).collect();
        let mut arg_types = String::new();
        for (&(_, vtc, binds), scope) in vars.iter().zip(&scope) {
            if binds {
                continue;
            }
            if vtc != SETVAR && !scope.is_empty() {
                arg_types.push_str(" (");
                for _ in scope {
                    arg_types.push_str("setvar->");
                }
                arg_types.push_str(vtc);
                arg_types.push(')');
            } else {
                arg_types.push(' ');
                arg_types.push_str(vtc);
            }
        }
        let (notation, name, prec) = match nice_notation(label) {
            Some((notation, kind, prec)) => {
                let op = match notation {
                    Notation::Infix(op) | Notation::Prefix(op) | Notation::Binder(op) => op,
                    Notation::Plain => unreachable!(),
                };
                self.out.write(&format!("syntax {{\n    {} {} {};\n}}\n", kind, op, prec));
                let rbp = if kind == "infixr" { prec - 1 } else { prec };
                (notation, op.to_string(), (prec, rbp))
            }
            None => (Notation::Plain, label.to_string(), (0, 0)),
        };
        self.out.write(&format!("term {}{} : {};\n", name, arg_types, tc));
        self.terms.push(TermInfo { name, notation, prec, vars, scope });
    }

    /// Converts a Metamath expression (starting with typecode `|-`) to Ghilbert.
    fn gh_expr(&self, label: &str, expr: &[&'a str]) -> String {
        match self.grammar.parse(&expr[1..], "wff", &self.vars) {
            Some(tree) => {
                let mut s = "|- ".to_string();
                self.print_tree(&tree, &mut s);
                s
            }
            None => panic!("{}: can't parse {}", label, expr.join(" ")),
        }
    }

    /// Writes a term with only the parentheses the Ghilbert parser needs.
    fn print_tree(&self, tree: &Rc<Tree<'a>>, s: &mut String) {
        self.print_ctx(tree, Ctx::Operand(0), s);
    }

    /// How far right a printed term extends: the lowest binding power on its
    /// right spine (an infix operator after it binds into it if stronger).
    fn right_bp(&self, tree: &Rc<Tree<'a>>) -> u32 {
        match **tree {
            Tree::Var(_) => u32::MAX,
            Tree::App(ix, ref kids) => {
                let info = &self.terms[ix];
                if let Notation::Plain = info.notation {
                    return u32::MAX;
                }
                let last = kids.last().unwrap();
                let last_parens = match **last {
                    Tree::App(lix, _) => match self.terms[lix].notation {
                        Notation::Infix(_) => self.terms[lix].prec.0 <= info.prec.1,
                        _ => false,
                    },
                    _ => false,
                };
                if last_parens {
                    info.prec.1
                } else {
                    info.prec.1.min(self.right_bp(last))
                }
            }
        }
    }

    fn print_ctx(&self, tree: &Rc<Tree<'a>>, ctx: Ctx, s: &mut String) {
        let (ix, kids) = match **tree {
            Tree::Var(v) => {
                s.push_str(&gh_var(v));
                if self.free_setvars.contains(&v) {
                    s.push('\'');
                }
                return;
            }
            Tree::App(ix, ref kids) => (ix, kids),
        };
        let info = &self.terms[ix];
        let parens = match (&info.notation, ctx) {
            (_, Ctx::Arg) => !kids.is_empty(),
            (&Notation::Plain, _) => false,
            (&Notation::Infix(_), Ctx::Operand(r)) => info.prec.0 <= r,
            (_, Ctx::Operand(_)) => false,
            (_, Ctx::Left(l)) => self.right_bp(tree) < l,
        };
        if parens {
            s.push_str("( ");
        }
        let binders: Vec<&Rc<Tree<'a>>> = info.vars.iter().zip(kids.iter())
            .filter(|&(v, _)| v.2).map(|(_, k)| k).collect();
        let bodies: Vec<&Rc<Tree<'a>>> = info.vars.iter().zip(kids.iter())
            .filter(|&(v, _)| !v.2).map(|(_, k)| k).collect();
        match info.notation {
            Notation::Infix(op) => {
                self.print_ctx(bodies[0], Ctx::Left(info.prec.0), s);
                s.push_str(&format!(" {} ", op));
                self.print_ctx(bodies[1], Ctx::Operand(info.prec.1), s);
            }
            Notation::Prefix(op) => {
                s.push_str(&format!("{} ", op));
                self.print_ctx(bodies[0], Ctx::Operand(info.prec.0), s);
            }
            Notation::Binder(op) => {
                s.push_str(&format!("{} ", op));
                self.print_ctx(binders[0], Ctx::Arg, s);
                s.push(' ');
                self.print_ctx(bodies[0], Ctx::Operand(info.prec.0), s);
            }
            Notation::Plain => {
                s.push_str(&info.name);
                let args = info.vars.iter().zip(&info.scope).filter(|&(v, _)| !v.2);
                for ((&(_, vtc, _), scope), kid) in args.zip(bodies) {
                    s.push(' ');
                    if vtc == SETVAR || scope.is_empty() {
                        self.print_ctx(kid, Ctx::Arg, s);
                    } else {
                        for &b in scope {
                            s.push_str("( \\ ");
                            self.print_ctx(&kids[b], Ctx::Arg, s);
                            s.push(' ');
                        }
                        self.print_ctx(kid, Ctx::Operand(0), s);
                        for _ in scope {
                            s.push_str(" )");
                        }
                    }
                }
            }
        }
        if parens {
            s.push_str(" )");
        }
    }

    /// Finds the mandatory setvar variables that occur in no binding position
    /// (in the statement or any proof step), and are not substituted for a
    /// bound variable of a statement used in the proof.
    fn find_free_setvars(&self, label: &str, frame: &Frame<'a>, lines: Option<&[Line<'a>]>)
        -> Vec<&'a str>
    {
        if self.bound_form.iter().any(|l| l == label) {
            return Vec::new();
        }
        let mut binding = Vec::new();
        let mut scan = |expr: &[&'a str]| {
            if let Some(tree) = self.grammar.parse(&expr[1..], "wff", &self.vars) {
                self.binding_vars(&tree, &mut binding);
            }
        };
        for &(_, ref hyp) in &frame.hyps {
            if let Hyp::E(ref e) = *hyp {
                scan(e);
            }
        }
        scan(&frame.concl);
        for line in lines.unwrap_or(&[]) {
            scan(&line.expr);
        }
        for line in lines.unwrap_or(&[]) {
            if let Some(free) = self.free_by_stmt.get(line.label) {
                for &(v, t) in &line.subst {
                    if !free.contains(&v) && !binding.contains(&t) {
                        binding.push(t);
                    }
                }
            }
        }
        frame.hyps.iter().filter_map(|&(_, ref hyp)| match *hyp {
            Hyp::F(tc, v) if tc == SETVAR && !binding.contains(&v) => Some(v),
            _ => None,
        }).collect()
    }

    fn binding_vars(&self, tree: &Rc<Tree<'a>>, result: &mut Vec<&'a str>) {
        if let Tree::App(ix, ref kids) = **tree {
            for (&(_, _, binds), kid) in self.terms[ix].vars.iter().zip(kids) {
                match **kid {
                    Tree::Var(v) if binds => if !result.contains(&v) { result.push(v) },
                    _ => self.binding_vars(kid, result),
                }
            }
        }
    }

    /// Writes an axiom (if `lines` is None) or theorem.
    fn write_stmt(&mut self, label: &'a str, frame: &Frame<'a>, comment: Option<&str>,
        lines: Option<&[Line<'a>]>)
    {
        let manual = self.manual_proof.take();
        self.free_setvars = self.find_free_setvars(label, frame, lines);
        self.free_by_stmt.insert(label, self.free_setvars.clone());
        let mut s = String::new();
        if let Some(comment) = comment {
            s.push_str(&format!("/* {} */\n", sanitize_comment(comment)));
        }
        let has_proof = lines.is_some() || manual.is_some();
        s.push_str(if has_proof { "theorem " } else { "axiom " });
        s.push_str(label);
        for &(hyp_label, ref hyp) in &frame.hyps {
            if let Hyp::E(ref e) = *hyp {
                let e = self.gh_expr(label, e);
                if has_proof {
                    s.push_str(&format!("\n  ({}: {})", hyp_label, e));
                } else {
                    s.push_str(&format!("\n  ({})", e));
                }
            }
        }
        // A `$d` becomes a not-free-in constraint with a setvar on the left
        // (for two setvars, either way round means they differ).
        let name = |v: &str| if self.free_setvars.contains(&v) {
            format!("{}'", gh_var(v))
        } else {
            gh_var(v)
        };
        let is_bound = |v: &str| self.vars[v] == SETVAR && !self.free_setvars.contains(&v);
        let notfree = frame.dv.iter().filter_map(|&(a, b)| {
            let (sa, sb) = (self.vars[a] == SETVAR, self.vars[b] == SETVAR);
            if (is_bound(a) && is_bound(b)) || !(sa || sb) {
                None  // bound variables are always distinct
            } else if sa && !is_bound(b) {
                Some(format!("{} F/ {}", name(a), name(b)))
            } else {
                Some(format!("{} F/ {}", name(b), name(a)))
            }
        }).collect::<Vec<_>>();
        if !notfree.is_empty() {
            s.push_str(&format!("\n  {}", notfree.join(", ")));
        }
        let concl = self.gh_expr(label, &frame.concl);
        if let Some(body) = manual {
            s.push_str(&format!(":\n  {} ::(\n{})\n\n", concl, body));
            self.out.write(&s);
            return;
        }
        match lines {
            None => s.push_str(&format!(":\n  {};\n\n", concl)),
            Some(lines) => {
                s.push_str(&format!(":\n  {} ::(\n", concl));
                // Only lines used other than by the next line (as `_`) need labels.
                let mut used = vec![false; lines.len()];
                for (i, line) in lines.iter().enumerate() {
                    for &arg in &line.args {
                        if arg + 1 != i {
                            used[arg] = true;
                        }
                    }
                }
                for (i, line) in lines.iter().enumerate() {
                    if used[i] {
                        s.push_str(&format!("  l{}: {}", i, line.label));
                    } else {
                        s.push_str(&format!("  {}", line.label));
                    }
                    for &arg in &line.args {
                        if arg + 1 == i {
                            s.push_str(" _");
                        } else {
                            s.push_str(&format!(" l{}", arg));
                        }
                    }
                    if line.needs_result {
                        let expr = self.subst_dummies(frame, &line.expr);
                        s.push_str(&format!("\n    [{}]\n", self.gh_expr(label, &expr)));
                    } else {
                        s.push_str(";\n");
                    }
                }
                s.push_str(")\n\n");
            }
        }
        self.out.write(&s);
    }

    /// Finds the bound setvars of a statement that a proof step makes the same
    /// variable, which Ghilbert doesn't allow. Returns a map identifying them.
    fn coincidences(&self, label: &str, subst: &[(&'a str, &'a str)]) -> Vec<(&'a str, &'a str)> {
        let free = match self.free_by_stmt.get(label) {
            Some(free) => free,
            None => return Vec::new(),
        };
        let bound: Vec<_> = subst.iter().filter(|p| !free.contains(&p.0)).collect();
        let mut map = Vec::new();
        for (i, &&(a, t)) in bound.iter().enumerate() {
            if let Some(&&(first, _)) = bound[..i].iter().find(|p| p.1 == t) {
                map.push((a, first));
            }
        }
        map
    }

    /// Gets the label of an instance of a statement with setvars identified,
    /// writing the instance if it's new. Its proof is the replayed proof of the
    /// statement, since any instance of a Metamath proof is a proof.
    fn instance(&mut self, label: &'a str, map: Vec<(&'a str, &'a str)>) -> &'a str {
        let mut name = label.to_string();
        for &(a, b) in &map {
            name.push_str(&format!(".{}={}", a, b));
        }
        if let Some((&name, _)) = self.frames.get_key_value(name.as_str()) {
            return name;
        }
        let name: &'a str = Box::leak(name.into_boxed_str());
        let frame = self.frames[label].clone();
        let inst_frame = instance_frame(&frame, &map);
        let comment = format!("Instance of {} with setvars identified.", label);
        self.manual_proof = self.instance_proofs.remove(name);
        match (self.manual_proof.is_some(), self.proofs.get(label).cloned()) {
            (false, Some(proof)) => {
                let n_hyps = self.hyps.len();
                for &(l, tc, v) in &proof.floats {
                    self.hyps.push((l, Hyp::F(tc, v)));
                    self.vars.insert(v, tc);
                }
                let lines = self.replay_proof(name, &frame, &proof.steps, &map);
                self.write_stmt(name, &inst_frame, Some(&comment), Some(&lines));
                self.hyps.truncate(n_hyps);
                self.reset_vars();
            }
            (false, None) => panic!("no proof of {}, an instance of an axiom", name),
            _ => self.write_stmt(name, &inst_frame, Some(&comment), None),
        }
        self.frames.insert(name, Rc::new(inst_frame));
        name
    }

    /// Replaces dummy wff and class variables in a result line, since Ghilbert
    /// result lines can't name dummy term variables. Any instance of a proof is
    /// still a proof. A class constant is the best replacement, because it has
    /// no free variables to break a `$d`; otherwise it's a variable of the same
    /// typecode from the statement.
    fn subst_dummies(&self, frame: &Frame<'a>, expr: &[&'a str]) -> Vec<&'a str> {
        let mand_var = |tc: &str| frame.hyps.iter().filter_map(|&(_, ref hyp)| match *hyp {
            Hyp::F(htc, v) if htc == tc => Some(v),
            _ => None,
        }).next();
        let replacement = |tc: &str| if tc == "wff" {
            mand_var(tc).or_else(|| self.grammar.constant(tc))
        } else {
            self.grammar.constant(tc).or_else(|| mand_var(tc))
        };
        let is_mand = |t: &str| frame.hyps.iter().any(|&(_, ref hyp)| match *hyp {
            Hyp::F(_, v) => v == t,
            _ => false,
        });
        expr.iter().map(|&t| match self.vars.get(t) {
            Some(&tc) if tc != SETVAR && !is_mand(t) => replacement(tc).unwrap_or(t),
            _ => t,
        }).collect()
    }

    /// Replays a proof, returning its judgment steps.
    ///
    /// The `map` argument identifies setvars of the statement, for replaying a
    /// proof as a proof of an instance.
    fn replay_proof(&mut self, label: &str, frame: &Frame<'a>, proof: &[&'a str], map: &VarMap<'a>)
        -> Vec<Line<'a>>
    {
        let mut lines = Vec::new();
        let mut stack: Vec<El<'a>> = Vec::new();
        if proof.first() == Some(&"(") {
            let pos = proof.iter().position(|&step| step == ")").expect("bad compressed proof");
            let labels = &proof[1..pos];
            let m = frame.hyps.len();
            let n = labels.len();
            let mut saved = Vec::new();
            for step in Compressed::new(&proof[pos + 1..]) {
                if step == 0 {
                    saved.push(stack.last().unwrap().clone());
                } else if step <= m {
                    let (hyp_label, ref hyp) = frame.hyps[step - 1];
                    self.push_hyp(hyp_label, hyp, map, &mut stack, &mut lines);
                } else if step <= m + n {
                    self.apply_label(label, labels[step - m - 1], frame, map, &mut stack, &mut lines);
                } else {
                    stack.push(saved[step - m - n - 1].clone());
                }
            }
        } else {
            for &step in proof {
                self.apply_label(label, step, frame, map, &mut stack, &mut lines);
            }
        }
        lines
    }

    fn push_hyp(&self, hyp_label: &'a str, hyp: &Hyp<'a>, map: &VarMap<'a>, stack: &mut Vec<El<'a>>,
        lines: &mut Vec<Line<'a>>)
    {
        match *hyp {
            Hyp::F(tc, v) => stack.push(El { expr: Rc::new(vec![tc, apply_map(map, v)]), step: None }),
            Hyp::E(ref e) => {
                let step = lines.len();
                let e: Rc<Vec<_>> = Rc::new(e.iter().map(|&t| apply_map(map, t)).collect());
                lines.push(Line { label: hyp_label, args: Vec::new(), expr: e.clone(),
                    needs_result: false, subst: Vec::new() });
                stack.push(El { expr: e, step: Some(step) });
            }
        }
    }

    fn apply_label(&mut self, thm: &str, label: &'a str, thm_frame: &Frame<'a>, map: &VarMap<'a>,
        stack: &mut Vec<El<'a>>, lines: &mut Vec<Line<'a>>)
    {
        let is_label = |h: &&(&'a str, Hyp<'a>)| h.0 == label;
        if let Some(&(hyp_label, ref hyp)) = thm_frame.hyps.iter().find(is_label)
            .or_else(|| self.hyps.iter().rev().find(is_label))
        {
            return self.push_hyp(hyp_label, hyp, map, stack, lines);
        }
        let frame = self.frames.get(label).unwrap_or_else(||
            panic!("{}: unknown label {} in proof", thm, label)).clone();
        let base = stack.len() - frame.hyps.len();
        let mut subst = HashMap::new();
        let mut setvar_subst = Vec::new();
        let mut args = Vec::new();
        for (&(_, ref hyp), el) in frame.hyps.iter().zip(&stack[base..]) {
            match *hyp {
                Hyp::F(tc, v) => {
                    if tc == SETVAR {
                        setvar_subst.push((v, el.expr[1]));
                    }
                    subst.insert(v, el.expr.clone());
                }
                Hyp::E(_) => args.push(el.step.expect("essential hyp is not a judgment")),
            }
        }
        let mut expr = Vec::new();
        for &t in &frame.concl {
            match subst.get(t) {
                Some(e) => expr.extend_from_slice(&e[1..]),
                None => expr.push(t),
            }
        }
        stack.truncate(base);
        let expr = Rc::new(expr);
        if frame.concl[0] != "|-" {
            stack.push(El { expr, step: None });
            return;
        }
        // A variable of the referenced statement that is not in its conclusion
        // is not determined by unification from below, so give the hypotheses
        // feeding it explicit result lines.
        let undetermined = frame.hyps.iter().any(|&(_, ref hyp)| match *hyp {
            Hyp::F(_, v) => !frame.concl.contains(&v),
            Hyp::E(_) => false,
        });
        if undetermined {
            for &arg in &args {
                lines[arg].needs_result = true;
            }
        }
        let inst_map: Vec<_> = self.coincidences(label, &setvar_subst);
        let (label, setvar_subst) = if inst_map.is_empty() {
            (label, setvar_subst)
        } else {
            let subst = setvar_subst.into_iter().filter(|p| !inst_map.iter().any(|m| m.0 == p.0))
                .collect();
            (self.instance(label, inst_map), subst)
        };
        let step = lines.len();
        lines.push(Line { label, args, expr: expr.clone(), needs_result: false,
            subst: setvar_subst });
        stack.push(El { expr, step: Some(step) });
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Mode {
    Normal,
    /// Record the statement but write nothing.
    Skip,
    /// Write a theorem as an axiom, without its proof.
    Assume,
}

/// Identifies setvars of a statement: each first variable becomes the second.
type VarMap<'a> = [(&'a str, &'a str)];

fn apply_map<'a>(map: &VarMap<'a>, t: &'a str) -> &'a str {
    map.iter().find(|m| m.0 == t).map_or(t, |m| m.1)
}

/// Makes the frame of an instance of a statement.
fn instance_frame<'a>(frame: &Frame<'a>, map: &VarMap<'a>) -> Frame<'a> {
    let subst = |e: &[&'a str]| e.iter().map(|&t| apply_map(map, t)).collect::<Vec<_>>();
    let hyps = frame.hyps.iter().filter_map(|&(label, ref hyp)| match *hyp {
        Hyp::F(_, v) if apply_map(map, v) != v => None,
        Hyp::F(..) => Some((label, hyp.clone())),
        Hyp::E(ref e) => Some((label, Hyp::E(subst(e)))),
    }).collect();
    let dv = frame.dv.iter().map(|&(a, b)| (apply_map(map, a), apply_map(map, b))).collect();
    Frame { hyps, concl: subst(&frame.concl), dv }
}

/// An entry on the proof replay stack.
#[derive(Clone)]
struct El<'a> {
    expr: Rc<Vec<&'a str>>,
    /// The line, if this is a judgment.
    step: Option<usize>,
}

struct Line<'a> {
    label: &'a str,
    args: Vec<usize>,
    expr: Rc<Vec<&'a str>>,
    needs_result: bool,
    /// For the setvar variables of the statement applied, what they become.
    subst: Vec<(&'a str, &'a str)>,
}

/// The name of a variable in Ghilbert, where parentheses end a token in `var`,
/// and a trailing prime means a setvar written as a term variable.
fn gh_var(var: &str) -> String {
    var.replace('(', "[").replace(')', "]").replace('\'', "''")
}

/// The level of a line of a set.mm section header, if it is one of the rules
/// that surround the title. Level 1 is the outermost.
fn rule_level(line: &str) -> Option<usize> {
    ["####", "#*#*", "=-=-", "-.-."].iter()
        .position(|rule| line.trim().starts_with(rule))
        .map(|ix| ix + 1)
}

/// Gets the level and title if a comment is a set.mm section header.
fn parse_section(comment: &str) -> Option<(usize, String)> {
    let mut lines = comment.lines();
    let level = rule_level(lines.next()?)?;
    let title: Vec<&str> = lines.take_while(|line| rule_level(line).is_none())
        .map(str::trim).collect();
    Some((level, title.join(" ")))
}

/// Keeps a Metamath comment from closing or nesting a Ghilbert comment.
fn sanitize_comment(comment: &str) -> String {
    comment.replace("*/", "* /").replace("/*", "/ *")
}
