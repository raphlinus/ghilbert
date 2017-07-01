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

//! Parser for new-style Ghilbert format.

use std::collections::BTreeMap;

use lexer::{Lexer, Token};

#[derive(Debug)]
pub struct ParseNode {
    start: usize,
    end: usize,
    pub info: Info,
    pub children: Vec<ParseNode>,
}

impl ParseNode {
    fn dummy() -> ParseNode {
        ParseNode { start: 0, end: 0, info: Info::Dummy, children: Vec::new() }
    }
}

#[derive(PartialEq, Debug)]
pub enum Info {
    // children: [syntax def], where syntax def is internal to this module
    SyntaxCmd,
    // children: kind
    KindCmd,
    // children: [vars], kind
    VarCmd,
    // children: [vars], kind
    BoundCmd,
    // children: con, [args], kind
    TermCmd,
    // children: step, [hyps], notfree, result
    AxiomCmd,
    // children: label, [hyp_names], [hyps], notfree, result, [lines]
    TheoremCmd,
    // children: con, [args]
    // children: label, step, [args], result
    // Notes: label is optional (Dummy if missing), arg = step or [lines]
    Line,
    List,
    Dummy,
    // children: kind, type
    Arrow,
    // children: bound_var, body
    Lambda,
    // children: [bound_var], var
    // Discussion question, should we also allow list of var (eg "x y F/ A B")?
    NotFree,
    Kind(Token),
    Var(Token),
    Const(Token),
    // children: [args]
    Atom(Token),  // is either Const or Var, will resolve later
    Step(Token),
}

struct Predefined {
    axiom: Token,
    bound: Token,
    kind: Token,
    term: Token,
    theorem: Token,
    var: Token,

    syntax: Token,
    infixl: Token,
    infixr: Token,

    open: Token,
    close: Token,
    open_bracket: Token,
    close_bracket: Token,
    open_brace: Token,
    close_brace: Token,
    semicolon: Token,
    colon: Token,
    colon_colon: Token,
    underline: Token,
    backslash: Token,
    arrow: Token,
    notfree: Token,
    comma: Token,
}

#[derive(PartialEq, Eq, Debug)]
pub enum Error {
    Eof,
    UnexpectedEof,
    ExpectedNum,
    SyntaxError,
}

impl Predefined {
    fn new(lexer: &mut Lexer) -> Predefined {
        Predefined {
            axiom: lexer.intern("axiom"),
            bound: lexer.intern("bound"),
            kind: lexer.intern("kind"),
            term: lexer.intern("term"),
            theorem: lexer.intern("theorem"),
            var: lexer.intern("var"),

            // keywords for syntax
            syntax: lexer.intern("syntax"),
            infixl: lexer.intern("infixl"),
            infixr: lexer.intern("infixr"),

            open: lexer.intern("("),
            close: lexer.intern(")"),
            open_bracket: lexer.intern("["),
            close_bracket: lexer.intern("]"),
            open_brace: lexer.intern("{"),
            close_brace: lexer.intern("}"),
            semicolon: lexer.intern(";"),
            colon: lexer.intern(":"),
            colon_colon: lexer.intern("::"),
            underline: lexer.intern("_"),
            backslash: lexer.intern("\\"),
            arrow: lexer.intern("->"),
            notfree: lexer.intern("F/"),
            comma: lexer.intern(","),
        }
    }
}

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    predefined: Predefined,
    binops: BTreeMap<Token, Binop>,
}

#[derive(Clone, Copy)]
struct Binop {
    lbp: u32,
    rbp: u32,
}

impl Binop {
    fn infixl(prec: u32) -> Binop {
        Binop{ lbp: prec, rbp: prec }
    }

    fn infixr(prec: u32) -> Binop {
        Binop{ lbp: prec, rbp: prec - 1}
    }
}

impl<'a> Parser<'a> {
    pub fn new(mut lexer: Lexer) -> Parser {
        let predefined = Predefined::new(&mut lexer);
        Parser {
            lexer,
            predefined,
            binops: BTreeMap::new(),
        }
    }

    fn start(&mut self) -> usize {
        self.lexer.skip_whitespace();
        self.lexer.pos()
    }

    fn node(&self, start: usize, info: Info, children: Vec<ParseNode>) -> ParseNode {
        ParseNode {
            start,
            end: self.lexer.pos(),
            info,
            children,
        }
    }

    fn leaf(&self, start: usize, info: Info) -> ParseNode {
        self.node(start, info, Vec::new())
    }

    fn list(&self, start: usize, children: Vec<ParseNode>) -> ParseNode {
        self.node(start, Info::List, children)
    }

    /// Expects a token (consuming the next token either way).
    fn expect(&mut self, expected: Token) -> Result<(), Error> {
        let token = self.lexer.next().ok_or(Error::Eof)?;
        if token == expected {
            Ok(())
        } else {
            Err(Error::SyntaxError)
        }
    }

    // convenience function to get the next token, eof is error
    fn next(&mut self) -> Result<Token, Error> {
        self.lexer.next().ok_or(Error::UnexpectedEof)
    }

    pub fn parse_cmd(&mut self) -> Result<ParseNode, Error> {
        let start = self.start();
        let token = self.lexer.next().ok_or(Error::Eof)?;
        if token == self.predefined.kind {
            let k_s = self.start();
            let kind = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
            let children = vec![self.leaf(k_s, Info::Kind(kind))];
            let semicolon = self.predefined.semicolon;
            self.expect(semicolon)?;
            Ok(self.node(start, Info::KindCmd, children))
        } else if token == self.predefined.var {
            let v_s = self.start();
            let mut vars = Vec::new();
            loop {
                let s = self.start();
                let token = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
                if token == self.predefined.colon {
                    break;
                } else {
                    vars.push(self.leaf(s, Info::Var(token)));
                }
            }
            let vars = self.list(v_s, vars);
            let k_s = self.start();
            let kind = self.next()?;
            let semicolon = self.predefined.semicolon;
            self.expect(semicolon)?;
            let children = vec![vars, self.leaf(k_s, Info::Kind(kind))];
            Ok(self.node(start, Info::VarCmd, children))
        } else if token == self.predefined.bound {
            let v_s = self.start();
            let mut vars = Vec::new();
            loop {
                let s = self.start();
                let token = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
                if token == self.predefined.colon {
                    break;
                } else {
                    vars.push(self.leaf(s, Info::Var(token)));
                }
            }
            let vars = self.list(v_s, vars);
            let k_s = self.start();
            let kind = self.next()?;
            let semicolon = self.predefined.semicolon;
            self.expect(semicolon)?;
            let children = vec![vars, self.leaf(k_s, Info::Kind(kind))];
            Ok(self.node(start, Info::BoundCmd, children))
        } else if token == self.predefined.term {
            let c_s = self.start();
            // Note: long here means that nullary terms need a space between const and :
            let con = self.lexer.next_long().ok_or(Error::UnexpectedEof)?;
            let con = self.leaf(c_s, Info::Const(con));
            let a_s = self.start();
            let mut args = Vec::new();
            loop {
                // Note: an arg might be a lambda term, not just a token.
                let colon = self.predefined.colon;
                if self.lexer.expect(colon) {
                    break;
                }
                let ty = self.parse_type()?;
                args.push(ty);
            }
            let args = self.list(a_s, args);
            let k_s = self.start();
            let kind = self.next()?;
            let kind_node = self.leaf(k_s, Info::Kind(kind));
            let semicolon = self.predefined.semicolon;
            self.expect(semicolon)?;
            let children = vec![con, args, kind_node];
            Ok(self.node(start, Info::TermCmd, children))
        } else if token == self.predefined.axiom {
            self.parse_axiom(start)
        } else if token == self.predefined.theorem {
            self.parse_theorem(start)
        } else if token == self.predefined.syntax {
            self.parse_syntax(start)
        } else {
            Err(Error::SyntaxError)
        }
    }

    // recognizes either "kind" or "(" (kind "->")* kind ")"
    fn parse_type(&mut self) -> Result<ParseNode, Error> {
        let start = self.start();
        let kind = self.next()?;
        if kind == self.predefined.open {
            // arrow term
            let mut subterms = Vec::new();
            loop {
                let s_s = self.start();
                let subterm = self.next()?;
                subterms.push(self.leaf(s_s, Info::Kind(subterm)));
                let close = self.predefined.close;
                if self.lexer.expect(close) {
                    break;
                }
                let arrow = self.predefined.arrow;
                if !self.lexer.expect(arrow) {
                    return Err(Error::SyntaxError);
                }
            }
            let mut result = subterms.pop().unwrap();
            while let Some(argtype) = subterms.pop() {
                let children = vec![argtype, result];
                result = self.node(start, Info::Arrow, children);
            }
            Ok(result)
        } else {
            Ok(self.leaf(start, Info::Kind(kind)))
        }
    }

    fn parse_axiom(&mut self, start: usize) -> Result<ParseNode, Error> {
        let step = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
        let step = self.leaf(start, Info::Step(step));
        let h_s = self.start();
        let mut hyps = Vec::new();
        let colon = self.predefined.colon;
        let mut notfree = ParseNode::dummy();
        loop {
            if self.lexer.expect(colon) {
                break;
            }
            let tok = self.lexer.peek().ok_or(Error::UnexpectedEof)?;
            if tok == self.predefined.open {
                hyps.push(self.parse_term(None)?);
            } else {
                notfree = self.parse_not_free()?;
                self.expect(colon)?;
                break;
            }
        }
        let hyps_node = self.list(h_s, hyps);
        let semicolon = self.predefined.semicolon;
        let result = self.parse_term(Some(semicolon))?;
        self.expect(semicolon)?;
        let children = vec![step, hyps_node, notfree, result];
        Ok(self.node(start, Info::AxiomCmd, children))
    }

    fn parse_theorem(&mut self, start: usize) -> Result<ParseNode, Error> {
        let step = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
        let step = self.leaf(start, Info::Step(step));
        let mut hyps = Vec::new();
        let mut hyp_names = Vec::new();
        let colon = self.predefined.colon;
        let open = self.predefined.open;
        let h_s = self.start();
        let mut notfree = ParseNode::dummy();
        loop {
            if self.lexer.expect(colon) {
                break;
            }
            if self.lexer.expect(open) {
                let h_s = self.start();
                let hyp_name = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
                hyp_names.push(self.leaf(h_s,Info::Step(hyp_name)));
                self.expect(colon)?;
                let close = self.predefined.close;
                hyps.push(self.parse_term(Some(close))?);
                self.expect(close)?;
            } else {
                notfree = self.parse_not_free()?;
                self.expect(colon)?;
                break;
            }
        }
        let hyp_names_node = self.list(h_s, hyp_names);
        let hyps_node = self.list(h_s, hyps);
        let colon_colon = self.predefined.colon_colon;
        let result = self.parse_term(Some(colon_colon))?;
        self.expect(colon_colon)?;

        // the proof
        self.expect(open)?;
        let proof = self.parse_proof()?;
        let children = vec![step, hyp_names_node, hyps_node, notfree, result, proof];
        Ok(self.node(start, Info::TheoremCmd, children))
    }

    // Note: at this point, the open paren of the proof has already been consumed
    fn parse_proof(&mut self) -> Result<ParseNode, Error> {
        let start = self.start();
        let open = self.predefined.open;
        let close = self.predefined.close;
        let open_bracket = self.predefined.open_bracket;
        let close_bracket = self.predefined.close_bracket;
        let semicolon = self.predefined.semicolon;
        let mut lines = Vec::new();
        let mut done = false;
        while !done {
            let mut label = ParseNode::dummy();
            let l_s = self.start();
            let mut tok = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
            let maybe_label = self.leaf(l_s, Info::Step(tok));
            //println!("tok {:?}", tok);
            if tok == close {
                break;
            }
            let mut t_s = l_s;
            if self.lexer.expect(self.predefined.colon) {
                label = maybe_label;
                t_s = self.start();
                tok = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
            }
            let step = self.leaf(t_s, Info::Step(tok));
            let a_s = self.start();
            let mut args = Vec::new();
            let mut result = ParseNode::dummy();
            loop {
                let t_s = self.start();
                let tok = self.next()?;
                if tok == open_bracket {
                    result = self.parse_term(Some(close_bracket))?;
                    self.expect(close_bracket)?;
                    break;
                } else if tok == semicolon {
                    break;
                } else if tok == close {
                    done = true;
                    break;
                } else if tok == open {
                    args.push(self.parse_proof()?);
                } else if tok == self.predefined.underline {
                    args.push(self.leaf(t_s, Info::Dummy));
                } else {
                    args.push(self.leaf(t_s, Info::Step(tok)));
                }
            }
            let children = vec![label, step, self.list(a_s, args), result];
            //println!("line: {:?}", children);
            lines.push(self.node(start, Info::Line, children));
        }
        Ok(self.list(start, lines))
    }

    fn parse_term(&mut self, closer: Option<Token>) -> Result<ParseNode, Error> {
        self.parse_term_rec(closer, 0)
    }

    // This method implements Pratt-style precedence parsing.
    fn parse_term_rec(&mut self, closer: Option<Token>, rbp: u32) -> Result<ParseNode, Error> {
        let start = self.start();
        let mut l = self.parse_term_unary(closer, rbp)?;
        while let Some(tok) = self.lexer.peek() {
            if let Some(&op) = self.binops.get(&tok) {
                if rbp < op.lbp {
                    let _ = self.lexer.next();
                    let r = self.parse_term_rec(closer, op.rbp)?;
                    l = self.node(start, Info::Atom(tok), vec![l, r]);
                    continue;
                }
            }
            break;
        }
        Ok(l)
    }

    fn parse_term_unary(&mut self, closer: Option<Token>, rbp: u32) -> Result<ParseNode, Error> {
        let start = self.start();
        let open = self.predefined.open;
        let close = self.predefined.close;
        if self.lexer.expect(open) {
            let result = self.parse_term(Some(close))?;
            self.expect(close)?;
            Ok(result)
        } else if self.lexer.expect(self.predefined.backslash) {
            let b_s = self.start();
            let bound_var = self.next()?;
            let body = self.parse_term_rec(closer, rbp)?;
            let children = vec![self.leaf(b_s, Info::Var(bound_var)), body];
            Ok(self.node(start, Info::Lambda, children))
        } else {
            let atom = self.next()?;
            let mut args = Vec::new();
            loop {
                let t_s = self.start();
                if let Some(tok) = self.lexer.peek() {
                    if Some(tok) == closer || self.binops.contains_key(&tok) {
                        break;
                    }
                    let _ = self.lexer.next();
                    if tok == open {
                        args.push(self.parse_term(Some(close))?);
                        self.expect(close)?;
                    } else {
                        args.push(self.leaf(t_s, Info::Atom(tok)))
                    }
                } else {
                    break;
                }
            }
            Ok(self.node(start, Info::Atom(atom), args))
        }
    }

    fn parse_not_free(&mut self) -> Result<ParseNode, Error> {
        let mut result = Vec::new();
        let start = self.start();
        loop {
            let l_s = self.start();
            let mut vars = Vec::new();
            let notfree = self.predefined.notfree;
            loop {
                let v_s = self.start();
                if self.lexer.peek() == Some(notfree) {
                    break;
                }
                let var = self.next()?;
                vars.push(self.leaf(v_s, Info::Var(var)));
            }
            let vars_node = self.list(l_s, vars);
            self.expect(notfree)?;
            let t_s = self.start();
            let tvar = self.next()?;
            let children = vec![vars_node, self.leaf(t_s, Info::Var(tvar))];
            result.push(self.node(l_s, Info::NotFree, children));
            if !self.lexer.expect(self.predefined.comma) {
                break;
            }
        }
        println!("{:?}", result);
        Ok(self.list(start, result))
    }

    // Support for syntax (note: this is expected to change quite a bit, to support
    // typesetting, more sophisticated grammars, etc.).

    /// Parses and immediately applies syntax definitions.
    ///
    /// The returned syntax node is empty; the syntax definitions are applied
    /// as a side effect, rather than being returned. (If there are other uses
    /// for the definitions, this will change)
    fn parse_syntax(&mut self, start: usize) -> Result<ParseNode, Error> {
        let open_brace = self.predefined.open_brace;
        let result = Vec::new();
        self.expect(open_brace)?;
        loop {
            let tok = self.next()?;
            if tok == self.predefined.close_brace {
                break;
            }
            if tok == self.predefined.infixl || tok == self.predefined.infixr {
                let op = self.lexer.next_long().ok_or(Error::UnexpectedEof)?;
                let prec = self.lexer.next_u32().ok_or(Error::ExpectedNum)?;
                let semicolon = self.predefined.semicolon;
                self.expect(semicolon)?;
                let binop = if tok == self.predefined.infixl {
                    Binop::infixl(prec)
                } else {
                    // Note: prec == 0 could panic
                    Binop::infixr(prec)
                };
                self.binops.insert(op, binop);
            }
        }
        Ok(self.node(start, Info::SyntaxCmd, result))
    }

    pub fn backslash(&self) -> Token {
        self.predefined.backslash
    }

    pub fn dump_tree(&self, node: &ParseNode) {
        self.dump_tree_rec(node, 0);
    }

    pub fn dump_tree_rec(&self, node: &ParseNode, depth: usize) {
        for _ in 0..depth {
            print!("  ");
        }
        match node.info {
            Info::SyntaxCmd => println!("syntax"),
            Info::KindCmd => println!("kind"),
            Info::VarCmd => println!("var"),
            Info::BoundCmd => println!("bound"),
            Info::TermCmd => println!("term"),
            Info::AxiomCmd => println!("axiom"),
            Info::TheoremCmd => println!("theorem"),
            Info::Line => println!("line"),
            Info::List => println!("[]"),
            Info::Dummy => println!("_"),
            Info::Arrow => println!("->"),
            Info::Lambda => println!("\\"),
            Info::NotFree => println!("F/"),
            Info::Kind(t) => println!("kind {}", self.lexer.tok_str(t)),
            Info::Var(t) => println!("var {}", self.lexer.tok_str(t)),
            Info::Const(t) => println!("const {}", self.lexer.tok_str(t)),
            Info::Atom(t) => println!("atom {}", self.lexer.tok_str(t)),
            Info::Step(t) => println!("step {}", self.lexer.tok_str(t)),
        }
        for child in &node.children {
            self.dump_tree_rec(child, depth + 1);
        }
    }

    /// Returns the string for the given token.
    pub fn tok_str(&self, tok: Token) -> &str {
        self.lexer.tok_str(tok)
    }
}
