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

use lexer::{Lexer, Token};

#[derive(Debug)]
pub struct ParseNode {
    // We'll add syncing to source locations later.
    /*
    start: usize,
    end: usize,
    */
    pub info: Info,
    pub children: Vec<ParseNode>,
}

impl ParseNode {
    fn leaf(info: Info) -> ParseNode {
        ParseNode { info, children: Vec::new() }
    }

    fn list(children: Vec<ParseNode>) -> ParseNode {
        ParseNode { info: Info::List, children }
    }
}

#[derive(Debug)]
pub enum Info {
    // children: kind
    KindCmd,
    // children: [vars], kind
    VarCmd,
    // children: con, [args], kind
    TermCmd,
    // children: step, [hyps], result
    AxiomCmd,
    // children: label, [hyp_names], [hyps], [lines]
    TheoremCmd,
    // children: con, [args]
    // children: label, step, [args], result
    // Notes: label is optional (Dummy if missing), arg = step or [lines]
    Line,
    List,
    Dummy,
    Kind(Token),
    Var(Token),
    Const(Token),
    // children: [args]
    Atom(Token),  // is either Const or Var, will resolve later
    Step(Token),
}

struct Predefined {
    axiom: Token,
    kind: Token,
    term: Token,
    theorem: Token,
    var: Token,
    open: Token,
    close: Token,
    open_bracket: Token,
    close_bracket: Token,
    semicolon: Token,
    colon: Token,
    colon_colon: Token,
    underline: Token,
}

#[derive(PartialEq, Eq, Debug)]
pub enum Error {
    Eof,
    UnexpectedEof,
    SyntaxError,
}

impl Predefined {
    fn new(lexer: &mut Lexer) -> Predefined {
        Predefined {
            axiom: lexer.intern("axiom"),
            kind: lexer.intern("kind"),
            term: lexer.intern("term"),
            theorem: lexer.intern("theorem"),
            var: lexer.intern("var"),
            open: lexer.intern("("),
            close: lexer.intern(")"),
            open_bracket: lexer.intern("["),
            close_bracket: lexer.intern("]"),
            semicolon: lexer.intern(";"),
            colon: lexer.intern(":"),
            colon_colon: lexer.intern("::"),
            underline: lexer.intern("_"),
        }
    }
}

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    predefined: Predefined,
}

impl<'a> Parser<'a> {
    pub fn new(mut lexer: Lexer) -> Parser {
        let predefined = Predefined::new(&mut lexer);
        Parser {
            lexer,
            predefined,
        }
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

    pub fn parse_cmd(&mut self) -> Result<ParseNode, Error> {
        let token = self.lexer.next().ok_or(Error::Eof)?;
        if token == self.predefined.kind {
            let kind = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
            let children = vec![ParseNode::leaf(Info::Kind(kind))];
            let semicolon = self.predefined.semicolon;
            self.expect(semicolon)?;
            Ok(ParseNode { info: Info::KindCmd, children })
        } else if token == self.predefined.var {
            let mut vars = Vec::new();
            loop {
                let token = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
                if token == self.predefined.colon {
                    break;
                } else {
                    vars.push(ParseNode::leaf(Info::Var(token)));
                }
            }
            let kind = self.lexer.next().ok_or(Error::UnexpectedEof)?;
            let semicolon = self.predefined.semicolon;
            self.expect(semicolon)?;
            let vars = ParseNode::list(vars);
            let children = vec![vars, ParseNode::leaf(Info::Kind(kind))];
            Ok(ParseNode { info: Info::VarCmd, children })
        } else if token == self.predefined.term {
            // Note: long here means that nullary terms need a space between const and :
            let con = self.lexer.next_long().ok_or(Error::UnexpectedEof)?;
            let con = ParseNode::leaf(Info::Const(con));
            let mut args = Vec::new();
            loop {
                // Note: an arg might be a lambda term, not just a token.
                let token = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
                if token == self.predefined.colon {
                    break;
                } else {
                    args.push(ParseNode::leaf(Info::Var(token)));
                }
            }
            let kind = self.lexer.next().ok_or(Error::UnexpectedEof)?;
            let semicolon = self.predefined.semicolon;
            self.expect(semicolon)?;
            let args = ParseNode { info: Info::List, children: args };
            let children = vec![con, args, ParseNode::leaf(Info::Kind(kind))];
            Ok(ParseNode { info: Info::TermCmd, children })
        } else if token == self.predefined.axiom {
            self.parse_axiom()
        } else if token == self.predefined.theorem {
            self.parse_theorem()
        } else {
            Err(Error::SyntaxError)
        }
    }

    fn parse_axiom(&mut self) -> Result<ParseNode, Error> {
        let step = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
        let step = ParseNode::leaf(Info::Step(step));
        let mut hyps = Vec::new();
        let colon = self.predefined.colon;
        loop {
            if self.lexer.expect(colon) {
                break;
            }
            let tok = self.lexer.peek().ok_or(Error::UnexpectedEof)?;
            if tok == self.predefined.open {
                hyps.push(self.parse_term(None)?);
            } else {
                return Err(Error::SyntaxError);
            }
        }
        let semicolon = self.predefined.semicolon;
        let result = self.parse_term(Some(semicolon))?;
        self.expect(semicolon)?;
        let children = vec![step, ParseNode::list(hyps), result];
        Ok(ParseNode { info: Info::AxiomCmd, children })
    }

    fn parse_theorem(&mut self) -> Result<ParseNode, Error> {
        let step = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
        let step = ParseNode::leaf(Info::Step(step));
        let mut hyps = Vec::new();
        let mut hyp_names = Vec::new();
        let colon = self.predefined.colon;
        let open = self.predefined.open;
        loop {
            if self.lexer.expect(colon) {
                break;
            }
            self.expect(open)?;
            let hyp_name = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
            hyp_names.push(ParseNode::leaf(Info::Step(hyp_name)));
            self.expect(colon)?;
            let close = self.predefined.close;
            hyps.push(self.parse_term(Some(close))?);
            self.expect(close)?;
        }
        let colon_colon = self.predefined.colon_colon;
        let result = self.parse_term(Some(colon_colon))?;
        self.expect(colon_colon)?;

        // the proof
        self.expect(open);
        let proof = self.parse_proof()?;
        let children = vec![step, ParseNode::list(hyp_names), ParseNode::list(hyps), result, proof];
        Ok(ParseNode { info: Info::TheoremCmd, children })
    }

    // Note: at this point, the open paren of the proof has already been consumed
    fn parse_proof(&mut self) -> Result<ParseNode, Error> {
        let open = self.predefined.open;
        let close = self.predefined.close;
        let open_bracket = self.predefined.open_bracket;
        let close_bracket = self.predefined.close_bracket;
        let semicolon = self.predefined.semicolon;
        let mut lines = Vec::new();
        let mut done = false;
        while !done {
            let mut label = ParseNode::leaf(Info::Dummy);
            let mut tok = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
            //println!("tok {:?}", tok);
            if tok == close {
                break;
            }
            if self.lexer.expect(self.predefined.colon) {
                label = ParseNode::leaf(Info::Step(tok));
                tok = self.lexer.next_medium().ok_or(Error::UnexpectedEof)?;
            }
            let step = ParseNode::leaf(Info::Step(tok));
            let mut args = Vec::new();
            let mut result = ParseNode::leaf(Info::Dummy);
            loop {
                let tok = self.lexer.next().ok_or(Error::UnexpectedEof)?;
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
                } else {
                    // Note: this (currently) takes care of underline case
                    args.push(ParseNode::leaf(Info::Step(tok)));
                }
            }
            let children = vec![label, step, ParseNode::list(args), result];
            //println!("line: {:?}", children);
            lines.push(ParseNode { info: Info::Line, children });
        }
        Ok(ParseNode::list(lines))
    }

    fn parse_term(&mut self, closer: Option<Token>) -> Result<ParseNode, Error> {
        let open = self.predefined.open;
        let close = self.predefined.close;
        if self.lexer.expect(open) {
            let result = self.parse_term(Some(close))?;
            self.expect(close)?;
            Ok(result)
        } else {
            let atom = self.lexer.next().ok_or(Error::UnexpectedEof)?;
            let mut args = Vec::new();
            loop {
                if let Some(tok) = self.lexer.peek() {
                    if Some(tok) == closer {
                        break;
                    }
                    let _ = self.lexer.next();
                    if tok == open {
                        args.push(self.parse_term(Some(close))?);
                        self.expect(close)?;
                    } else {
                        args.push(ParseNode::leaf(Info::Atom(tok)))
                    }
                } else {
                    break;
                }
            }
            Ok(ParseNode { info: Info::Atom(atom), children: args })
            /*
            let atom = ParseNode::leaf(Info::Atom(atom));
            if args.is_empty() {
                Ok(atom)
            } else {
                let args = ParseNode::list(args);
                let children = vec![atom, args];
                Ok(ParseNode { info: Info::Term, children })
            }
            */
        }
    }

    pub fn dump_tree(&self, node: &ParseNode) {
        self.dump_tree_rec(node, 0);
    }

    pub fn dump_tree_rec(&self, node: &ParseNode, depth: usize) {
        for _ in 0..depth {
            print!("  ");
        }
        match node.info {
            Info::KindCmd => println!("kind"),
            Info::VarCmd => println!("var"),
            Info::TermCmd => println!("term"),
            Info::AxiomCmd => println!("axiom"),
            Info::TheoremCmd => println!("theorem"),
            Info::Line => println!("line"),
            Info::List => println!("[]"),
            Info::Dummy => println!("_"),
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
