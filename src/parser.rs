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
struct ParseNode {
    // We'll add syncing to source locations later.
    /*
	start: usize,
	end: usize,
    */
	info: Info,
	children: Vec<ParseNode>,
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
enum Info {
	KindCmd,
    VarCmd,
    TermCmd,
    AxiomCmd,
    Term,
    List,
	Kind(Token),
    Var(Token),
    Const(Token),
    Atom(Token),  // is either Const or Var, will resolve later
    Step(Token),
}

struct Predefined {
    axiom: Token,
    kind: Token,
    term: Token,
    var: Token,
    open: Token,
    close: Token,
    semicolon: Token,
    colon: Token,
}

#[derive(PartialEq, Eq, Debug)]
enum Error {
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
            var: lexer.intern("var"),
            open: lexer.intern("("),
            close: lexer.intern(")"),
            semicolon: lexer.intern(";"),
            colon: lexer.intern(":"),
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

    fn parse_term(&mut self, closer: Option<Token>) -> Result<ParseNode, Error> {
        let open = self.predefined.open;
        let close = self.predefined.close;
        if self.lexer.expect(open) {
            let result = self.parse_term(Some(close))?;
            self.expect(close)?;
            Ok(result)
        } else {
            let atom = self.lexer.next().ok_or(Error::UnexpectedEof)?;
            let atom = ParseNode::leaf(Info::Atom(atom));
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
            if args.is_empty() {
                Ok(atom)
            } else {
                let args = ParseNode::list(args);
                let children = vec![atom, args];
                Ok(ParseNode { info: Info::Term, children })
            }
        }
    }
}
