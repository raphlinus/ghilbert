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

//! A parser for compressed Metamath format files.

pub struct Scanner<'a> {
    text: &'a str,
    ix: usize,
}

#[derive(Debug)]
pub enum Token<'a> {
    Comment(&'a str),
    Keyword(char),
    Symbol(&'a str),
}

impl<'a> Scanner<'a> {
    pub fn new(text: &'a str) -> Scanner {
        Scanner { text, ix: 0 }
    }

    fn comment(&mut self) -> Option<Token<'a>> {
        if let Some(i) = self.text[self.ix ..].find("$)") {
            let tok = Token::Comment(&self.text[self.ix .. self.ix + i].trim());
            self.ix += i + 2;
            return Some(tok);
        }
        self.ix = self.text.len();
        None
    }

    fn next_skip_comment(&mut self) -> Option<Token<'a>> {
        while let Some(tok) = self.next() {
            match tok {
                Token::Comment(_) => (),
                _ => return Some(tok),
            }
        }
        None
    }
}

impl<'a> Iterator for Scanner<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Token<'a>> {
        for (i, c) in self.text[self.ix ..].char_indices() {
            match c {
                ' ' | '\t' | '\r' | '\n' => (),
                '$' => {
                    if let Some(c2) = self.text[self.ix + i + 1 ..].chars().next() {
                        self.ix += i + 1 + c2.len_utf8();
                        if c2 == '(' {
                            return self.comment();
                        } else {
                            return Some(Token::Keyword(c2));
                        }
                    } else {
                        panic!("Unexpected eof after $");
                    }
                }
                _ => {
                    let start = self.ix + i;
                    let mut end = self.text.len();
                    for (i, c) in self.text[start..].char_indices() {
                        match c {
                            ' ' | '\t' | '\r' | '\n' => {
                                end = start + i;
                                break;
                            }
                            _ => (),
                        }
                    }
                    self.ix = end;
                    return Some(Token::Symbol(&self.text[start..end]));
                }
            }
        }
        self.ix = self.text.len();
        None
    }
}

#[derive(Debug)]
pub enum Statement<'a> {
    Axiom(&'a str, Vec<&'a str>),
    Constant(Vec<&'a str>),
    Distinct(Vec<&'a str>),
    Variable(Vec<&'a str>),
    Essential(&'a str, Vec<&'a str>),
    Floating(&'a str, &'a str, &'a str),  // label, const, var
    // TODO: proof should also hold comment
    Proof(&'a str, Vec<&'a str>, Vec<&'a str>),
    StartBlock,
    EndBlock,
}

pub struct Parser<'a> {
    scanner: Scanner<'a>
}

impl<'a> Parser<'a> {
    pub fn new(scanner: Scanner<'a>) -> Parser {
        Parser { scanner }
    }

    /// Get a list of symbols terminated by $.
    fn symbol_list(&mut self) -> Vec<&'a str> {
        let mut result = Vec::new();
        while let Some(tok) = self.scanner.next_skip_comment() {
            match tok {
                Token::Symbol(s) => result.push(s),
                Token::Keyword('.') => return result,
                _ => panic!("unexpected {:?} in list", tok),
            }
        }
        panic!("unexpected eof in list");
    }

    fn axiom(&mut self, label: &'a str) -> Option<Statement<'a>> {
        Some(Statement::Axiom(label, self.symbol_list()))
    }

    fn constant(&mut self) -> Option<Statement<'a>> {
        Some(Statement::Constant(self.symbol_list()))
    }

    fn distinct(&mut self) -> Option<Statement<'a>> {
        Some(Statement::Distinct(self.symbol_list()))
    }

    fn essential(&mut self, label: &'a str) -> Option<Statement<'a>> {
        Some(Statement::Essential(label, self.symbol_list()))
    }

    fn floating(&mut self, label: &'a str) -> Option<Statement<'a>> {
        if let Some(Token::Symbol(c)) = self.scanner.next_skip_comment() {
            if let Some(Token::Symbol(v)) = self.scanner.next_skip_comment() {
                if let Some(Token::Keyword('.')) = self.scanner.next_skip_comment() {
                    return Some(Statement::Floating(label, c, v));
                }
            }
        }
        panic!("syntax error in $f");
    }

    fn proof(&mut self, label: &'a str) -> Option<Statement<'a>> {
        let mut result = Vec::new();
        while let Some(tok) = self.scanner.next_skip_comment() {
            match tok {
                Token::Symbol(s) => result.push(s),
                Token::Keyword('=') => {
                    let proof = self.symbol_list();
                    return Some(Statement::Proof(label, result, proof));
                }
                _ => panic!("unexpected {:?} in $p", tok),
            }
        }
        panic!("unexpected eof in $p");
    }

    fn variable(&mut self) -> Option<Statement<'a>> {
        Some(Statement::Variable(self.symbol_list()))
    }
}

impl<'a> Iterator for Parser<'a> {
    type Item = Statement<'a>;

    // Using Option sucks for error handling (it should be result), but is
    // ok under the assumption that the input is valid (ie has been validated
    // by some other tool).
    fn next(&mut self) -> Option<Statement<'a>> {
        let mut label = None;
        while let Some(tok) = self.scanner.next_skip_comment() {
            match tok {
                Token::Keyword('a') => return self.axiom(label.take().unwrap()),
                Token::Keyword('c') => return self.constant(),
                Token::Keyword('d') => return self.distinct(),
                Token::Keyword('e') => return self.essential(label.take().unwrap()),
                Token::Keyword('f') => return self.floating(label.take().unwrap()),
                Token::Keyword('p') => return self.proof(label.take().unwrap()),
                Token::Keyword('v') => return self.variable(),
                Token::Keyword('{') => return Some(Statement::StartBlock),
                Token::Keyword('}') => return Some(Statement::EndBlock),
                Token::Symbol(s) => {
                    label = Some(s);
                }
                _ => panic!("unexpected token {:?}", tok),
            }
        }
        None
    }
}

pub struct Compressed<'a> {
    input: &'a [&'a str],
    ix: usize,
}

impl<'a> Compressed<'a> {
    pub fn new(input: &'a [&'a str]) -> Compressed<'a> {
        Compressed { input, ix: 0 }
    }
}

impl<'a> Iterator for Compressed<'a> {
    type Item = usize;

    /// proof steps starting at 1, and 0 as special value representing Z tag
    fn next(&mut self) -> Option<usize> {
        if self.input.is_empty() {
            None
        } else {
            let mut val = 0;
            loop {
                let c = self.input[0].as_bytes()[self.ix];
                self.ix += 1;
                if self.ix == self.input[0].len() {
                    self.input = &self.input[1..];
                    self.ix = 0;
                }
                if c >= b'A' && c < b'U' {
                    return Some(val * 20 + ((c - b'A') as usize) + 1);
                } else if c >= b'U' && c <= b'Y' {
                    val = val * 5 + ((c - b'U') as usize) + 1;
                } else if c == b'Z' {
                    return Some(0);
                } else {
                    panic!("unknown byte 0x{:02x} in compressed proof", c);
                }
            }
        }
    }
}
