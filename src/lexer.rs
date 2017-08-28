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

//! A simple lexer for the the new Ghilbert format.

use std::collections::BTreeMap;

pub type Token = usize;

struct Node {
    terminal: Option<Token>,
    succ: BTreeMap<char, Node>,
}

impl Node {
    fn new() -> Node {
        Node {
            terminal: None,
            succ: BTreeMap::new(),
        }
    }

    fn traverse<I: Iterator<Item=char>>(&mut self, iter: I) -> &mut Node {
        let mut node = self;
        for c in iter {
            node = {node}.succ.entry(c).or_insert_with(|| Node::new());
        }
        node
    }
}

pub struct Lexer<'a> {
    text: &'a str,
    ix: usize,
    root: Node,
    tokens: Vec<String>,
    lookahead: Option<(Token, usize)>,
}

fn find_end_of_comment(s: &str) -> usize {
    let mut state = 0;
    let mut nest = 1;
    for (i, c) in s.char_indices() {
        match (state, c) {
            (0, '/') => state = 1,
            (0, '*') => state = 2,
            (1, '*') => { nest += 1; state = 0; }
            (1, _) => state = 0,
            (2, '/') => {
                nest -= 1;
                if nest == 0 {
                    return i + 1;
                }
                state = 0;
            }
            (2, _) => state = 0,
            _ => (),
        }
    }
    s.len()
}

impl<'a> Lexer<'a> {
    /// Creates a new lexer for a given input string.
    pub fn new(text: &str) -> Lexer {
        Lexer {
            text: text,
            ix: 0,
            root: Node::new(),
            tokens: Vec::new(),
            lookahead: None,
        }
    }

    /// Get a comment if it's present. Return value are start and end
    /// indices.
    pub fn next_comment(&mut self) -> Option<(usize, usize)> {
        for (i, c) in self.text[self.ix..].char_indices() {
            if c == '/' && self.ix + i + 1 < self.text.len() &&
                self.text.as_bytes()[self.ix + i + 1] == b'*'
            {
                let comment_start = self.ix + i + 2;
                let len = find_end_of_comment(&self.text[comment_start..]);
                self.ix = comment_start + len;
                return Some((comment_start, comment_start + len - 2));
            }
            if !c.is_whitespace() {
                self.ix += i;
                return None;
            }
        }
        self.ix = self.text.len();
        None
    }

    /// Skips whitespace and comments.
    // TODO: could avoid duplication by writing in terms of next_comment
    pub fn skip_whitespace(&mut self) {
        'outer: loop {
            for (i, c) in self.text[self.ix..].char_indices() {
                if c == '/' && self.ix + i + 1 < self.text.len() &&
                    self.text.as_bytes()[self.ix + i + 1] == b'*'
                {
                    self.ix += i + 2;
                    self.ix += find_end_of_comment(&self.text[self.ix..]);
                    continue 'outer;
                }
                if !c.is_whitespace() {
                    self.ix += i;
                    return;
                }
            }
            self.ix = self.text.len();
            return;
        }
    }

    /// Interns a token, in other words installs it in the table if not already
    /// present.
    pub fn intern(&mut self, s: &str) -> Token {
        let mut node = self.root.traverse(s.chars());
        if let Some(token) = node.terminal {
            token
        } else {
            let token = self.tokens.len();
            self.tokens.push(s.to_string());
            node.terminal = Some(token);
            token
        }
    }

    fn next_from_len(&mut self, len: usize) -> Option<Token> {
        if len == 0 {
            None
        } else {
            let ix = self.ix;
            self.ix += len;
            Some(self.intern(&self.text[ix..ix + len]))
        }
    }

    /// Scans a token using "long" policy; token is everything up to space.
    pub fn next_long(&mut self) -> Option<Token> {
        if let Some((tok, ix)) = self.lookahead.take() {
            self.ix = ix;
            return Some(tok);
        }
        self.skip_whitespace();
        let mut len = 0;
        for c in self.text[self.ix..].chars() {
            if c.is_whitespace() {
                break;
            }
            len += c.len_utf8();
        }
        self.next_from_len(len)
    }

    /// Scans a token using "medium" policy; delimeters include space, semicolon, colon, parens.
    pub fn next_medium(&mut self) -> Option<Token> {
        if let Some((tok, ix)) = self.lookahead.take() {
            self.ix = ix;
            return Some(tok);
        }
        self.skip_whitespace();
        let mut len = 0;
        for c in self.text[self.ix..].chars() {
            if len > 0 && (c.is_whitespace() || c == ';' || c == ':' || c == '(' || c == ')') {
                break;
            }
            len += c.len_utf8();
        }
        self.next_from_len(len)
    }

    /// Scans a token using normal policy; longest matching token, or at least
    /// one codepoint.
    pub fn next(&mut self) -> Option<Token> {
        if let Some((tok, ix)) = self.lookahead.take() {
            self.ix = ix;
            return Some(tok);
        }
        self.skip_whitespace();
        let mut best = None;
        let mut one_cp_len = None;
        {
            let mut len = 0;
            let mut node = &mut self.root;
            for c in self.text[self.ix..].chars() {
                if c.is_whitespace() {
                    break;
                }
                if len == 0 {
                    one_cp_len = Some(c.len_utf8());
                }
                if let Some(next) = {node}.succ.get_mut(&c) {
                    node = next;
                } else {
                    break;
                }
                len += c.len_utf8();
                if let Some(token) = node.terminal {
                    best = Some((token, len));
                }
            }
        }
        if let Some((token, len)) = best {
            self.ix += len;
            Some(token)
        } else {
            one_cp_len.and_then(|len| self.next_from_len(len))
        }
    }

    /// Scans a nonnegative decimal number (does not add token to trie).
    ///
    /// Returns `None` on u32 overflow; return type should arguably be changed
    /// to provide for more precise error messages.
    pub fn next_u32(&mut self) -> Option<u32> {
        self.skip_whitespace();
        let mut val = 0u32;
        let mut len = 0;
        for &c in self.text[self.ix..].as_bytes() {
            if c >= b'0' && c <= b'9' {
                if let Some(v) = val.checked_mul(10).and_then(|x|
                    x.checked_add((c - b'0') as u32))
                {
                    val = v;
                } else {
                    return None;
                }
                len += 1;
            } else {
                break;
            }
        }
        if len > 0 {
            self.ix += len;
            Some(val)
        } else {
            None
        }
    }

    /// Returns the string for the given token.
    pub fn tok_str(&self, tok: Token) -> &str {
        &self.tokens[tok]
    }

    /// Peeks at the next token without advancing the cursor.
    pub fn peek(&mut self) -> Option<Token> {
        if let Some((tok, _)) = self.lookahead {
            return Some(tok);
        }
        let save_ix = self.ix;
        self.next().map(|tok| {
            self.lookahead = Some((tok, self.ix));
            self.ix = save_ix;
            tok
        })
    }

    /// Consumes the expected token, otherwise leaves the lexer state unchanged.
    pub fn expect(&mut self, expected: Token) -> bool {
        if let Some(tok) = self.peek() {
            if tok == expected {
                let _ = self.next();
                return true;
            }
        }
        false
    }

    /// Returns the current byte offset.
    pub fn pos(&self) -> usize {
        self.ix
    }
}
