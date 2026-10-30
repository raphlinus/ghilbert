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

//! Typesetting into TeX, starting from parse tree.

// Currently the typesetting rules are basically hardcoded, but we want to
// move as much as possible into syntax definitions.

use parser::{Info, Notation, Parser, ParseNode};

pub struct Typeset;

impl Typeset {
    pub fn new() -> Typeset {
        Typeset
    }

    /// Typeset the parse node to TeX format
    pub fn typeset(&self, node: &ParseNode, parser: &Parser) -> String {
        let mut buf = String::new();
        self.rec(node, parser, &mut buf, 0);
        buf
    }

    fn rec(&self, node: &ParseNode, parser: &Parser, buf: &mut String, prec: u32) {
        //println!("rec {:?}", node);
        if node.info == Info::Lambda {
            self.lambda(node, parser, buf, prec);
        } else if let Info::Atom(tok) | Info::Var(tok) = node.info {
            if parser.is_coercion(tok) && node.children.len() == 1 {
                return self.rec(&node.children[0], parser, buf, prec);
            }
            if let Some(notation) = parser.notation(tok) {
                if notation.arg_prec.len() == node.children.len() {
                    return self.notation(notation, node, parser, buf, prec);
                }
            }
            let tok = parser.tok_str(tok);
            match tok {
                "ph" => buf.push_str("\\varphi"),
                "ps" => buf.push_str("\\psi"),
                "ch" => buf.push_str("\\chi"),
                "th" => buf.push_str("\\theta"),
                "ta" => buf.push_str("\\tau"),
                "et" => buf.push_str("\\eta"),
                "ze" => buf.push_str("\\zeta"),
                "si" => buf.push_str("\\sigma"),
                "rh" => buf.push_str("\\rho"),
                "mu" => buf.push_str("\\mu"),
                "la" => buf.push_str("\\lambda"),
                "ka" => buf.push_str("\\kappa"),
                "|-" => self.unary("\\vdash", 5, node, parser, buf, prec),
                "<->" => self.infixl("\\leftrightarrow", 20, node, parser, buf, prec),
                "->" => self.infixr("\\rightarrow", 25, node, parser, buf, prec),
                "\\/" => self.infixl("\\vee", 30, node, parser, buf, prec),
                "/\\" => self.infixl("\\wedge", 35, node, parser, buf, prec),
                "-." => self.unary("\\neg", 40, node, parser, buf, prec),
                "=" => self.infixl("=", 50, node, parser, buf, prec),
                "e." => self.infixl("\\in", 50, node, parser, buf, prec),
                "\\" => self.lambda(node, parser, buf, prec),
                "A." => self.binder("\\forall ", "", &node.children[0], parser, buf, prec),
                "E." => self.binder("\\exists ", "", &node.children[0], parser, buf, prec),
                "wnf" => self.binder("\\Finv ", "", &node.children[0], parser, buf, prec),
                "wmo" => self.binder("\\exists^{*} ", "", &node.children[0], parser, buf, prec),
                "weu" => self.binder("\\exists! ", "", &node.children[0], parser, buf, prec),
                "wsb" => {
                    let mut pre = String::from("[");
                    self.rec(&node.children[0], parser, &mut pre, 0);
                    pre.push_str(" / ");
                    self.binder(&pre, "]", &node.children[1], parser, buf, prec);
                }
                _ => {
                    if node.children.is_empty() {
                        buf.push_str(tok);
                    } else {
                        buf.push_str("(\\mathrm{");
                        buf.push_str(tok);
                        buf.push('}');
                        for child in &node.children {
                            buf.push_str("\\ ");
                            self.rec(child, parser, buf, 9999);
                        }
                        buf.push_str(")");
                    }
                }
            }
        } else {
            println!("unexpected {:?} in typeset", node);
        }
    }

    fn notation(&self, notation: &Notation, node: &ParseNode, parser: &Parser,
        buf: &mut String, prec: u32)
    {
        if notation.prec < prec {
            buf.push('(');
        }
        let mut rest = &notation.template[..];
        while let Some(ix) = find_arg(rest) {
            buf.push_str(&rest[..ix]);
            rest = &rest[ix + 1..];
            let (arg, after) = split_num(rest);
            rest = after;
            let mut child = &node.children[arg - 1];
            if rest.starts_with('@') {
                let (depth, after) = split_num(&rest[1..]);
                rest = after;
                for _ in 0..depth {
                    child = lambda_parts(child, parser).expect("lambda in notation").1;
                }
                let var = lambda_parts(child, parser).expect("lambda in notation").0;
                self.rec(var, parser, buf, 0);
            } else {
                while let Some((_, body)) = lambda_parts(child, parser) {
                    child = body;
                }
                self.rec(child, parser, buf, notation.arg_prec[arg - 1]);
            }
        }
        buf.push_str(rest);
        if notation.prec < prec {
            buf.push(')');
        }
    }

    /// Typesets a term that binds the variable of `lambda`, with the variable
    /// between `pre` and `post` and the body following.
    fn binder(&self, pre: &str, post: &str, lambda: &ParseNode, parser: &Parser,
        buf: &mut String, prec: u32)
    {
        let myprec = 45;
        if let Some((var, body)) = lambda_parts(lambda, parser) {
            if myprec < prec {
                buf.push('(');
            }
            buf.push_str(pre);
            self.rec(var, parser, buf, 0);
            buf.push_str(post);
            buf.push_str(" \\, ");
            // A negation needs no parentheses, as nothing can come between it
            // and the binder.
            let body_prec = match body.info {
                Info::Atom(tok) if parser.tok_str(tok) == "-." => 40,
                _ => myprec,
            };
            self.rec(body, parser, buf, body_prec);
            if myprec < prec {
                buf.push(')');
            }
        } else {
            println!("unexpected {:?} in typeset", lambda);
        }
    }

    fn lambda(&self, node: &ParseNode, parser: &Parser, buf: &mut String, prec: u32) {
        if let Some((var, body)) = lambda_parts(node, parser) {
            if prec > 0 {
                buf.push('(');
            }
            buf.push_str("\\lambda ");
            self.rec(var, parser, buf, 0);
            buf.push_str(". \\, ");
            self.rec(body, parser, buf, 0);
            if prec > 0 {
                buf.push(')');
            }
        } else {
            println!("unexpected {:?} in typeset", node);
        }
    }

    fn unary(&self, sym: &str, myprec: u32, node: &ParseNode, parser: &Parser,
        buf: &mut String, prec: u32)
    {
        if myprec < prec {
            buf.push('(');
        }
        buf.push_str(sym);
        buf.push(' ');
        self.rec(&node.children[0], parser, buf, myprec);
        if myprec < prec {
            buf.push(')');
        }
    }

    fn infixl(&self, sym: &str, myprec: u32, node: &ParseNode, parser: &Parser,
        buf: &mut String, prec: u32)
    {
        if myprec < prec {
            buf.push('(');
        }
        self.rec(&node.children[0], parser, buf, myprec);
        buf.push(' ');
        buf.push_str(sym);
        buf.push(' ');
        self.rec(&node.children[1], parser, buf, myprec + 1);
        if myprec < prec {
            buf.push(')');
        }
    }

    fn infixr(&self, sym: &str, myprec: u32, node: &ParseNode, parser: &Parser,
        buf: &mut String, prec: u32)
    {
        if myprec < prec {
            buf.push('(');
        }
        self.rec(&node.children[0], parser, buf, myprec + 1);
        buf.push(' ');
        buf.push_str(sym);
        buf.push(' ');
        self.rec(&node.children[1], parser, buf, myprec);
        if myprec < prec {
            buf.push(')');
        }
    }
}

/// Finds the next argument in a template, which is a `#` before a digit that
/// isn't escaped.
fn find_arg(s: &str) -> Option<usize> {
    let b = s.as_bytes();
    (0..b.len()).find(|&i| b[i] == b'#' && (i == 0 || b[i - 1] != b'\\')
        && b.get(i + 1).map_or(false, u8::is_ascii_digit))
}

/// Splits the leading number off a string.
fn split_num(s: &str) -> (usize, &str) {
    let len = s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
    (s[..len].parse().unwrap_or(0), &s[len..])
}

/// Splits a lambda into its bound variable and body. Lambdas from the parser are
/// `Info::Lambda` nodes, while the ones reconstructed from proof steps are
/// applications of a backslash atom.
fn lambda_parts<'a>(node: &'a ParseNode, parser: &Parser) -> Option<(&'a ParseNode, &'a ParseNode)> {
    let is_lambda = match node.info {
        Info::Lambda => true,
        Info::Atom(tok) => parser.tok_str(tok) == "\\",
        _ => false,
    };
    if is_lambda && node.children.len() == 2 {
        Some((&node.children[0], &node.children[1]))
    } else {
        None
    }
}
