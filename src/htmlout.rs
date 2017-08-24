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

//! Generation of HTML output for proofs.

use std::collections::HashMap;
use std::io::{self, Write};

use lexer::Token;
use parser::{Parser, ParseNode};
use prooflistener::ProofListener;
use typeset::Typeset;

#[derive(Clone)]
enum SpanInfo {
    Theorem(Token),
    Step(Option<Token>, usize),
    HypName,
    Hyp(String),
    Result(String),
}

impl SpanInfo {
    fn emit_start<W: Write>(&self, writer: &mut W, parser: &Parser) -> io::Result<()> {
        match *self {
            SpanInfo::Theorem(tok) => {
                // Note: this doesn't get escaping right...
                write!(writer, "<span class=\"thm\" id=\"thm_{}\">",
                    parser.tok_str(tok))
            }
            SpanInfo::HypName => {
                write!(writer, "<span class=\"hypname\">")
            }
            SpanInfo::Hyp(ref s) => {
                write!(writer, "<span class=\"hyp\">\\({}\\)<!--", s)
            }
            SpanInfo::Step(opt_tok, _ix) => {
                if let Some(tok) = opt_tok {
                    write!(writer, "<span class=\"step\"><a href=\"#thm_{}\">",
                        parser.tok_str(tok))
                } else {
                    write!(writer, "<span class=\"step\">")
                }
            }
            SpanInfo::Result(ref s) => {
                write!(writer, "<span class=\"result\">\\({}\\)<!--", s)
            }
        }
    }

    fn emit_end<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        match *self {
            SpanInfo::Step(opt_tok, _) => {
                if opt_tok.is_some() {
                    write!(writer, "</a>")?;
                }
                write!(writer, "</span>")
            }
            SpanInfo::Hyp(_) | SpanInfo::Result(_) => write!(writer, "--></span>"),
            _ => write!(writer, "</span>"),
        }
    }
}

#[derive(Clone)]
struct Span {
    // We don't store start because it's the key of the map which holds the spans.
    end: usize,
    info: SpanInfo,
}

pub struct HtmlOut<'a> {
    text: &'a str,
    spans: HashMap<usize, Span>,
    typeset: Typeset,
}

impl<'a> HtmlOut<'a> {
    pub fn new(text: &str) -> HtmlOut {
        HtmlOut {
            text,
            spans: HashMap::new(),
            typeset: Typeset::new(),
        }
    }

    /// Write the formatted proof to the output.
    pub fn write<W: Write>(&mut self, writer: &mut W, parser: &Parser) -> io::Result<()> {
        write_prelude(writer)?;
        let mut close: Option<Span> = None;
        for (i, c) in self.text.char_indices() {
            let mut clear_close = false;
            if let Some(ref cur_span) = close {
                if i == cur_span.end {
                    cur_span.info.emit_end(writer)?;
                    clear_close = true;
                }
            }
            if clear_close { close = None; }
            if let Some(span) = self.spans.remove(&i) {
                // This is somewhat crude but should work.
                if let Some(cur_span) = close {
                    cur_span.info.emit_end(writer)?;
                }
                span.info.emit_start(writer, parser)?;
                close = Some(span);
            }
            write_escaped_char(writer, c)?;
        }
        write_footer(writer)
    }

    /// Add a span. Note that, in the current scheme, there can be only one
    /// span at any given start position.
    fn add_span(&mut self, node: &ParseNode, info: SpanInfo) {
        let span = Span {
            end: node.get_end(),
            info
        };
        self.spans.insert(node.get_start(), span);
    }
}

impl<'a> ProofListener for HtmlOut<'a> {
    fn start_proof(&mut self, node: &ParseNode) {
        let step = node.get_step().unwrap();
        self.add_span(node, SpanInfo::Theorem(step));
    }

    fn end_proof(&mut self) {
    }

    fn hyp(&mut self, hyp_name: &ParseNode, hyp: &ParseNode, parser: &Parser) {
        self.add_span(hyp_name, SpanInfo::HypName);
        let hyp_str = self.typeset.typeset(hyp, parser);
        self.add_span(hyp, SpanInfo::Hyp(hyp_str));
    }

    fn concl(&mut self, concl: &ParseNode, parser: &Parser) {
        let concl_str = self.typeset.typeset(concl, parser);
        self.add_span(concl, SpanInfo::Hyp(concl_str));
    }

    fn step(&mut self, node: &ParseNode, node_ix: usize) {
        self.add_span(node, SpanInfo::Step(node.get_step(), node_ix));
    }

    fn result(&mut self, node: &ParseNode, _node_ix: usize, parser: &Parser) {
        let result_str = self.typeset.typeset(node, parser);
        self.add_span(node, SpanInfo::Result(result_str));
    }
}

fn write_prelude<W: Write>(writer: &mut W) -> io::Result<()> {
    write!(writer, r#"<!DOCTYPE html>
<html>
<head>
<title>Ghilbert sample output</title>
<link rel="stylesheet" href="proof.css">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta charset="utf-8">
<script type="text/javascript" async
  src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.1/MathJax.js?config=TeX-MML-AM_CHTML">
</script>
<body>
<p class="proof">"#)
}

fn write_footer<W: Write>(writer: &mut W) -> io::Result<()> {
    write!(writer, r#"</p>
"#)
}

/// Write a character with HTML escaping.
fn write_escaped_char<W: Write>(writer: &mut W, c: char) -> io::Result<()> {
    let s = match c {
        '<' => "&lt;",
        '>' => "&gt;",
        '&' => "&amp;",
        _ => return write!(writer, "{}", c),
    };
    write!(writer, "{}", s)
}
