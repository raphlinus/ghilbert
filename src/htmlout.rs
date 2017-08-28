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

use std::collections::HashSet;
use std::fs::{self, File};
use std::io::{self, ErrorKind, Write};
use std::path::Path;

use lexer::Token;
use parser::{Info,Parser, ParseNode};
use prooflistener::ProofListener;
use typeset::Typeset;

pub struct HtmlOut<'a> {
    out_dir: String,
    text: &'a str,
    typeset: Typeset,

    last_comment: Option<&'a str>,
    all_thm_names: HashSet<Token>,
    thms: Vec<(Option<&'a str>, ParseNode)>,
}

impl<'a> HtmlOut<'a> {
    pub fn new(out_dir: &str, text: &'a str) -> HtmlOut<'a> {
        if let Err(e) = fs::create_dir(out_dir) {
            if e.kind() != ErrorKind::AlreadyExists {
                panic!("error {:?} creating {}", e, out_dir);
            }
        }
        HtmlOut {
            out_dir: out_dir.to_string(),
            text,
            typeset: Typeset::new(),

            last_comment: None,
            all_thm_names: HashSet::new(),
            thms: Vec::new(),
        }
    }

    /// Write the formatted proof to the output.
    pub fn write<W: Write>(&mut self, writer: &mut W, parser: &Parser) -> io::Result<()> {
        for &(comment, ref thm) in &self.thms {
            self.write_thm(comment, thm, parser)?;
        }
        Ok(())
    }

    fn write_thm(&self, comment: Option<&'a str>, node: &ParseNode, parser: &Parser)
        -> io::Result<()>
    {
        let thm_name = parser.tok_str(node.children[0].get_step().unwrap());
        let page_fn = Path::new(&self.out_dir).join(format!("{}.html", thm_name));
        let mut f = File::create(page_fn)?;
        write!(f, r#"<!DOCTYPE html>
<html>
<head>
<title>Theorem {}</title>
<link href="https://fonts.googleapis.com/css?family=Lato:300,400,400i,700" rel="stylesheet">
<link rel="stylesheet" href="../thm.css">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta charset="utf-8"/>
<script type="text/javascript" async
  src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.1/MathJax.js?config=TeX-AMS_CHTML">
</script>
<body>
<div class="wrapper">
<div class="thmname"><span class="xt">Theorem</span> {}</div>
"#, thm_name, thm_name)?;
        self.write_comment(&mut f, comment.unwrap_or("(comment missing)"))?;
        self.write_hyps(&mut f, &node.children[1], &node.children[2], parser)?;
        // TODO: free variable constraints
        self.write_concl(&mut f, &node.children[4], parser)?;
        self.write_proof(&mut f, &node.children[5], parser)?;
        writeln!(f, "</div>")
    }

    fn write_comment<W: Write>(&self, w: &mut W, comment: &str) -> io::Result<()> {
        let comment = comment.trim();
        write!(w, "<div class=\"text\">")?;
        for c in comment.chars() {
            // TODO: markdown processing
            write_escaped_char(w, c)?;
        }
        writeln!(w, "</div>")
    }

    fn write_hyps<W: Write>(&self, w: &mut W, hyp_names: &ParseNode, hyps: &ParseNode,
        parser: &Parser) -> io::Result<()>
    {
        if hyp_names.children.len() == 1 {
            writeln!(w, "<div class=\"ex\">Hypothesis</div>")?;
        } else if hyp_names.children.len() > 1 {
            writeln!(w, "<div class=\"ex\">Hypotheses</div>")?;
        }
        for (hyp_name, hyp) in hyp_names.children.iter().zip(hyps.children.iter()) {
            writeln!(w, "<div class=\"l\">{}</div>",
                parser.tok_str(hyp_name.get_step().unwrap()))?;
            let hyp_str = self.typeset.typeset(hyp, parser);
            writeln!(w, "<div class=\"f\">\\( {} \\)</div>", hyp_str)?;
        }
        Ok(())
    }

    fn write_concl<W: Write>(&self, w: &mut W, concl: &ParseNode, parser: &Parser)
        -> io::Result<()>
    {
        writeln!(w, "<div class=\"ex\">Conclusion</div>")?;
        let concl_str = self.typeset.typeset(concl, parser);
        writeln!(w, "<div class=\"concl\">\\( {} \\)</div>", concl_str)
    }

    fn write_proof<W: Write>(&self, w: &mut W, proof: &ParseNode, parser: &Parser)
        -> io::Result<()>
    {
        writeln!(w, "<div class=\"ex\">Proof</div>")?;
        for line in &proof.children {
            if let Some(label) = line.children[0].get_step() {
                writeln!(w, "<div class=\"pl\">{}</div>", parser.tok_str(label))?;
            }
            write!(w, "<div class=\"s\">")?;
            self.write_linkable_step(w, &line.children[1], parser)?;
            for arg in &line.children[2].children {
                write!(w, " ")?;
                match arg.info {
                    Info::List => write!(w, "[nested proof NYI]")?,
                    _ => self.write_linkable_step(w, arg, parser)?,
                }
            }
            writeln!(w, "</div>")?;
            let res_line = &line.children[3];
            if res_line.info != Info::Dummy {
                let result_str = self.typeset.typeset(res_line, parser);
                writeln!(w, "<div class=\"r\">\\( {} \\)</div>", result_str)?;
            }
        }
        Ok(())
    }

    fn write_linkable_step<W: Write>(&self, w: &mut W, step: &ParseNode, parser: &Parser)
        -> io::Result<()>
    {
        match step.info {
            Info::Dummy => write!(w, "_"),
            Info::Step(tok) => {
                let s = parser.tok_str(tok);
                if self.all_thm_names.contains(&tok) {
                    write!(w, "<a href=\"{}.html\">{}</a>", s, s)
                } else {
                    write!(w, "{}", s)
                }
            }
            _ => panic!("not valid linkable step {:?}", step.info),
        }
    }
}

impl<'a> ProofListener for HtmlOut<'a> {
    fn comment(&mut self, start: usize, end: usize) {
        println!("comment {} {}", start, end);
        self.last_comment = Some(&self.text[start..end]);
    }

    fn start_proof(&mut self, node: &ParseNode) {
        self.thms.push((self.last_comment.take(), node.clone()));
        if let Some(tok) = node.children[0].get_step() {
            self.all_thm_names.insert(tok);
        }
    }

    fn end_proof(&mut self) {
    }

    fn hyp(&mut self, _hyp_name: &ParseNode, _hyp: &ParseNode, _parser: &Parser) {
    }

    fn concl(&mut self, _concl: &ParseNode, _parser: &Parser) {
    }

    fn start_line(&mut self, _node: &ParseNode) {
    }

    fn step(&mut self, _node: &ParseNode, _node_ix: usize) {
    }

    fn result(&mut self, _node: &ParseNode, _node_ix: usize, _parser: &Parser) {
    }
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
