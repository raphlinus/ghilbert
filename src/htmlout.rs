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
use std::fs::{self, File};
use std::io::{self, ErrorKind, Write};
use std::path::Path;

use lexer::Token;
use parser::{Info, Parser, ParseNode};
use prooflistener::{Inspector, NodeIx, ProofListener};
use typeset::Typeset;

use serde_json::Value;
use serde_json::map::Map;

// offset within text
type Offset = usize;

type StepIx = usize;

pub struct HtmlOut<'a> {
    out_dir: String,
    text: &'a str,
    typeset: Typeset,

    last_comment: Option<&'a str>,
    thm_info: HashMap<Token, ThmInfo>,
    thms: Vec<(Option<&'a str>, ParseNode)>,

    step_ix: StepIx,
    steps: HashMap<Offset, StepInfo>,
    // name of current thm
    cur_tok: Option<Token>,
    last_line: StepIx,
}

struct ThmInfo {
    // TODO: work out HTML formatting / escaping
    full_comment: String,
    short_text: String,
    defs: HashMap<Token, StepIx>,

    /// List of arguments for each step
    // Note: could switch to denser representation
    refs: HashMap<StepIx, Vec<StepIx>>,

    step_to_node: HashMap<StepIx, NodeIx>,

    step_typeset: HashMap<StepIx, String>,

    underscores: HashMap<Offset, StepIx>,
}

struct StepInfo {
    step_ix: usize,
    opt_tok: Option<Token>,
}

/// Context for rendering a proof into HTML
struct Ctx<'a, W: Write> {
    w: W,
    json: Map<String, Value>,
    parser: &'a Parser<'a>,
    thm_info: &'a ThmInfo,
}

// Convenience so we can write to ctx rather than &mut ctx.w
impl<'a, W: Write> Write for Ctx<'a, W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.w.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.w.flush()
    }

    // maybe more methods so we don't get the default?
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
            thm_info: HashMap::new(),
            thms: Vec::new(),

            step_ix: 0,
            steps: HashMap::new(),
            cur_tok: None,
            last_line: 0,
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
        let thm_name_tok = node.children[0].get_step().expect("thm name wasn't step");
        let thm_name = parser.tok_str(thm_name_tok);
        let page_fn = Path::new(&self.out_dir).join(format!("{}.html", thm_name));
        let mut f = File::create(page_fn)?;
        let thm_info = self.thm_info.get(&thm_name_tok).expect(
            &format!("no info for thm {}", parser.tok_str(thm_name_tok)));
        let mut ctx = Ctx {
            w: f,
            json: Map::new(),
            parser,
            thm_info,
        };
        write!(&mut ctx, r#"<!DOCTYPE html>
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
<div id="outer">
<div class="wrapper" id="left">
<div class="thmname"><span class="xt">Theorem</span> {}</div>
"#, thm_name, thm_name)?;
        self.write_comment(&mut ctx, comment.unwrap_or("(comment missing)"))?;
        self.write_hyps(&mut ctx, &node.children[1], &node.children[2])?;
        // TODO: free variable constraints
        self.write_concl(&mut ctx, &node.children[4], parser)?;
        self.write_proof(&mut ctx, &node.children[5])?;
        write!(&mut ctx.w, r#"</div>
<div id="right" class="hidden">
This is the content in the right pane.
</div>
</div>
<script async src="../thm.js">
</script>
"#)?;
        let json_fn = Path::new(&self.out_dir).join(format!("{}.json", thm_name));
        let mut json_f = File::create(json_fn)?;
        writeln!(json_f, "{}", Value::Object(ctx.json).to_string())
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

    fn write_hyps<W: Write>(&self, ctx: &mut Ctx<W>, hyp_names: &ParseNode, hyps: &ParseNode)
        -> io::Result<()>
    {
        if hyp_names.children.len() == 1 {
            writeln!(ctx, "<div class=\"ex\">Hypothesis</div>")?;
        } else if hyp_names.children.len() > 1 {
            writeln!(ctx, "<div class=\"ex\">Hypotheses</div>")?;
        }
        for (hyp_name, hyp) in hyp_names.children.iter().zip(hyps.children.iter()) {
            let hyp_name_tok = hyp_name.get_step().unwrap();
            writeln!(ctx, "<div class=\"l\"><span id=\"s{}\">{}</span></div>",
                self.steps.get(&hyp_name.get_start()).expect("steps get").step_ix,
                ctx.parser.tok_str(hyp_name_tok))?;
            let hyp_str = self.typeset.typeset(hyp, &ctx.parser);
            writeln!(ctx, "<div class=\"f\">\\( {} \\)</div>", hyp_str)?;
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

    fn write_proof<W: Write>(&self, ctx: &mut Ctx<W>, proof: &ParseNode) -> io::Result<()>
    {
        writeln!(ctx, "<div class=\"ex\">Proof</div>")?;
        for line in &proof.children {
            if let Some(label) = line.children[0].get_step() {
                writeln!(&mut ctx.w, "<div class=\"pl\">{}</div>", ctx.parser.tok_str(label))?;
            }
            write!(&mut ctx.w, "<div class=\"s\">")?;
            self.write_linkable_step(ctx, &line.children[1])?;
            for arg in &line.children[2].children {
                write!(ctx, " ")?;
                match arg.info {
                    Info::List => write!(&mut ctx.w, "[nested proof NYI]")?,
                    _ => self.write_linkable_step(ctx, arg)?,
                }
            }
            writeln!(ctx, "</div>")?;
            let res_line = &line.children[3];
            if res_line.info != Info::Dummy {
                let result_str = self.typeset.typeset(res_line, &ctx.parser);
                writeln!(ctx, "<div class=\"r\">\\( {} \\)</div>", result_str)?;
            }
        }
        Ok(())
    }

    fn write_linkable_step<W: Write>(&self, ctx: &mut Ctx<W>, node: &ParseNode) -> io::Result<()>
    {
        if let Some(step) = self.steps.get(&node.get_start()) {
            let step_id = format!("s{}", step.step_ix);
            write!(ctx, "<span id=\"{}\">", step_id)?;
            let mut step_info = None;
            if let Some(tok) = step.opt_tok {
                if let Some(step_ix) = ctx.thm_info.defs.get(&tok) {
                    step_info = Some(json!({
                        "def": step_ix,
                    }));
                } else if let Some(info) = self.thm_info.get(&tok) {
                    step_info = Some(json!({
                        "link": ctx.parser.tok_str(tok),
                        "comment": info.full_comment,
                        "hover": info.short_text
                    }));
                }
            } else {
                if let Some(step_ix) = ctx.thm_info.underscores.get(&node.get_start()) {
                    step_info = Some(json!({"def": step_ix}));
                }
            }
            if let Some(mut step_info) = step_info {
                if let Some(refs) = ctx.thm_info.refs.get(&step.step_ix) {
                    step_info["refs"] = json!(refs);
                }
                if let Some(ts) = ctx.thm_info.step_typeset.get(&step.step_ix) {
                    step_info["typeset"] = json!(ts);
                }
                ctx.json.insert(step_id, step_info);
            }
        } else {
            write!(ctx, "<span><!-- step id not found -->")?;
        }
        match node.info {
            Info::Dummy => write!(ctx, "_")?,
            Info::Step(tok) => write!(ctx, "{}", ctx.parser.tok_str(tok))?,
            _ => panic!("not valid linkable step {:?}", node.info),
        }
        write!(ctx, "</span>")
    }

    fn cur_info(&self) -> &ThmInfo {
        self.thm_info.get(&self.cur_tok.unwrap()).unwrap()
    }

    fn cur_info_mut(&mut self) -> &mut ThmInfo {
        self.thm_info.get_mut(&self.cur_tok.unwrap()).unwrap()
    }
}

impl<'a> ProofListener for HtmlOut<'a> {
    fn comment(&mut self, start: usize, end: usize) {
        println!("comment {} {}", start, end);
        self.last_comment = Some(&self.text[start..end]);
    }

    fn start_proof(&mut self, node: &ParseNode) {
        if let Some(comment) = self.last_comment {
            if let Some(tok) = node.children[0].get_step() {
                self.cur_tok = Some(tok);
                self.thm_info.insert(tok, ThmInfo {
                    full_comment: comment.trim().to_string(),
                    short_text: extract_short_string(&comment),
                    defs: HashMap::new(),
                    refs: HashMap::new(),
                    step_to_node: HashMap::new(),
                    step_typeset: HashMap::new(),
                    underscores: HashMap::new(),
                });
            }
        }
        self.thms.push((self.last_comment.take(), node.clone()));
        self.step_ix = 0;
    }

    fn end_proof(&mut self, inspector: &mut Inspector, parser: &Parser) {
        let mut step_typeset = HashMap::new();
        {
            let info = self.cur_info();
            for (&step, &node_ix) in &info.step_to_node {
                let node = inspector.describe(node_ix);
                let ts = self.typeset.typeset(&node, parser);
                step_typeset.insert(step, ts);
            }
        }
        self.cur_info_mut().step_typeset = step_typeset;
        self.cur_tok = None;
    }

    fn hyp(&mut self, hyp_name: &ParseNode, hyp: &ParseNode, _parser: &Parser) {
        let step_ix = self.step_ix;
        self.steps.insert(hyp_name.get_start(), StepInfo {
            step_ix,
            opt_tok: hyp_name.get_step(),
        });
        if let Some(tok) = hyp_name.get_step() {
            self.cur_info_mut().defs.insert(tok, step_ix);
        }
        self.step_ix += 1;
    }

    fn concl(&mut self, _concl: &ParseNode, _parser: &Parser) {
    }

    fn start_line(&mut self, line: &ParseNode) {
    }

    fn end_line(&mut self, line: &ParseNode) {
        let step_ix = self.steps.get(&line.children[1].get_start()).expect("get_step").step_ix;
        if let Some(tok) = line.children[0].get_step() {
            self.cur_info_mut().defs.insert(tok, step_ix);
        }
        let refs = line.children[2].children.iter().map(|node|
            self.steps.get(&node.get_start()).expect("ref get_step").step_ix
        ).collect();
        self.cur_info_mut().refs.insert(step_ix, refs);
        // TODO: this logic is probably wrong wrt nested proofs
        self.last_line = step_ix;
    }

    fn step(&mut self, node: &ParseNode, node_ix: usize) {
        if node.info == Info::Dummy {
            let last_line = self.last_line;
            self.cur_info_mut().underscores.insert(node.get_start(), last_line);
        }
        let step_ix = self.step_ix;
        self.cur_info_mut().step_to_node.insert(step_ix, node_ix);
        self.steps.insert(node.get_start(), StepInfo {
            step_ix: step_ix,
            opt_tok: node.get_step(),
        });
        self.step_ix += 1;
    }

    fn result(&mut self, _node: &ParseNode, _node_ix: usize, _parser: &Parser) {
    }
}

fn extract_short_string(comment: &str) -> String {
    let comment = comment.trim();
    // TODO: Maybe get more sophisticated about finding the boundary.
    if let Some(pos) = comment.find('.') {
        &comment[..pos]
    } else {
        comment
    }.to_string()
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
