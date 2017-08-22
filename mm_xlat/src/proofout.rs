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

//! Generation of Ghilbert proof files.

use std::fs::File;
use std::io::{BufWriter, Result, Write};
use std::path::Path;

pub type StepId = usize;

pub struct ProofOut {
    o: BufWriter<File>,
    step_id: StepId,
}

/// Convert an expression in set.mm to Ghilbert syntax.
// TODO: actually parse and reconstruct; this is a placeholder.
fn set_to_gh(set_expr: &[&str]) -> String {
    set_expr.join(" ")
}

impl ProofOut {
    pub fn new<P: AsRef<Path>>(filename: P) -> Result<ProofOut> {
        let f = File::create(filename)?;
        Ok(ProofOut {
            o: BufWriter::new(f),
            step_id: 0,
        })
    }

    /// Write text to the proof output file.
    pub fn write(&mut self, s: &str) {
        write!(self.o, "{}", s).unwrap();
    }

    pub fn start_thm(&mut self, label: &str,
            hyps: &[(&str, Vec<&str>)],
            concl: &[&str],
        ) {
        write!(self.o, "theorem {}", label).unwrap();
        for &(hyp_label, ref hyp) in hyps {
            write!(self.o, "\n  ({}: {})", hyp_label, set_to_gh(&hyp)).unwrap();
        }
        writeln!(self.o, ":\n  {} ::(", set_to_gh(concl)).unwrap();
        self.step_id = 0;
    }

    pub fn add_step(&mut self, label: &str, args: Vec<StepId>) -> StepId {
        let id = self.step_id;
        if id != 0 {
            writeln!(self.o, ";").unwrap();
        }
        write!(self.o, "  l{}: {}", id, label).unwrap();
        for id in &args {
            if id + 1 == self.step_id {
                write!(self.o, " _").unwrap();
            } else {
                write!(self.o, " l{}", id).unwrap();
            }
        }
        self.step_id += 1;
        id
    }

    pub fn end_thm(&mut self) {
        writeln!(self.o, "\n)").unwrap();
    }
}
