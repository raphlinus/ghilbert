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

//! An interface (and maybe utility methods) for creating output based on proofs.

use parser::{Parser, ParseNode};

/// Index of a step. The hypotheses start at 0. The first step in the proof is
/// the number of hypotheses. They will be assigned in evaluation order.
pub type StepIx = usize;

pub trait ProofListener {
    /// start and end are indices of interior of comment (don't count comment
    /// delimeters but do count spaces)
    fn comment(&mut self, start: usize, end: usize);

    fn start_proof(&mut self, label: &ParseNode);

    fn end_proof(&mut self, inspector: &mut Inspector, parser: &Parser);

    fn hyp(&mut self, hyp_name: &ParseNode, hyp: &ParseNode, parser: &Parser);

    fn concl(&mut self, concl: &ParseNode, parser: &Parser);

    fn start_line(&mut self, node: &ParseNode);

    fn step(&mut self, node: &ParseNode, step_ix: StepIx);

    fn result(&mut self, node: &ParseNode, step_ix: StepIx, _parser: &Parser);

    fn end_line(&mut self, node: &ParseNode);
}

pub trait Inspector {
    /// Provide an expression containing the result of the step.
    fn describe(&mut self, node_ix: StepIx) -> ParseNode;
}

pub struct DebugListener;

impl ProofListener for DebugListener {
    fn comment(&mut self, start: usize, end: usize) {
        println!("comment {} {}", start, end);
    }

    fn start_proof(&mut self, node: &ParseNode) {
        println!("start proof {:?}:", node);
    }

    fn end_proof(&mut self, _inspector: &mut Inspector, _parser: &Parser) {
        println!("end proof");
    }

    fn hyp(&mut self, hyp_name: &ParseNode, hyp: &ParseNode, _parser: &Parser) {
        println!("  hyp {:?}: {:?}", hyp_name, hyp);
    }

    fn concl(&mut self, concl: &ParseNode, _parser: &Parser) {
        println!("  concl {:?}", concl);
    }

    fn start_line(&mut self, node: &ParseNode) {
        println!("  start line {:?}", node);
    }

    fn step(&mut self, node: &ParseNode, step_ix: StepIx) {
        println!("  step {:?} ix={}", node, step_ix);
    }

    fn result(&mut self, node: &ParseNode, step_ix: StepIx, _parser: &Parser) {
        println!("  result {:?} ix={}", node, step_ix);
    }

    fn end_line(&mut self, node: &ParseNode) {
        println!("  end line {:?}", node);
    }
}
