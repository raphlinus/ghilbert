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

//! A translator from Metamath into Ghilbert format.

use std::env;
use std::fs::File;
use std::io::{self, Read};
use std::process::exit;

mod parser;
use parser::{Scanner, Parser};

mod proofout;
use proofout::ProofOut;

mod script;
use script::Script;

mod session;
use session::Session;

fn run_file(scr_fn: &str, filename: &str, out_fn: &str) -> io::Result<()> {
    println!("running {}", filename);
    let mut script = Script::new(scr_fn)?;
    let mut file = File::open(filename)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    let s = Scanner::new(&contents);
    let mut p = Parser::new(s);
    let out = ProofOut::new(out_fn)?;
    let mut sess = Session::new(out);
    sess.run_script(&mut script, &mut p);
    Ok(())
}

fn main() {
    let mut args = Vec::new();
    for arg in env::args().skip(1) {
        // could process flags here
        args.push(arg);
    }
    if args.len() != 3 {
        eprintln!("Usage: mm_xlat script set.mm out.gh");
        exit(1);
    }
    let scr_fn = &args[0];
    let inp_fn = &args[1];
    let out_fn = &args[2];
    if let Err(e) = run_file(scr_fn, inp_fn, out_fn) {
        eprintln!("Error: {:?}", e);
        exit(1);
    }
}
