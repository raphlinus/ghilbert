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
use parser::{Scanner, Parser, Statement, Compressed};

mod session;
use session::Session;

fn run_file(filename: &str) -> io::Result<()> {
    println!("running {}", filename);
    let mut file = File::open(filename)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    let s = Scanner::new(&contents);
    let p = Parser::new(s);
    let mut sess = Session::new();
    for stmt in p {
        sess.do_stmt(stmt);
    }
    Ok(())
}

fn main() {
    let mut inp_fn = None;
    for arg in env::args().skip(1) {
        if inp_fn.is_some() {
            eprintln!("More than one input filename");
            exit(1);
        }
        inp_fn = Some(arg);
    }
    if let Some(inp_fn) = inp_fn {
        if let Err(e) = run_file(&inp_fn) {
            eprintln!("Error: {:?}", e);
            exit(1);
        }
    } else {
        eprintln!("More than one input filename");
        exit(1);
    }
}
