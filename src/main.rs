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

//! A command line utility for the new Ghilbert format.

extern crate union_find;

use std::env;
use std::fs::File;
use std::io::Read;

mod htmlout;
use htmlout::HtmlOut;

mod lexer;
use lexer::Lexer;

mod parser;
use parser::Parser;

mod prooflistener;
use prooflistener::DebugListener;

mod sexp;
use sexp::{Intern, Sexp};

mod session;
use session::Session;

mod typeset;

mod unify;

fn my_main() -> ::std::io::Result<()> {
    let mut args = env::args();
    args.next();
    let mut verbose = true;
    let mut sexpr = false;
    let mut debug = false;
    for f in args {
        if f == "-q" {
            verbose = false;
            continue;
        } else if f == "-s" {
            sexpr = true;
            continue;
        } else if f == "-d" {
            debug = true;
            continue;
        }
        let mut file = File::open(f)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        let mut intern = Intern::new();
        if sexpr {
            let mut ix = 0;
            loop {
                match Sexp::parse(&mut intern, &contents[ix..]) {
                    Ok((sexp, len)) => {
                        if verbose {
                            sexp.print(&intern);
                            println!();
                        }
                        ix += len;
                    },
                    Err(e) => {
                        println!("parse error: {:?}", e);
                        break;
                    }
                }
            }
        } else {
            let lexer = Lexer::new(&contents);
            let parser = Parser::new(lexer);
            // A little code duplication here, but not so bad...
            if debug {
                let mut out = DebugListener;
                let mut session = Session::new(parser);
                if let Err(e) = session.run(&mut out) {
                    println!("err: {:?}", e);
                }
            } else {
                let mut out_file = File::create("out.html")?;
                let mut out = HtmlOut::new(&contents);
                let mut session = Session::new(parser);
                if let Err(e) = session.run(&mut out) {
                    println!("err: {:?}", e);
                }
                out.write(&mut out_file, session.get_parser())?;
            }
        }
    }
    Ok(())
}

fn main() {
    if let Err(e) = my_main() {
        println!("err: {}", e);
    }
}
