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

mod lexer;
use lexer::Lexer;

mod sexp;
use sexp::{Intern, Sexp};

mod unify;

fn my_main() -> ::std::io::Result<()> {
    let mut args = env::args();
    args.next();
    let mut verbose = true;
    let mut toks = false;
    for f in args {
        if f == "-q" {
            verbose = false;
            continue;
        } else if f == "-t" {
            toks = true;
            continue;
        }
        let mut file = File::open(f)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        let mut intern = Intern::new();
        if toks {
            let mut lexer = Lexer::new(&contents);
            lexer.intern("kind");
            while let Some(tok) = lexer.next() {
                println!("tok {}", lexer.tok_str(tok));
            }
        } else {
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
        }
    }
    Ok(())
}

fn main() {
    if let Err(e) = my_main() {
        println!("err: {}", e);
    }
}
