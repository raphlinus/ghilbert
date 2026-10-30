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

//! Scripting to guide the translation process.

use std::fs::File;
use std::io::{BufRead, BufReader, Result};
use std::path::Path;

pub struct Script {
    i: BufReader<File>,
    mode: Mode,
}

enum Mode {
    Ready,
    Copy,
}

pub enum Command {
    CopyLine(String),
    RunThrough(String),
    /// Run up to (but not including) the labeled statement.
    RunUntil(String),
    Skip(String),
    /// Write a theorem as an axiom, without its proof.
    Assume(String),
    /// Keep all setvar variables of these statements bound (see Session).
    BoundForm(Vec<String>),
    /// Write a theorem with a hand-written proof (the lines of its body).
    Prove(String, String),
}

impl Script {
    pub fn new<P: AsRef<Path>>(filename: P) -> Result<Script> {
        let f = File::open(filename)?;
        Ok(Script {
            i: BufReader::new(f),
            mode: Mode::Ready,
        })
    }
}

impl Iterator for Script {
    type Item = Command;

    fn next(&mut self) -> Option<Command> {
        let mut buf = String::new();
        loop {
            buf.clear();
            let n = self.i.read_line(&mut buf).expect("error reading script");
            if n == 0 { return None; }
            match self.mode {
                Mode::Ready => {
                    let l = buf.split_whitespace().collect::<Vec<_>>();
                    if l.is_empty() || l[0] == "#" {
                        continue;
                    }
                    match l[0] {
                        "copy" => self.mode = Mode::Copy,
                        "run_through" => return Some(Command::RunThrough(l[1].to_string())),
                        "run_until" => return Some(Command::RunUntil(l[1].to_string())),
                        "skip" => return Some(Command::Skip(l[1].to_string())),
                        "assume" => return Some(Command::Assume(l[1].to_string())),
                        "bound_form" => return Some(Command::BoundForm(
                            l[1..].iter().map(|s| s.to_string()).collect())),
                        "prove" => {
                            let label = l[1].to_string();
                            let mut body = String::new();
                            loop {
                                let mut line = String::new();
                                let n = self.i.read_line(&mut line).expect("error reading script");
                                if n == 0 || line.trim() == "--" { break; }
                                body.push_str(&line);
                            }
                            return Some(Command::Prove(label, body));
                        }
                        "replace" => {
                            self.mode = Mode::Copy;
                            return Some(Command::Skip(l[1].to_string()));
                        }
                        _ => panic!("unknown command {}", buf.trim()),
                    }
                }
                Mode::Copy => {
                    if buf.trim() == "--" {
                        self.mode = Mode::Ready;
                    } else {
                        return Some(Command::CopyLine(buf));
                    }
                }
            }
        }
    }
}
