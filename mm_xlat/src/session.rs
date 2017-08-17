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

//! State from a Metamath session.

use parser::{Statement, Compressed};

pub struct Session {
}

impl Session {
    pub fn new() -> Session {
        Session {
        }
    }

    pub fn do_stmt(&mut self, stmt: Statement) {
        match stmt {
            Statement::Proof(label, concl, compr) => {
                if let Some(pos) = compr.iter().position(|&step| step == ")") {
                    let steps = Compressed::new(&compr[pos+1 ..]).collect::<Vec<_>>();
                    println!("compressed {} {:?} {:?} {:?}", label, concl,
                        &compr[1..pos], steps);
                } else {
                    panic!("proof {:?} not valid compressed format", compr);
                }
            }
            _ => println!("stmt {:?}", stmt),
        }
    }
}
