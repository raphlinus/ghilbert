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

pub struct ProofOut {
    o: BufWriter<File>,
}

impl ProofOut {
    pub fn new<P: AsRef<Path>>(filename: P) -> Result<ProofOut> {
        let f = File::create(filename)?;
        Ok(ProofOut { o: BufWriter::new(f) })
    }

    /// Write text to the proof output file.
    pub fn write(&mut self, s: &str) {
        write!(self.o, "{}", s).unwrap();
    }
}
