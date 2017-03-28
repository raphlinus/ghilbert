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

//! Parsing of s-expressions. Will be used for old-style Ghilbert, and also
//! for experimentation before the new parser is ready.

use std::collections::HashMap;

/// A context for interned identifiers.
pub struct Intern {
	map: HashMap<String, usize>,
	vals: Vec<String>,
}

impl Intern {
	pub fn new() -> Intern {
		Intern {
			map: HashMap::new(),
			vals: Vec::new(),
		}
	}

	pub fn intern(&mut self, s: &str) -> usize {
		if let Some(&result) = self.map.get(s) {
			return result;
		}
		let result = self.vals.len();
		self.vals.push(s.to_string());
		self.map.insert(s.to_string(), result);
		result
	}

	pub fn val(&self, ix: usize) -> &str {
		&self.vals[ix]
	}
}


pub enum Sexp {
	Atom(usize),
	List(Vec<Sexp>),
}

#[derive(Debug)]
pub enum ParseError {
	UnclosedParen,
	UnexpectedClose,
	Empty,
}

fn skip_whitespace(s: &str, mut ix: usize) -> usize {
	while ix < s.len() {
		match s.as_bytes()[ix] {
			b'\t' | b'\r' | b'\n' | b' ' => ix += 1,
			b'#' => {
				// TODO: can replace with memchr, if we care
				ix += 1;
				while ix < s.len() && s.as_bytes()[ix] != b'\n' {
					ix += 1;
				}
			}
			_ => return ix,
		}
	}
	ix
}

impl Sexp {
	pub fn parse(intern: &mut Intern, s: &str) -> Result<(Sexp, usize), ParseError> {
		let mut ix = skip_whitespace(s, 0);
		if ix == s.len() {
			return Err(ParseError::Empty);
		}
		match s.as_bytes()[ix] {
			b')' => return Err(ParseError::UnexpectedClose),
			b'(' => {
				ix += 1;
				let mut result = Vec::new();
				loop {
					ix = skip_whitespace(s, ix);
					if ix == s.len() {
						return Err(ParseError::UnclosedParen);
					}
					if s.as_bytes()[ix] == b')' {
						return Ok((Sexp::List(result), ix + 1));
					}
					let (child, len) = Sexp::parse(intern, &s[ix..])?;
					result.push(child);
					ix += len;
				}
			}
			_ => {
				let mut end = ix + 1;
				while end < s.len() {
					match s.as_bytes()[end] {
						b'\t' | b'\r' | b'\n' | b' ' | b'(' | b')' | b'#' => break,
						_ => end += 1,
					}
				}
				let atom = intern.intern(&s[ix..end]);
				Ok((Sexp::Atom(atom), end))
			}
		}
	}

	pub fn print(&self, intern: &Intern) {
		match *self {
			Sexp::Atom(atom) => print!("{}", intern.val(atom)),
			Sexp::List(ref list) => {
				let mut delim = '(';
				for child in list {
					print!("{}", delim);
					child.print(intern);
					delim = ' ';
				}
				print!(")");
			}
		}
	}
}
