// <license>
// This module implements a direct mode, in which changes to the editor
// window are reflected immediately into a stack view.

// text is a CanvasEdit object, stack is a canvas for drawing the stack view
// suggestArea is a place for suggesting proof steps.
GH.Direct = function(text, stack, suggestArea) {
    var self = this;
    this.text = text;
    this.text.clearImtrans();  // todo: hack
    this.stack = stack;
    this.text.addListener(function() { self.update(true); });
    this.marker = null;
	var buttonController = new GH.ButtonController(suggestArea);
	this.prover = new GH.Prover(buttonController, this);

	this.thmctx = null;
	this.auLink = document.getElementById("autounify");
	this.status = null;
	this.session = null;
	this.offset = 0;
	this.rootSegments = [];
	this.notationGuide = null;
};

/**
 * Split a string in a primary and secondary set of tokens. The secondary tokens
 * are used for styling the proof.
 *   - str: The string to split into tokens.
 *   - offset: The character position of the start of the string within the proof.
 */
GH.splitrange = function(str, offset) {
    function token(beg, end) {
		var tok = new String(str.substring(beg, end));
		tok.beg = offset + beg;
		tok.end = offset + end;
		return tok;
    }

    var result = [];
	var secondary = [];
    var beg = 0;
    for (var i = 0; i < str.length; i++) {
		var c = str.charAt(i);
		if (c == ' ') {
			if (i != beg) {
				result.push(token(beg, i));
			}
			beg = i + 1;
		} else if (c == "(" || c == ")") {
			if (i != beg) {
				result.push(token(beg, i));
			}
			result.push(token(i, i+1));
			beg = i + 1;
		} else if (c == '#') {
			// The string '##' indicates that what follows is a styling command.
			// These commands are placed in the set of secondary tokens.
			if ((i + 1 < str.length) && (str.charAt(i + 1) == '#')) {
				var tokens = GH.splitrange(str.substring(i + 2, str.length), offset + i + 2);
				secondary = tokens.primary;
			}
			if (i != beg) {
				result.push(token(beg, i));
			}
			beg = str.length;
			break;
		}
    }
    if (beg != str.length) {
		result.push(token(beg, str.length));
    }
    return {primary: result, secondary: secondary};
};

GH.Direct.replace_thmname = function (newname, styling) {
    var elem = document.getElementById('thmname');
    while (elem.firstChild) {
      elem.removeChild(elem.firstChild);
    }
	var title = styling ? styling.title : '';
	if (title != '') {
		title += ' - ' + newname;
	} else {
		title = newname;
	}
    elem.appendChild(document.createTextNode(title));
    name = newname; // replace global 'name'.
};

GH.Direct.counter = 0;

GH.Direct.prototype.update = function(refreshProofs) {
	GH.Direct.counter++;
	this.session = this.text.getSession();  // for ACE editing
	if (this.session) {
		if (this.marker !== null) {
			this.session.removeMarker(this.marker);
			this.marker = null;
		}
   		this.session.setAnnotations([]);
	}
	this.auLink.style.display='none';
	if (this.thmctx) {
		this.thmctx.clearNewSyms();
	}
	this.thmctx = new GH.DirectThm(this.vg);
	this.status = null;
	this.offset = 0;
	var cursorPosition = this.text.getCursorPosition();
	this.stack.innerHTML = '';
	for (var i = 0; i < this.text.numLines() && this.status == null; i++) {
		this.parseText(this.text.getLine(i));
	}
	if (refreshProofs) {
		this.updateProofs(cursorPosition);
	}
};

GH.Direct.prototype.addAutoUnifyLink = function(ex) {
	var auLink = this.auLink;
	if (ex.found && (ex.found.beg)) {
		auLink.style.display = 'inline';
		auLink.innerHTML = "AutoUnify: Replace " + ex.found + "[" + ex.found.beg
		+ ":" + ex.found.end + "]" + " with " + ex.expected + "?";
		var that = this;
		auLink.onclick = function() {
			if (auLink.onmouseout) {
				auLink.onmouseout();
			}
			that.text.splice(ex.found.beg, ex.found.end - ex.found.beg, ex.expected);
			that.update(true);
			if (auLink.style.display != 'none') {
				auLink.onmouseover();
			}
			return false;
		};
		var textarea = document.getElementById("canvas");
		if (textarea.setSelectionRange) {
			auLink.onmouseover = function() {
				var cursor = textarea.selectionEnd;
				auLink.onmouseout = function() {
					textarea.setSelectionRange(cursor, cursor);
					delete auLink.onmouseout;
				};
				textarea.setSelectionRange(ex.found.beg,
					ex.found.end);
			};			  
		}
	}
};

// Parses Ghilbert text and updates thmctx based on the text.
GH.Direct.prototype.parseText = function(text) {
	var thmctx = this.thmctx;
	thmctx.styleScanner.read_styling(text.replace(/\(|\)/g, ' $& '));
	var tokens = GH.splitrange(text, this.offset);
	var spl = tokens.primary;
	thmctx.applyStyling(tokens.secondary);
	for (var j = 0; j < spl.length; j++) {
		try {
			this.status = thmctx.tok(spl[j]);	
		} catch (ex) {
			this.addAutoUnifyLink(ex);
			this.status = "! " + ex;
		}
		if (this.status) {
			if (this.session) {
				var range = new this.text.Range(i, spl[j].beg - this.offset, i, spl[j].end - this.offset);
				var text = this.status;
				if (text.slice(0, 2) === '! ') {
					text = text.slice(2);
				}
				this.marker = this.session.addMarker(range, "gh_error", "text", false);
				this.session.setAnnotations([{row:i, column:spl[j].beg - this.offset, text:text, type:"error"}]);
			}
			this.status = spl[j] + ' ' + spl[j].beg + ':' + spl[j].end + ' ' + this.status;
			this.stack.appendChild(GH.Direct.textToHtml(this.status));
			break;
		}
	}
	this.offset += text.length + 1;
};



// Display the proofs in the right panel.
GH.Direct.prototype.updateProofs = function(cursorPosition) {
	var thmctx = this.thmctx;
    if (thmctx.proofctx) {
    	pstack = thmctx.proofctx.mandstack;
		thmctx.history.push(thmctx.proofctx.stackHistory);
		thmctx.hierarchies.push(thmctx.proofctx.hierarchy);
		var shownHistory = thmctx.history[thmctx.history.length - 1];
		for (var i = thmctx.history.length - 2; i >= 0; i--) {
			for (var j = 0; j < thmctx.history[i].length; j++) {
				if (cursorPosition <= thmctx.hierarchies[i].end) {
					shownHistory = thmctx.history[i];
				}
			}
		}		
		this.rootSegments = [];
		this.notationGuide = new GH.notationGuide();
		for (var j = 0; j < shownHistory.length; j++) {
			var summary = (j == 0) ? thmctx.styleScanner.summary : '';
			this.rootSegments.push(shownHistory[j].displayStack(this.stack, summary, j, cursorPosition));
			this.notationGuide.addStep(shownHistory[j]);
		}
		
		var expectedTypes = this.thmctx.getExpectedTypes(pstack);
		GH.ProofStep.displayInputArguments(this.stack, pstack, expectedTypes, cursorPosition);
		
		if (shownHistory.length > 0) {
			this.notationGuide.render(this.stack);
		}
		
		this.stack.appendChild(GH.Direct.textToHtml('&nbsp;'));
    }
	if (thmctx && thmctx.proofctx) {
		this.prover.update(thmctx.proofctx.stackHistory, thmctx.proofctx.mandstack);
	} else {
		this.prover.update([], []);
	}
}

GH.Direct.prototype.getTheorems = function() {	
	if (this.thmctx.proofctx) {
		return this.thmctx.proofctx.stackHistory;
	} else {
		return null;
	}
};

GH.Direct.prototype.getStack = function() {	
	if (this.thmctx.proofctx) {
		return this.thmctx.proofctx.mandstack;
	} else {
		return null;
	}
};

GH.Direct.prototype.insertText = function(text) {
	this.text.moveCursorToEnd();
	this.text.insertText(text);

	// Remove line breaks.
	text = text.replace(/(\r\n|\n|\r)/gm,"");
	this.parseText(text);
}

GH.Direct.prototype.removeExpression = function(expression) {
	var begin = expression.begin;
	var end = expression.end;
	this.text.splice(begin, end - begin, '');
	this.update(false);
};

// Reverse the order of the last two steps.
GH.Direct.prototype.reverseLastSteps = function() {
	var steps = this.thmctx.proofctx.stackHistory;
	var last = steps[steps.length - 1];
	var secondLast = steps[steps.length - 2];
	var secondSize = (secondLast.end - secondLast.getBeginning());
	var secondLastText = this.text.splice(secondLast.getBeginning(), secondSize, '');
	secondLastText = ' ' + secondLastText.join('');

	var insertionPoint = last.end - secondSize;
	this.text.splice(insertionPoint, insertionPoint, secondLastText);
	this.update(true);
};

// This is called when starting on a new theorem that the current theorem needs.
// It removes the current partially complete theorem which will infer with the new one.
// It is restored later.
GH.Direct.prototype.removeCurrentTheorem = function() {
	var thmCount = this.thmctx.history.length;
	var begin = 0;
	if (thmCount >= 1) {
		// If the last theorem is still open cut it out, otherwise cut everything past it.
		if (this.thmctx.hierarchies[thmCount - 1].isOpen()) {
			begin = (thmCount >= 2) ? this.thmctx.hierarchies[thmCount - 2].end : 0;
		} else {
			begin = this.thmctx.hierarchies[thmCount - 1].end;
		}
	}
	var end = this.text.getValue().length;
	var currentThm = this.text.splice(begin, end - begin, '');
	this.update(false);
	return currentThm;
};

/**
 * The minimum number of lines in the displayed stack. Blank lines are added if the
 * stack is smaller.
 */
GH.Direct.MINIMUM_LINES = 12;

GH.Direct.textToHtml = function(text) {
	var div = document.createElement("div");
	div.innerHTML = text;
	return div;
}

GH.DirectThm = function(vg) {
	this.vg = vg;
	this.thmname = null;
	this.sexpstack = [];
	this.hypmap = {};
	this.state = GH.DirectThm.StateType.THM;
	this.proofctx = null;
	this.fv = null;
	this.hyps = null;
	this.concl = null;
	this.thmType = GH.DirectThm.ThmType.NORMAL;

	// A list of symbols added in this directThm.
	this.newSyms = [];

	// A set of the previous stack histories. Used when there are multiple proofs in the editor.
	this.history = [];

	// A set of the previous stack hierarchies. Used when there are multiple proofs in the editor.
	this.hierarchies = [];
	
	this.styleScanner = new GH.StyleScanner();

	this.tagNames = [];
};

GH.DirectThm.ThmType = {
	NORMAL : 0,
	DEFINITION : 1,
};

GH.DirectThm.StateType = {
	THM : 0,
	POST_THM : 1,
	NAME : 2,
	POST_NAME : 3,
	FREE_VARIABLE : 4,
	POST_FREE_VARIABLE : 5,
	HYPOTHESES : 6,
	POST_HYPOTHESES : 7,
	S_EXPRESSION : 8,
	POST_S_EXPRESSION : 9,
	PROOF_END : 10,
	KIND : 11,
	POST_KIND : 12,
	DEFINED_TERM: 13,
	POST_DEFINED_TERM: 14,
};

GH.DirectThm.prototype.clearNewSyms = function() {
	for (var i = 0; i < this.newSyms.length; i++) {
		delete this.vg.syms[this.newSyms[i]];
	}
};

GH.DirectThm.prototype.pushEmptySExp_ = function(tok) {
	var newSExp = [];
	newSExp.beg = tok.beg;
	this.sexpstack.push(newSExp);
}

// Styling tag to increment the depth. Proof steps with a higher depth are
// less important and less visible.
GH.DirectThm.INCREMENT_DEPTH_TAG_ = '<d';

// Styling tag to decrement the depth. Proof steps with a lower depth are
// more important and more visible.
GH.DirectThm.DECREMENT_DEPTH_TAG_ = '</d';

// Update the depth based on the styling.
GH.DirectThm.prototype.applyStyling = function(styling) {
	if (styling[0] && styling[0].indexOf(GH.DirectThm.INCREMENT_DEPTH_TAG_) == 0) {
		var begin = styling[0].beg;
		var splitStyling = styling.join(' ').split('\'');
		var tagName = (splitStyling.length == 3) ? splitStyling[1] : null;
		this.tagNames.push(tagName);

		var newHierarchy = new GH.ProofHierarchy(null, begin, tagName);
		this.proofctx.hierarchy.appendChild(newHierarchy);
		this.proofctx.hierarchy = newHierarchy;
	} else if (styling[0] && styling[0].indexOf(GH.DirectThm.DECREMENT_DEPTH_TAG_) == 0) {
		this.proofctx.hierarchy.end = styling[styling.length - 1].end
		this.proofctx.hierarchy = this.proofctx.hierarchy.parent;
		this.tagNames.pop();
	}
}

GH.DirectThm.getType = function(typeArray) {
	var type = typeArray[1];
	// It's a binding variable if it's a var instead of tvar.
	if ((typeArray[0] == 'var') && (type == 'nat')) {
		type = 'bind';
	}
	return type;
};

GH.DirectThm.prototype.getExpectedTypes = function(actualArgs) {
	if (this.vg.error_step) {
		var expectedTypes = [];
		var actualTypes = [];
		var expectations = this.vg.error_step[4];
		for (var i = 0; i < expectations.length; i++) {
			expectedTypes.push(GH.DirectThm.getType(expectations[i]));
		}
		
		var actualTypes = [];
		for (var i = 0; i < actualArgs.length; i++) {
			actualTypes.push(GH.DirectThm.getType(actualArgs[i][0]));
		}
		var totalLength = Math.max(expectedTypes.length, actualTypes.length);
		for (var i = expectedTypes.length; i < totalLength; i++) {
			expectedTypes.push('empty');
		}
		for (var i = actualTypes.length; i < totalLength; i++) {
			actualTypes.push('empty');
		}
		return [expectedTypes, actualTypes];
	} else {
		return [];
	}
};

GH.DirectThm.prototype.tok = function(tok) {
	var stateType = GH.DirectThm.StateType;
	var thmType = GH.DirectThm.ThmType;
	var state = this.state;
	var thestep = null;
	var i, pc;
	switch (state) {
		case stateType.THM:
			if (tok == 'thm') {
				this.state = stateType.POST_THM;
			} else if (tok == 'defthm') {
				this.state = stateType.POST_THM;
				this.thmType = thmType.DEFINITION;
			} else {
				return 'expected thm';
			}
			break;
		case stateType.POST_THM:
			if (tok == '(') {
				this.state = stateType.NAME;
			} else {
				return 'expected (';
			}
			break;
		case stateType.NAME:
			if (tok == '(' || tok == ')') {
				return 'expected thm name';
			} else {
				this.thmname = tok;
				if (this.vg.syms.hasOwnProperty(tok)) {
					return "A symbol of name '" + tok + "' already exists.";
				}
				// Is this the best place to do this?
				GH.Direct.replace_thmname(tok, this.styleScanner.get_styling(''));
				if (this.thmType == thmType.NORMAL) {
					this.state = stateType.POST_NAME;
				} else {
					// Definitions have the kind after the name.
					this.state = stateType.KIND;
				}
			}
			break;
		case stateType.KIND:
			// We currently don't do anything with the kind in defthms, but we still need to parse it.
			this.state = stateType.POST_KIND;
			break;
		case stateType.POST_KIND:
			if (tok == '(') {
				this.pushEmptySExp_(tok);
				this.state = stateType.DEFINED_TERM;
			} else {
				return "expected ( to open defined term";
			}
			break;
		case stateType.POST_NAME:
		case stateType.POST_DEFINED_TERM:
			if (tok == '(') {
				this.pushEmptySExp_(tok);
				this.state = stateType.FREE_VARIABLE;
			} else {
				return "expected ( to open dv's";
			}
			break;
		case stateType.POST_FREE_VARIABLE:
			if (tok == '(') {
			  this.pushEmptySExp_(tok);
				this.state = stateType.HYPOTHESES;
			} else {
				return "expected ( to open hyps";
			}
			break;
		case stateType.POST_HYPOTHESES:
			if (tok == '(') {
			  this.pushEmptySExp_(tok);
				this.state = stateType.S_EXPRESSION;
			} else if (tok == ')') {
				return 'expected proof stmt';
			} else {
				thestep = tok;
				this.state = stateType.POST_S_EXPRESSION;
			}
			break;
		case stateType.POST_S_EXPRESSION:
			if (tok == '(') {
			  this.pushEmptySExp_(tok);
				this.state = stateType.S_EXPRESSION;
			} else if (tok == ')') {
				if (this.thmType != thmType.DEFINITION) {
					pc = this.proofctx;
					if (pc.mandstack.length != 0) {
						//this.proofctx.stackHistory.push(new GH.ProofStep([], tok + ' Error', tok.beg, tok.end, [], true, null));
						return '\n\nExtra mandatory hypotheses on stack at the end of the proof.';
					}
					if (pc.stack.length != 1) {
						return '\n\nStack must have one term at the end of the proof.';
					}
					if (!GH.sexp_equals(pc.stack[0], this.concl)) {
						return ('\n\nStack has:\n ' + GH.sexp_to_string(pc.stack[0]) +
								'\nWanted:\n ' + GH.sexp_to_string(this.concl));
					}
					
					var new_hyps = [];
					if (this.hyps) {
						for (j = 1; j < this.hyps.length; j += 2) {
							new_hyps.push(this.hyps[j]);
						}
					}
					// Hmm, could possibly save proofctx.varmap instead of this.syms...
					// If we go to index variable expression storage we don't need either
					this.vg.add_assertion('thm', this.thmname, this.fv, new_hyps, this.concl,
									   this.proofctx.varlist, this.proofctx.num_hypvars,
									   this.proofctx.num_nondummies, this.vg.syms, this.styleScanner.get_styling(''));
					this.newSyms.push(this.thmname);
	
					this.state = stateType.THM;
					// Make the end of the hierarchy equal to the final end to the theorem.
					this.proofctx.hierarchy.end = tok.end;
					this.concl = null;
					this.hypmap = {};
				} else {
					var conclusion = new GH.ProofStep('Definition', [], this.concl, this.concl.beg, this.concl.end, [], false, null)
					conclusion.hierarchy = new GH.ProofHierarchy(null, 0, 'Definition');
					this.proofctx.stackHistory.push(conclusion);
				}
			} else {
				thestep = tok;
			}
			break;
		case stateType.FREE_VARIABLE:
		case stateType.HYPOTHESES:
		case stateType.S_EXPRESSION:
		case stateType.DEFINED_TERM:
			if (tok == '(') {
			  this.pushEmptySExp_(tok);
			} else if (tok == ')') {
				if (this.sexpstack.length == 1) {
					// When the last s-expression is popped, increment the state.
					thestep = this.sexpstack.pop();
					thestep.end = tok.end;
					this.state += 1;
				} else {
					// Otherwise, attach the last s-expression as a child of the one before it.
					var last = this.sexpstack.pop();
					last.end = tok.end;
					this.sexpstack[this.sexpstack.length - 1].push(last);
				}
			} else {
				this.sexpstack[this.sexpstack.length - 1].push(tok);
			}
			break;
		case stateType.PROOF_END:
			this.proofctx.stackHistory.push(new GH.ProofStep('Error', [], tok + ' Extra Junk After Proof', tok.beg, tok.end, [], true, null));
			return 'extra junk after proof';
			break;
	}

  state = this.state;
  if (state == stateType.POST_FREE_VARIABLE) {
		// thestep has dv list
		this.fv = thestep;
		if (this.proofctx) {
			this.history.push(this.proofctx.stackHistory);
			this.hierarchies.push(this.proofctx.hierarchy);
		}
		this.proofctx = new GH.ProofCtx();
		this.proofctx.varlist = [];
		this.proofctx.varmap = {};
	} else if (state == stateType.POST_HYPOTHESES) {
		if (thestep.length & 1) {
			return 'Odd length hypothesis list';
		}
		this.hyps = [];
		for (i = 0; i < thestep.length; i += 2) {
			var hypname = thestep[i];
			if (GH.typeOf(hypname) != 'string') {
				return 'Hyp label must be string';
			}
			if (this.hypmap.hasOwnProperty(hypname)) {
				return 'Repeated hypothesis label ' + hypname;
			}
			var hyp = thestep[i + 1];
			try {
					this.vg.kind_of(hyp, this.proofctx.varlist,
				this.proofctx.varmap, false, this.vg.syms);
			} catch (e1) {
					return "!" + e1;
			}
			this.hypmap[hypname] = hyp;
			this.hyps = thestep;
			//log ('hypothesis: ' + hypname + ' ' + GH.sexp_to_string(hyp));
		}
		this.proofctx.num_hypvars = this.proofctx.varlist.length;
  } else if (state == stateType.POST_S_EXPRESSION && this.concl == null) {
		if (this.thmType != thmType.DEFINITION) {
			pc = this.proofctx;
			try {
				this.vg.kind_of(thestep, pc.varlist, pc.varmap, false, this.vg.syms);
				pc.num_nondummies = pc.varlist.length;
				pc.fvvarmap = this.vg.fvmap_build(this.fv, pc.varlist, pc.varmap);
			} catch (e2) {
				return "! " + e2;
			}
		}
		this.concl = thestep || 'null';
  } else if (thestep != null && state == stateType.POST_S_EXPRESSION && (this.thmType != thmType.DEFINITION)) {
		try {
			var tagName = (this.tagNames.length > 0) ? this.tagNames[this.tagNames.length - 1] : null;
			this.vg.check_proof_step(this.hypmap, thestep, this.proofctx, tagName);
		} catch (e3) {
			if (e3.found) {
				throw e3;
			}
			var stackHistory = this.proofctx.stackHistory;
			var removed = stackHistory.splice(0);
			stackHistory.push(new GH.ProofStep('Error', removed, e3, tok.beg, tok.end, [], true, null));
			return "! " + e3;
		}
  }
  return null;
};
