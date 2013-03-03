// <license>
// This module implements a direct mode, in which changes to the editor
// window are reflected immediately into a stack view.

// text is a CanvasEdit object, stack is a canvas for drawing the stack view
GH.Direct = function(text, stack) {
    var self = this;
    this.text = text;
    this.text.clearImtrans();  // todo: hack
    this.stack = stack;
    this.text.addListener(function() { self.update(); });
    this.marker = null;
};

GH.splitrange = function(str, offset) {
    function token(beg, end) {
	var tok = new String(str.substring(beg, end));
	tok.beg = offset + beg;
	tok.end = offset + end;
	return tok;
    }

    var result = [];
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
    return result;
};

GH.Direct.replace_thmname = function (newname) {
    var elem = document.getElementById('thmname');
    while (elem.firstChild) {
      elem.removeChild(elem.firstChild);
    }
    elem.appendChild(document.createTextNode(newname));
    name = newname; // replace global 'name'.
};

GH.Direct.prototype.update = function() {
	var session = this.text.getSession();  // for ACE editing
	if (session && this.marker !== null) {
		session.removeMarker(this.marker);
		this.marker = null;
	}
	var auLink = document.getElementById("autounify");
	auLink.style.display='none';
	var thmctx = new GH.DirectThm(this.vg);
	this.thmctx = thmctx;
	var status = null;
	var i, loc;
	var offset = 0;
	var cursorPosition = this.text.getCursorPosition();
	for (i = 0; i < this.text.numLines() && status == null; i++) {
		var line = this.text.getLine(i);
		var spl = GH.splitrange(line, offset);
		for (var j = 0; j < spl.length; j++) {
			try {
				status = thmctx.tok(spl[j]);	
			} catch (ex) {
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
						that.update();
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
				status = "! " + ex;
			}
			if (status) {
				if (session) {
					var range = new this.text.Range(i, spl[j].beg-offset, i, spl[j].end-offset);
					var text = status;
					if (text.slice(0, 2) === '! ') {
						text = text.slice(2);
					}
				    this.marker = session.addMarker(range, "gh_error", "text", false);
				    session.setAnnotations([{row:i, column:spl[j].beg-offset, text:text, type:"error"}]);
				}
				loc = spl[j] + ' ' + spl[j].beg + ':' + spl[j].end;
				break;
			}
		}
		offset += line.length + 1;
	}
		var html = [];
		var proofStepHtml = [];
    if (thmctx.proofctx) {
    	pstack = thmctx.proofctx.mandstack;
			var stackHistory = thmctx.proofctx.stackHistory;
			for (var i = 0; i < stackHistory.length; i++) {
				stackHistory[i].display(0, proofStepHtml, cursorPosition);
			}
			if (pstack.length > 0) {
    		for (i = 0; i < pstack.length; i++) {
					GH.Direct.stepToHtmlDefault(GH.sexptohtml(pstack[i][1]), proofStepHtml);
    		}
    	}
			proofStepHtml.push(GH.Direct.textToHtml('&nbsp;'));
    }
    // keep height from bouncing around in common case
    while (proofStepHtml.length < GH.Direct.MINIMUM_LINES) {
			proofStepHtml.splice(0, 0, GH.Direct.textToHtml('&nbsp;'));
    }
    if (status) {
			proofStepHtml.push(GH.Direct.textToHtml(loc + ' ' + status));
    } else {
    	if (session) {
    		session.setAnnotations([]);
    	}
    }
		html = html.concat(proofStepHtml);
		this.stack.innerHTML = html.join('');
		for (var i = 0; i < stack.children.length; i++) {
			this.stack.children[i].onclick = function() {
				window.direct.update();
			}
		}
};

/**
 * The amount to indent the proof steps in pixels.
 */
GH.Direct.INDENTATION = 15;

/**
 * The minimum number of lines in the displayed stack. Blank lines are added if the
 * stack is smaller.
 */
GH.Direct.MINIMUM_LINES = 12;

GH.Direct.textToHtml = function(text) {
	return html = '<div class=\'proof-step-div\'>' + text + '</div>';
}

// Display a proof step with default settings, no highlighting.
GH.Direct.stepToHtmlDefault = function(text, proofStepHtml) {
	GH.Direct.stepToHtml(text, 0, false, false, 0, 0, proofStepHtml);
}

// Display a proof step.
//   text: The text inside the step.
//   indentation: How many times to indent.
//   isHighlighted: True if the step is currently highlighted.
//   isError: True if the step is displayed in red as an error.
//   textStart: The position of the first character to highlight in the editor when hovering over the proof step.
//   textEd: The position of the last character to highlight in the editor when hovering over the proof step.
//   proofStepHtml: The full list of proof steps. The output goes here.
GH.Direct.stepToHtml = function(text, indentation, isHighlighted, isError, textStart, textEnd, proofStepHtml) {
	var html = '';
	html += '<div class=\'proof-step-div\' onmousemove=\'GH.setSelectionRange(' + textStart + ',' + textEnd + ')\'>';
	if (isError) {
		if (isHighlighted) {
			html += '<span class=\'proof-step-span error-in-step highlighted-step\' ';
		} else {
			html += '<span class=\'proof-step-span error-in-step\' ';
		}
	}	else {
		if (isHighlighted) {
			html += '<span class=\'proof-step-span highlighted-step\' ';
		} else {
			html += '<span class=\'proof-step-span\' ';
		}
	}
	html += 'style=\'margin: 1px 0 1px ' + indentation * GH.Direct.INDENTATION + 'px\'>';
	html += text;
	html += '</span></div>\n';
	proofStepHtml.push(html);
};

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
	PROOF_END : 10
};

GH.DirectThm.prototype.pushEmptySExp_ = function(tok) {
	var newSExp = [];
	newSExp.beg = tok.beg;
	this.sexpstack.push(newSExp);
}

GH.DirectThm.prototype.tok = function(tok) {
	var stateType = GH.DirectThm.StateType;
	var state = this.state;
	var thestep = null;
	var i, pc;
	switch (state) {
		case stateType.THM:
			if (tok == 'thm') {
				this.state = stateType.POST_THM;
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
				GH.Direct.replace_thmname(tok);
				this.state = stateType.POST_NAME;
			}
			break;
		case stateType.POST_NAME:
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
				this.state = stateType.PROOF_END;
			} else {
				thestep = tok;
			}
			break;
		case stateType.FREE_VARIABLE:
		case stateType.HYPOTHESES:
		case stateType.S_EXPRESSION:
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
			this.proofctx.stackHistory.push(new GH.ProofStep([], tok + ' Extra Junk After Proof', tok.beg, tok.end, [], true));
			return 'extra junk after proof';
			break;
	}

  state = this.state;
  if (state == stateType.POST_FREE_VARIABLE) {
		// thestep has dv list
		this.fv = thestep;
		this.proofctx = new GH.ProofCtx();
		this.proofctx.varlist = [];
		this.proofctx.varmap = {};
	} else if (state == stateType.POST_HYPOTHESES) {
		if (thestep.length & 1) {
			return 'Odd length hypothesis list';
		}
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
		pc = this.proofctx;
		try {
			this.vg.kind_of(thestep, pc.varlist,
											pc.varmap, false, this.vg.syms);
			pc.num_nondummies = pc.varlist.length;
			pc.fvvarmap = this.vg.fvmap_build(this.fv, pc.varlist, pc.varmap);
		} catch (e2) {
			return "! " + e2;
		}
		this.concl = thestep || 'null';
  } else if (thestep != null && state == stateType.POST_S_EXPRESSION) {
		try {
			this.vg.check_proof_step(this.hypmap, thestep, this.proofctx);
		} catch (e3) {
			if (e3.found) {
				throw e3;
			}
			var stackHistory = this.proofctx.stackHistory;
			var removed = stackHistory.splice(0);
			stackHistory.push(new GH.ProofStep(removed, e3, tok.beg, tok.end, [], true));
			return "! " + e3;
		}
  } else if (state == stateType.PROOF_END) {
    pc = this.proofctx;
    if (pc.mandstack.length != 0) {
			//this.proofctx.stackHistory.push(new GH.ProofStep([], tok + ' Error', tok.beg, tok.end, [], true));
	    return '\n\nExtra mandatory hypotheses on stack at the end of the proof.';
		}
		if (pc.stack.length != 1) {
			return '\n\nStack must have one term at the end of the proof.';
		}
		if (!GH.sexp_equals(pc.stack[0], this.concl)) {
				return ('\n\nStack has:\n ' + GH.sexp_to_string(pc.stack[0]) +
						'\nWanted:\n ' + GH.sexp_to_string(this.concl));
		}
  }
  return null;
};
