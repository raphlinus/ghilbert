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
	var stext = [];
	var thmctx = new GH.DirectThm(this.vg);
	this.thmctx = thmctx;
	var status = null;
	var i, loc;
	var offset = 0;
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

    //stext.push('state: ' + thmctx.state);
    //stext.push('ss: ' + GH.sexp_to_string(thmctx.sexpstack));
    sp = '&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;';
    if (thmctx.hyps != null) {
    	for (i = 0; i < thmctx.hyps.length; i += 2) {
    		stext.push(GH.sexptohtml(thmctx.hyps[i+1]) + 
    			sp + '# ' + GH.escapeHtml(thmctx.hyps[i]));
    	}
    }
    if (thmctx.concl != null) {
    	stext.push(GH.sexptohtml(thmctx.concl) + sp + '# WTS');
    }
    if (thmctx.proofctx) {
    	var pstack = thmctx.proofctx.stack;
    	for (i = 0; i < pstack.length; i++) {
    		stext.push(GH.sexptohtml(pstack[i]));
    	}
    	pstack = thmctx.proofctx.mandstack;
    	if (pstack.length > 0) {
    		for (i = 0; i < pstack.length; i++) {
    			stext.push(GH.sexptohtml(pstack[i][1]) + sp + '# W' + i);
    		}
    	}
    }
    // keep height from bouncing around in common case
    while (stext.length < 10) {
    	stext.push('&nbsp;');
    }
    if (status) {
    	stext.push(loc + ' ' + status);
    } else {
    	if (session) {
    		session.setAnnotations([]);
    	}
    }
    GH.updatemultiline(stext, this.stack);
};

// Update an element so each HTML string is a separate child div
GH.updatemultiline = function(strings, element) {
    var html = [];
    for (var i = 0; i < strings.length; i++) {
        html.push('<div>', strings[i], '</div>\n');
    }
    element.innerHTML = html.join('');
}

GH.DirectThm = function(vg) {
    this.vg = vg;
    this.thmname = null;
    this.sexpstack = [];
    this.hypmap = {};
    this.state = 0;
    this.proofctx = null;
    this.fv = null;
    this.hyps = null;
    this.concl = null;
};

GH.DirectThm.prototype.tok = function(tok) {
    var state = this.state;
    var thestep = null;
    var i, pc;
    if (state == 0) {
	if (tok == 'thm') {
	    this.state = 1;
	} else {
	    return 'expected thm';
	}
    } else if (state == 1) {
	if (tok == '(') {
	    this.state = 2;
	} else {
	    return 'expected (';
	}
    } else if (state == 2) {
	if (tok == '(' || tok == ')') {
	    return 'expected thm name';
	} else {
	    this.thmname = tok;
	    if (this.vg.syms.hasOwnProperty(tok)) {
	        return "A symbol of name '" + tok + "' already exists.";
	    }
	    // Is this the best place to do this?
	    GH.Direct.replace_thmname(tok);
	    this.state = 3;
	}
    } else if (state == 3) {
	if (tok == '(') {
	    this.sexpstack.push([]);
	    this.state = 5;
	} else {
	    return "expected ( to open dv's";
	}
    } else if (state == 4) {
	if (tok == '(') {
	    this.sexpstack.push([]);
	    this.state = 7;
	} else {
	    return "expected ( to open hyps";
	}
    } else if (state == 6) {
	if (tok == '(') {
	    this.sexpstack.push([]);
	    this.state = 9;
	} else if (tok == ')') {
	    return 'expected proof stmt';
	} else {
	    thestep = tok;
	    this.state = 8;
	}
    } else if (state == 8) {
	if (tok == '(') {
	    this.sexpstack.push([]);
	    this.state = 9;
	} else if (tok == ')') {
	    this.state = 10;
	} else {
	    thestep = tok;
	}
    } else if (state == 5 || state == 7 || state == 9) {
	if (tok == '(') {
	    this.sexpstack.push([]);
	} else if (tok == ')') {
	    if (this.sexpstack.length == 1) {
		thestep = this.sexpstack.pop();
		this.state -= 1;
	    } else {
		var last = this.sexpstack.pop();
		this.sexpstack[this.sexpstack.length - 1].push(last);
	    }
	} else {
	    this.sexpstack[this.sexpstack.length - 1].push(tok);
	}
    } else if (state == 10) {
	return 'extra junk after proof';
    }
    state = this.state;
    if (state == 4) {
	// thestep has dv list
        this.fv = thestep;
	this.proofctx = new GH.ProofCtx();
	this.proofctx.varlist = [];
	this.proofctx.varmap = {};
    } else if (state == 6) {
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
    } else if (state == 8 && this.concl == null) {
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
    } else if (thestep != null && state == 8) {
	try {
	    this.vg.check_proof_step(this.hypmap, thestep, this.proofctx);
	} catch (e3) {
	    if (e3.found) {
		throw e3;
	    }
	    return "! " + e3;
	}
    } else if (state == 10) {
        pc = this.proofctx;
        if (pc.mandstack.length != 0) {
	    return '\n\nExtra mand hyps on stack at end of proof';
	}
	if (pc.stack.length != 1) {
	    return '\n\nStack must have one term at end of proof';
	}
	if (!GH.sexp_equals(pc.stack[0], this.concl)) {
	    return ('\n\nStack has:\n ' + GH.sexp_to_string(pc.stack[0]) +
		   '\nWanted:\n ' + GH.sexp_to_string(this.concl));
	}
    }
    return null;
};
