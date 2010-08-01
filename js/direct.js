// <license>
// This module implements a direct mode, in which changes to the editor
// window are reflected immediately into a stack view.

// text is a CanvasEdit object, stack is a canvas for drawing the stack view
GH.Direct = function(text, stack) {
    var self = this;
    this.text = text;
    this.text.clearImtrans();  // todo: hack
    this.stack = new GH.CanvasEdit(stack);
    this.stack.cursorvisible = false;
    this.text.addListener(function() { self.update(); });
};

GH.splitrange = function(str) {
    var result = [];
    var beg = 0;
    for (var i = 0; i < str.length; i++) {
	var c = str.charAt(i);
	if (c === ' ') {
	    if (i !== beg) {
		result.push({tok: str.substring(beg, i), beg: beg, end: i});
	    }
	    beg = i + 1;
	} else if (c === "(" || c === ")") {
	    if (i !== beg) {
		result.push({tok: str.substring(beg, i), beg: beg, end: i});
	    }
	    result.push({tok: str.substring(i, i+1), beg: i, end: i+1});
	    beg = i + 1;
	} else if (c === '#') {
	    if (i !== beg) {
		result.push({tok: str.substring(beg, i), beg: beg, end: i});
	    }
	    beg = str.length;
	    break;
	}
    }
    if (beg !== str.length) {
	result.push({tok: str.substring(beg), beg: beg, end: str.length});
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
    this.stack.text = [];
    var thmctx = new GH.DirectThm(this.vg);
    this.thmctx = thmctx;
    var status = null;
    var i, loc;
    var lines = this.text.getLines()
    for (i = 0; i < lines.length && status === null; i++) {
	var spl = GH.splitrange(lines[i]);
	for (var j = 0; j < spl.length; j++) {
	    status = thmctx.tok(spl[j].tok);
	    if (status) {
		loc = spl[j].tok + ' ' + spl[j].beg + ':' + spl[j].end;
		break;
	    }
	}
    }
    var stext = this.stack.text;

    //stext.push('state: ' + thmctx.state);
    //stext.push('ss: ' + GH.sexp_to_string(thmctx.sexpstack));
    if (thmctx.hyps !== null) {
        for (i = 0; i < thmctx.hyps.length; i += 2) {
	    stext.push(GH.sexptounicode(thmctx.hyps[i+1]) + 
					'      # ' + thmctx.hyps[i]);
	}
    }
    if (thmctx.concl !== null) {
        stext.push(GH.sexptounicode(thmctx.concl) + '      # WTS');
    }
    if (thmctx.proofctx) {
	var pstack = thmctx.proofctx.stack;
	for (i = 0; i < pstack.length; i++) {
	    stext.push(GH.sexptounicode(pstack[i]));
	}
	pstack = thmctx.proofctx.mandstack;
	if (pstack.length > 0) {
	    for (i = 0; i < pstack.length; i++) {
	        stext.push(GH.sexptounicode(pstack[i][1]) + '      # W' + i);
	    }
	}
    }
    if (status) {
	this.stack.text.push(loc + ' ' + status);
    }
    this.stack.dirty();
};

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
    if (state === 0) {
	if (tok === 'thm') {
	    this.state = 1;
	} else {
	    return 'expected thm';
	}
    } else if (state === 1) {
	if (tok === '(') {
	    this.state = 2;
	} else {
	    return 'expected (';
	}
    } else if (state === 2) {
	if (tok === '(' || tok === ')') {
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
    } else if (state === 3) {
	if (tok === '(') {
	    this.sexpstack.push([]);
	    this.state = 5;
	} else {
	    return "expected ( to open dv's";
	}
    } else if (state === 4) {
	if (tok === '(') {
	    this.sexpstack.push([]);
	    this.state = 7;
	} else {
	    return "expected ( to open hyps";
	}
    } else if (state === 6) {
	if (tok === '(') {
	    this.sexpstack.push([]);
	    this.state = 9;
	} else if (tok === ')') {
	    return 'expected proof stmt';
	} else {
	    thestep = tok;
	    this.state = 8;
	}
    } else if (state === 8) {
	if (tok === '(') {
	    this.sexpstack.push([]);
	    this.state = 9;
	} else if (tok === ')') {
	    this.state = 10;
	} else {
	    thestep = tok;
	}
    } else if (state === 5 || state === 7 || state === 9) {
	if (tok === '(') {
	    this.sexpstack.push([]);
	} else if (tok === ')') {
	    if (this.sexpstack.length === 1) {
		thestep = this.sexpstack.pop();
		this.state -= 1;
	    } else {
		var last = this.sexpstack.pop();
		this.sexpstack[this.sexpstack.length - 1].push(last);
	    }
	} else {
	    this.sexpstack[this.sexpstack.length - 1].push(tok);
	}
    } else if (state === 10) {
	return 'extra junk after proof';
    }
    state = this.state;
    if (state === 4) {
	// thestep has dv list
        this.fv = thestep;
	this.proofctx = new GH.ProofCtx();
	this.proofctx.varlist = [];
	this.proofctx.varmap = {};
    } else if (state === 6) {
        if (thestep.length & 1) {
	    return 'Odd length hypothesis list';
	}
	for (i = 0; i < thestep.length; i += 2) {
	    var hypname = thestep[i];
	    if (typeof hypname !== 'string') {
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
    } else if (state === 8 && this.concl === null) {
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
    } else if (thestep !== null && state === 8) {
	try {
	    this.vg.check_proof_step(this.hypmap, thestep, this.proofctx);
	} catch (e3) {
	    return "! " + e3;
	}
    } else if (state === 10) {
        pc = this.proofctx;
        if (pc.mandstack.length !== 0) {
	    return '\n\nExtra mand hyps on stack at end of proof';
	}
	if (pc.stack.length !== 1) {
	    return '\n\nStack must have one term at end of proof';
	}
	if (!GH.sexp_equals(pc.stack[0], this.concl)) {
	    return ('\n\nStack has:\n ' + GH.sexp_to_string(pc.stack[0]) +
		   '\nWanted:\n ' + GH.sexp_to_string(this.concl));
	}
    }
    return null;
};
