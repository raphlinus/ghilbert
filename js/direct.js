// <license>
// This module implements a direct mode, in which changes to the editor
// window are reflected immediately into a stack view.

// text is a CanvasEdit object, stack is a canvas for drawing the stack view
GH.Direct = function(text, stack) {
    var self = this;
    this.text = text;
    this.text.imtrans = {};  // todo: hack
    this.stack = new GH.CanvasEdit(stack);
    this.stack.cursorvisible = false;
    text.listeners.push(function() { self.update(); });
};

GH.splitrange = function(str) {
    var result = [];
    var beg = 0;
    for (var i = 0; i < str.length; i++) {
	c = str.charAt(i);
	if (c == ' ') {
	    if (i != beg) {
		result.push({tok: str.substring(beg, i), beg: beg, end: i});
	    }
	    beg = i + 1;
	} else if (c == '(' || c == ')') {
	    if (i != beg) {
		result.push({tok: str.substring(beg, i), beg: beg, end: i});
	    }
	    result.push({tok: str.substring(i, i+1), beg: i, end: i+1});
	    beg = i + 1;
	} else if (c == '#') {
	    if (i != beg) {
		result.push({tok: str.substring(beg, i), beg: beg, end: i});
	    }
	    beg = str.length;
	    break;
	}
    }
    if (beg != str.length) {
	result.push({tok: str.substring(beg), beg: beg, end: str.length});
    }
    return result;
};

GH.Direct.prototype.update = function() {
    this.stack.text = [];
    thmctx = new GH.DirectThm(this.vg);
    var status = null;
    for (var i = 0; i < this.text.text.length && status == null; i++) {
	var spl = GH.splitrange(this.text.text[i]);
	for (var j = 0; j < spl.length; j++) {
	    status = thmctx.tok(spl[j].tok);
	    if (status) {
		var loc = spl[j].tok + ' ' + spl[j].beg + ':' + spl[j].end;
		break;
	    }
	}
    }
    //this.stack.text.push('state: ' + thmctx.state);
    //this.stack.text.push('ss: ' + GH.sexp_to_string(thmctx.sexpstack));
    //if (thmctx.stmt != null) {
        //this.stack.text.push('stmt: ' + GH.sexp_to_string(thmctx.stmt));
    //}
    if (thmctx.proofctx) {
	var pstack = thmctx.proofctx.stack;
	for (var i = 0; i < pstack.length; i++) {
	    this.stack.text.push(GH.sexptounicode(pstack[i]));
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
};

GH.DirectThm.prototype.tok = function(tok) {
    var state = this.state;
    var thestep = null;
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
	var fvvarmap = {};
	// todo: nyi
	this.proofctx = new GH.ProofCtx(fvvarmap);
    } else if (state == 6) {
	for (var i = 0; i < thestep.length; i += 2) {
	    this.hypmap[thestep[i]] = thestep[i + 1];
	}
    } else if (state == 8 && this.stmt == null) {
	this.stmt = thestep || 'null';
    } else if (thestep != null && state == 8) {
	try {
	    this.vg.check_proof_step(this.hypmap, thestep, this.proofctx);
	} catch (e) {
	    return e;
	}
    }
};