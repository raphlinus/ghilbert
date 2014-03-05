GH.operatorUtil = function(prover) {
	this.prover = prover;
};

// TODO: Delete this and use prover.getOperatorTypes.
GH.operatorUtil.getOperatorTypes = function(operator) {
	if (operator == '-.') 	return ['wff', 'wff'];
	if (operator == '->') 	return ['wff', 'wff', 'wff'];
	if (operator == '<->') 	return ['wff', 'wff', 'wff'];
	if (operator == '\\/') 	return ['wff', 'wff', 'wff'];
	if (operator == '/\\') 	return ['wff', 'wff', 'wff'];
	if (operator == 'A.') 	return ['bind', 'wff', 'wff'];
	// if (operator == 'E.') 	return ['bind', 'wff', 'wff'];
	if (operator == '=') 	return ['nat', 'nat', 'wff'];
	if (operator == 'n.=') 	return ['n.nat', 'n.nat', 'wff'];
	if (operator == 'n.<=') return ['n.nat', 'n.nat', 'wff'];
	if (operator == 'z.=') 	return ['z.nat', 'z.nat', 'wff'];
	if (operator == 'r.=') 	return ['r.nat', 'r.nat', 'wff'];
	if (operator == 'z.<=') return ['z.nat', 'z.nat', 'wff'];
	if (operator == 'q.=') 	return ['q.nat', 'q.nat', 'wff'];
	if (operator == 'q.<=') return ['q.nat', 'q.nat', 'wff'];
	if (operator == '=q') 	return ['rat', 'rat', 'wff'];
	if (operator == 'qpos') return ['rat', 'wff'];
	// if (operator == '=z') 	return ['rat', 'rat', 'wff'];
	if (operator == '<=') 	return ['nat', 'nat', 'wff'];
	if (operator == '<') 	return ['nat', 'nat', 'wff'];
	if (operator == '>=') 	return ['nat', 'nat', 'wff'];
	if (operator == '>') 	return ['nat', 'nat', 'wff'];
	if (operator == '|') 	return ['nat', 'nat', 'wff'];
	if (operator == 'prime') 	return ['nat', 'wff'];
	if (operator == 'S') 	return ['nat', 'nat'];
	if (operator == '+') 	return ['nat', 'nat', 'nat'];
	if (operator == '*') 	return ['nat', 'nat', 'nat'];
	if (operator == 'div') 	return ['nat', 'nat', 'nat'];
	if (operator == 'mod') 	return ['nat', 'nat', 'nat'];
	if (operator == 'exp') 	return ['nat', 'nat', 'nat'];
	if (operator == '=_') 	return ['set', 'set', 'wff'];
	if (operator == 'C_') 	return ['set', 'set', 'wff'];
	if (operator == 'C.') 	return ['set', 'set', 'wff'];
	if (operator == '{|}') 	return ['bind', 'wff', 'set'];
	if (operator == '[/]') 	return ['nat', 'bind', 'wff', 'wff'];
	if (operator == 'rwff') return ['bind', 'wff', 'wff'];
	if (operator == 'min') 	return ['set', 'nat'];
	if (operator == 'head') return ['nat', 'nat'];
	if (operator == 'tail') return ['nat', 'nat'];
	if (operator == 'e.') 	return ['nat', 'set', 'wff'];
	if (operator == '{}') 	return ['nat', 'set'];
	if (operator == 'u.') 	return ['set', 'set', 'set'];
	if (operator == 'i^i') 	return ['set', 'set', 'set'];
	if (operator == 'ifn') 	return ['wff', 'nat', 'nat', 'nat'];
	if (operator == 'iota') return ['set', 'nat'];
	if (operator == '{...}') return ['nat', 'nat', 'set'];
	if (operator == '!') return ['nat', 'nat'];
	if (operator == 'fibonacci') return ['nat', 'nat'];
	return null;
};

// Integers have a kind that is an ordinary natural number, but we need to
// use integer equality for them.
GH.operatorUtil.getSpecialOperatorTypes = function(operator) {
	if (operator == 'n.=') 	return ['n.nat', 'n.nat', 'wff'];
	if (operator == 'n.<=') return ['n.nat', 'n.nat', 'wff'];	
	if (operator == 'n.+') 	return ['n.nat', 'n.nat', 'n.nat'];
	if (operator == 'n.*') 	return ['n.nat', 'n.nat', 'n.nat'];
	if (operator == 'n.E.') return ['bind', 'n.nat', 'wff'];
	
	if (operator == 'z.=') 	return ['n.nat', 'z.nat', 'wff'];
	if (operator == 'z.<=') return ['n.nat', 'z.nat', 'wff'];	
	if (operator == 'z.+') 	return ['n.nat', 'z.nat', 'z.nat'];
	if (operator == 'z.*') 	return ['n.nat', 'z.nat', 'z.nat'];
	if (operator == 'z.E.') return ['bind', 'z.nat', 'wff'];
	
	if (operator == 'q.=') 	return ['q.nat', 'q.nat', 'wff'];
	if (operator == 'q.<=') return ['q.nat', 'q.nat', 'wff'];	
	if (operator == 'q.+') 	return ['q.nat', 'q.nat', 'q.nat'];
	if (operator == 'q.*') 	return ['q.nat', 'q.nat', 'q.nat'];
	if (operator == 'q.E.') return ['bind', 'z.nat', 'wff'];
	
	if (operator == 'r.=') 	return ['r.nat', 'r.nat', 'wff'];
	if (operator == 'r.<=') return ['r.nat', 'r.nat', 'wff'];	
	if (operator == 'r.+') 	return ['r.nat', 'r.nat', 'r.nat'];
	if (operator == 'r.-') 	return ['r.nat', 'r.nat', 'r.nat'];
	if (operator == 'r.-n') return ['r.nat', 'r.nat'];
	if (operator == 'r.*') 	return ['r.nat', 'r.nat', 'r.nat'];
	if (operator == 'r./') 	return ['r.nat', 'r.nat', 'r.nat'];
	if (operator == 'r.E.') return ['bind', 'r.nat', 'wff'];

	if (operator == '-') 	return ['nat', 'nat', 'nat'];
	if (operator == 'int') 	return ['nat', 'int'];
	if (operator == '=z') 	return ['int', 'int', 'wff'];
	if (operator == '<=z') 	return ['int', 'int', 'wff'];
	if (operator == '<z') 	return ['int', 'int', 'wff'];
	if (operator == '>=z') 	return ['int', 'int', 'wff'];
	if (operator == '>z') 	return ['int', 'int', 'wff'];
	if (operator == '+z') 	return ['int', 'int', 'int'];
	if (operator == '*z') 	return ['int', 'int', 'int'];
	// if (operator == '-n') 	return ['int', 'int'];
	if (operator == '-qn') 	return ['rat', 'rat'];
	if (operator == '=q') 	return ['rat', 'rat', 'wff'];
	if (operator == '<q') 	return ['rat', 'rat', 'wff'];
	if (operator == '<=q') 	return ['rat', 'rat', 'wff'];
	if (operator == '>q') 	return ['rat', 'rat', 'wff'];
	if (operator == '>=q') 	return ['rat', 'rat', 'wff'];
	if (operator == '*q') 	return ['rat', 'rat', 'rat'];
	if (operator == '+q') 	return ['rat', 'rat', 'rat'];
	if (operator == '-q') 	return ['rat', 'rat', 'rat'];
	// if (operator == '/') 	return ['rat', 'rat', 'rat'];
	if (operator == '</>') 	return ['int', 'int', 'rat'];
	if (operator == 'zpos') return ['int', 'wff'];
	if (operator == 'qpos') return ['rat', 'wff'];
	return null;
};

GH.operatorUtil.getType = function(sexp) {
	var operator = sexp.operator;
	var operatorTypes = GH.operatorUtil.getOperatorTypes(operator);
	return operatorTypes && operatorTypes[operatorTypes.length - 1];
};

GH.operatorUtil.getRootType = function(sexp) {
	var root = sexp;
	while(root.parent) {
		root = root.parent;
	}
	return GH.operatorUtil.getType(root);
};

GH.operatorUtil.getName = function(operator) {
	       if (operator == '-.') {		return 'Not';
	} else if (operator == '->') {		return 'Imp';		
	} else if (operator == '<->') {		return 'Bi';
	} else if (operator == '\\/') {		return 'Or';
	} else if (operator == '/\\') {		return 'An';
	} else if (operator == 'A.') {		return 'Al';
	} else if (operator == 'E.') {		return 'Ex';
	} else if (operator == 'n.E.') {		return 'Nex';
	} else if (operator == 'z.E.') {		return 'Zex';
	} else if (operator == '=') {		return 'Eq';
	} else if (operator == 'n.=') {		return 'Neq';
	} else if (operator == 'n.<=') {	return 'Nle';
	} else if (operator == 'z.=') {		return 'Zeq';
	} else if (operator == 'z.<=') {	return 'Zle';
	} else if (operator == 'q.=') {		return 'Qeq';
	} else if (operator == 'q.<=') {	return 'Qle';
	} else if (operator == '=z') {		return 'Zeq';
	} else if (operator == '=q') {		return 'Qeq';
	} else if (operator == 'r.=') {		return 'Req';
	} else if (operator == '=mod') {	return 'Modcon';
	} else if (operator == '<=z') {		return 'Zle';
	} else if (operator == '<z') {		return 'Zlt';
	} else if (operator == '>=z') {		return 'Zge';
	} else if (operator == '>z') {		return 'Zgt';
	} else if (operator == '<=q') {		return 'Qle';
	} else if (operator == '<q') {		return 'Qlt';
	} else if (operator == '>=q') {		return 'Qge';
	} else if (operator == '>q') {		return 'Qgt';
	} else if (operator == '<=') {		return 'Le';
	} else if (operator == '<') {		return 'Lt';
	} else if (operator == '>=') {		return 'Ge';
	} else if (operator == '>') {		return 'Gt';
	} else if (operator == '|') {		return 'Divs';
	} else if (operator == 'S') {		return 'Suc';
	} else if (operator == '+') {		return 'Add';
	} else if (operator == 'n.+') {		return 'Nadd';
	} else if (operator == 'n.*') {		return 'Nmul';
	} else if (operator == '+z') {		return 'Zadd';
	} else if (operator == '*z') {		return 'Zmul';
	} else if (operator == '+q') {		return 'Qadd';
	} else if (operator == '*q') {		return 'Qmul';
	} else if (operator == 'r.+') {		return 'Radd';
	} else if (operator == 'r.*') {		return 'Rmul';
	} else if (operator == 'r./') {		return 'Rdiv';
	} else if (operator == 'r.-') {		return 'Rsub';
	} else if (operator == 'r.-n') {	return 'Rneg';
	} else if (operator == '/') {		return 'Div';
	} else if (operator == '-n') {		return 'Neg';
	} else if (operator == '-qn') {		return 'Qneg';
	} else if (operator == '-') {		return 'Minus';
	} else if (operator == '-q') {		return 'Qminus';
	} else if (operator == '*') {		return 'Mul';
	} else if (operator == 'e.') {		return 'El';
	} else if (operator == '=_') {		return 'Seq';
	} else if (operator == 'C_') {		return 'Ss';
	} else if (operator == 'C.') {		return 'Pss';
	} else if (operator == '{|}') {		return 'Ab';
	} else if (operator == '{}') {		return 'Sn';
	} else if (operator == 'u.') {		return 'Un';
	} else if (operator == 'i^i') {		return 'In';
	} else if (operator == '{...}') {	return 'Intv';
	} else if (operator == '<,>') {	    return 'Op';
	} else if (operator == '<>') {	    return 'Tuple';
	} else if (operator == '_') {	    return 'Index';
	} else if (operator == '!') {	    return 'Fact';
	} else if (operator == 'nCr') {	    return 'Bin';
	} else if (operator == '.-') {	    return 'HM';
	} else if (operator == '<*>') {	    return 'TProd';
	} else if (operator == '<+>') {	    return 'TSum';
	} else if (operator == '<{}>') {	return 'TSet';
	} else if (operator == '{.|}') {	return 'Apset';
	} else if (operator == '</>') {	return 'Frac';
	} else {
		return operator.charAt(0).toUpperCase() + operator.slice(1);
	}
};

GH.operatorUtil.getThmName = function(operator, prefixed) {
	       if (operator == '-.') {		return 'not';
	} else if (operator == '->') {		return 'im';		
	} else if (operator == '<->') {		return 'bi';
	} else if (operator == '\\/') {		return 'or';
	} else if (operator == '/\\') {		return 'an';
	} else if (operator == 'A.') {		return 'al';
	} else if (operator == 'E.') {		return 'ex';
	} else if (operator == 'n.E.') {	if (prefixed) { return 'n.ex';} else { return 'ex';}
	} else if (operator == 'z.E.') {	if (prefixed) { return 'z.ex';} else { return 'ex';}
	} else if (operator == '=') {		return 'eq';
	} else if (operator == 'n.=') {		if (prefixed) { return 'n.eq';} else { return 'eq';}
	} else if (operator == 'n.<=') {	if (prefixed) { return 'n.le';} else { return 'le';}
	} else if (operator == 'z.=') {		if (prefixed) { return 'z.eq';} else { return 'eq';}
	} else if (operator == 'z.<=') {	if (prefixed) { return 'z.le';} else { return 'le';}
	} else if (operator == 'q.=') {		if (prefixed) { return 'q.eq';} else { return 'eq';}
	} else if (operator == 'q.<=') {	if (prefixed) { return 'q.le';} else { return 'le';}
	} else if (operator == 'r.=') {		if (prefixed) { return 'r.eq';} else { return 'eq';}
	} else if (operator == 'r.<=') {	if (prefixed) { return 'r.le';} else { return 'le';}
	} else if (operator == '=z') {		return 'zeq';
	} else if (operator == '=q') {		return 'eqq';
	} else if (operator == '=r') {		return 'req';
	} else if (operator == '=mod') {	return 'modcon';
	} else if (operator == '<=z') {		return 'zle';
	} else if (operator == '<z') {		return 'zlt';
	} else if (operator == '>=z') {		return 'zge';
	} else if (operator == '>z') {		return 'zgt';
	} else if (operator == '+z') {		return 'zadd';
	} else if (operator == '*z') {		return 'zmul';
	} else if (operator == '<=q') {		return 'qle';
	} else if (operator == '<q') {		return 'qlt';
	} else if (operator == '>=q') {		return 'qge';
	} else if (operator == '>q') {		return 'qgt';
	} else if (operator == '+q') {		return 'qadd';
	} else if (operator == '*q') {		return 'qmul';
	} else if (operator == '/') {		return 'div';
	} else if (operator == '<=') {		return 'le';
	} else if (operator == '<') {		return 'lt';
	} else if (operator == '>=') {		return 'ge';
	} else if (operator == '>') {		return 'gt';
	} else if (operator == '|') {		return 'divides';
	} else if (operator == 'S') {		return 'suc';
	} else if (operator == '+') {		return 'add';
	} else if (operator == 'n.+') {		if (prefixed) { return 'n.add';} else { return 'add';}
	} else if (operator == 'n.*') {		if (prefixed) { return 'n.mul';} else { return 'mul';}
	} else if (operator == 'z.+') {		if (prefixed) { return 'z.add';} else { return 'add';}
	} else if (operator == 'z.*') {		if (prefixed) { return 'z.mul';} else { return 'mul';}
	} else if (operator == 'q.+') {		if (prefixed) { return 'q.add';} else { return 'add';}
	} else if (operator == 'q.*') {		if (prefixed) { return 'q.mul';} else { return 'mul';}
	} else if (operator == 'r.+') {		if (prefixed) { return 'r.add';} else { return 'add';}
	} else if (operator == 'r.-') {		if (prefixed) { return 'r.minus';} else { return 'minus';}
	} else if (operator == 'r.-n') {	if (prefixed) { return 'r.neg';} else { return 'neg';}
	} else if (operator == 'r.*') {		if (prefixed) { return 'r.mul';} else { return 'mul';}
	} else if (operator == 'r./') {		if (prefixed) { return 'r.div';} else { return 'div';}
	} else if (operator == '-n') {		return 'neg';
	} else if (operator == '-qn') {		return 'qneg';
	} else if (operator == '-') {		return 'minus';
	} else if (operator == '-q') {		return 'qminus';
	} else if (operator == '*') {		return 'mul';
	} else if (operator == '.-') {		return 'halfminus';
	} else if (operator == 'e.') {		return 'el';
	} else if (operator == '=_') {		return 'seq';
	} else if (operator == 'C_') {		return 'Ss';
	} else if (operator == 'C.') {		return 'pss';
	} else if (operator == '{|}') {		return 'ab';
	} else if (operator == '[/]') {		return 'sbc';
	} else if (operator == '{}') {		return 'sn';
	} else if (operator == 'u.') {		return 'un';
	} else if (operator == 'i^i') {		return 'in';
	} else if (operator == 'ifn') {		return 'ifn';
	} else if (operator == '<,>') {	    return 'op';
	} else if (operator == '<>') {	    return 'tuple';
	} else if (operator == '_') {	    return 'index';
	} else if (operator == '!') {	    return 'factorial';
	} else if (operator == 'nCr') {	    return 'binomial';
	} else if (operator == '<*>') {	    return 'tupleproduct';
	} else if (operator == '<+>') {	    return 'tuplesum';
	} else if (operator == '<{}>') {	return 'tupleset';
	} else if (operator == '{.|}') {	return 'applyset';
	} else if (operator == '</>') {	return 'frac';
	} else {
		// Otherwise assume the operator is its name.
		return operator;
	}
};

// TODO: Check if this function is being used anywhere.
GH.operatorUtil.getlatex = function(operator) {
	       if (operator == '-.') {		return '¬';
	} else if (operator == '->') {		return '→';		
	} else if (operator == '<->') {		return '↔';
	} else if (operator == '\\/') {		return '∨';
	} else if (operator == '/\\') {		return '∧';
	} else if (operator == 'A.') {		return '∀';
	} else if (operator == 'E.') {		return '∃';
	} else if (operator == '=') {		return '=';
	} else if (operator == '<=') {		return '≤';
	} else if (operator == '<') {		return '<';
	} else if (operator == '.-') {		return '-';
	} else if (operator == 'e.') {		return '∈';
	} else if (operator == '=_') {		return '=';
	} else if (operator == 'C_') {		return '⊆';
	} else if (operator == 'C.') {		return '⊂';
	} else if (operator == 'u.') {		return '∪';
	} else if (operator == 'i^i') {		return '∩';
	} else if (operator == 'ifn') {		return 'ifn';
	} else {
		// Otherwise assume the operator is its name.
		return operator;
	}
};

GH.operatorUtil.EQUIVALENCE_OPERATORS = ['<->', '=', 'n.=', 'z.=', 'q.=', 'r.=', '=z', '=q', '=_'];

GH.operatorUtil.EQUIVALENCE_MAP = [
	[['wff'],         '<->'],
	[['nat', 'bind'],   '='],
	[['n.nat'],       'n.='],
	[['z.nat'],       'z.='],
	[['q.nat'],       'q.='],
	[['r.nat'],       'r.='],
	[['int'],          '=z'],
	[['rat'],          '=q'],
	[['set'],          '=_'],
	[['n.set'],        'n.=_'],
	[['z.set'],        'z.=_'],
	[['q.set'],        'q.=_']
];

GH.operatorUtil.getEquivalenceOperator = function(type) {
	var EquivalenceOp = GH.operatorUtil.EQUIVALENCE_MAP;
	for (var i = 0; i < EquivalenceOp.length; i++) {
		for (var j = 0; j < EquivalenceOp[i][0].length; j++) {
			if (EquivalenceOp[i][0][j] == type) {
				return EquivalenceOp[i][1];
			}
		}
	}
	alert('Equivalence operator for unknown type ' + type);
};

GH.operatorUtil.prototype.isReduced = function(sexp) {
	if (sexp.operands == 0) {
		return true;
	}
	var types = this.prover.getOperatorTypes(sexp.operator);
	var type = types[types.length - 1];
	if (!type) {
		return true;
	}
	if (type == 'nat') {
		return GH.numUtil.isReduced(sexp);
	} else if (type == 'set') {
		return GH.setUtil.isReduced(sexp);
	} else if (type == 'wff') {
		return sexp.isProven;
	}
};

// Creates an s-expression from an operator and several operands.
GH.operatorUtil.prototype.create = function(operator, operands) {
	var types = this.prover.getOperatorTypes(operator);
	if (operands.length != types.length - 1) {
		alert(operands.length + ' operands for a ' + operator + ' operation.');
	}
	var sexpOperands = [];
	for (var i = 0; i < operands.length; i++) {
		// Add the operands if it's already an s-expression, otherwise convert it.
		if (operands[i] instanceof GH.sExpression) {
			sexpOperands.push(operands[i].copy());
		} else if (typeof operands[i] == 'string') {
			sexpOperands.push(GH.sExpression.fromRaw(operands[i]));
		} else {
			sexpOperands.push(GH.operatorUtil.createType(types[i], operands[i]))
		}
	}
	return new GH.sExpression.createOperator(operator, sexpOperands);
};

// Create an expression with the given type and value.
GH.operatorUtil.createType = function(type, value) {
	if (type == 'nat') {
		return GH.numUtil.createNum(value);
	} else if (type == 'set') {
		return GH.setUtil.createSet(value);
	} else {
		alert('Creating type ' + type + ' is not supported.');
	}
};

// Reduce the s-expression to the given value.
GH.operatorUtil.reduce = function(sexp, value) {
	// Get the type of the s-expression.
	var types = GH.operatorUtil.getOperatorTypes(sexp.operator);
	return GH.operatorUtil.createType(types[types.length - 1], value);
};

// A guide for getting help with the notation. Appears below the proof and 
// provided links for more information on all of the symbols used in the
// proof.
GH.notationGuide = function(syms, context) {
	this.titleElements = [];
	this.bodyElements = [];
	this.isOpen = [false, false];
	this.steps = [];
	this.variables = {};
	this.operators = [];
	this.precomputed = false;
	this.syms = syms;
	this.context = context;
};

GH.notationGuide.prototype.render = function() {
	var guideContainer = document.createElement("div");
	stack.appendChild(guideContainer);
	for (var i = 0; i < 2; i++) {
		this.titleElements.push(document.createElement("span"));
		this.titleElements[i].setAttribute('class', 'notation-closed');
		this.titleElements[i].setAttribute('onclick', 'window.direct.notationGuide.toggle(' + i + ')');
		this.bodyElements.push(document.createElement("div"));
		this.bodyElements[i].setAttribute('class', 'notation-body');
		guideContainer.appendChild(this.titleElements[i]);
	}
	for (var i = 0; i < 2; i++) {
		guideContainer.appendChild(this.bodyElements[i]);
	}

	this.titleElements[0].innerHTML = 'Notation Help';
	this.titleElements[1].innerHTML = 'Context';
	this.bodyElements[1].innerHTML = this.context;
	this.close(1);
	if (this.context == '') {
		this.titleElements[1].setAttribute('style', 'display: none');
	}
};

GH.notationGuide.prototype.clear = function() {
	this.steps = [];
	this.variables = {};
	this.operators = [];
};

GH.notationGuide.prototype.addStep = function(step) {
	this.steps.push(step);
};

GH.notationGuide.prototype.addGuideElement = function(guide, symbol, useLatex) {
	var guideElement = document.createElement('span');
	guideElement.setAttribute('class', 'notation-guide');
	if (guide.hasOwnProperty('link')) {
		guideElement.innerHTML = symbol + ' <a href="/wiki/peano/' + guide.link + '">' + guide.name + '</a>';
	} else {
		guideElement.innerHTML = symbol + ' ' + '<span class="guide-no-link">' + guide.name + '</span>';
	}
	this.bodyElements[0].appendChild(guideElement);
	MathJax.Hub.Queue(["Typeset", MathJax.Hub, guideElement]);
};

GH.notationGuide.prototype.toggle = function(index) {
	this.isOpen[index] = !this.isOpen[index];
	this.close(1 - index);
	if (this.isOpen[index]) {
		this.titleElements[index].setAttribute('class', 'notation-open');
		this.bodyElements[index].setAttribute('style', '');
		if (!this.precomputed && (index == 0)) {
			this.precomputed = true;
			for (var i = 0; i < this.steps.length; i++) {
				this.addSymbolsFromStep(this.steps[i]);
			}
			for (var i = 0; i < GH.notationGuide.variableData.length; i++) {
				var variableData = GH.notationGuide.variableData[i];
				if (this.variables.hasOwnProperty(variableData.kind)) {
					var kindVars = this.variables[variableData.kind];
					for (var j = 0; j < kindVars.length; j++) {
						kindVars[j] = GH.typesetVariables(kindVars[j]);
					}
					var symbol = kindVars.join(',');
					this.addGuideElement(variableData, '\\(' + symbol + '\\)', true);
				}
			}
			for (var i = 0; i < GH.notationGuide.guideData.length; i++) {
				var guide = GH.notationGuide.guideData[i];
				var match = false;
				for (var j = 0; j < guide.symbols.length; j++) {
					if (this.operators.hasOwnProperty(guide.symbols[j])) {
						match = true;
					}
				}
				if (match) {
					var useLatex = guide.hasOwnProperty('latex');
					var symbol = useLatex ? guide.latex : guide.symbols[0];
					this.addGuideElement(guide, symbol, useLatex);
				}
			}
		}
	} else {
		this.close(index);
	}
};

GH.notationGuide.prototype.close = function(index) {
	this.isOpen[index] = false;
	this.titleElements[index].setAttribute('class', 'notation-closed');
	this.bodyElements[index].setAttribute('style', 'display: none');
};

GH.notationGuide.prototype.addSymbolsFromStep = function(step) {
	this.addSymbolsFromSexp(step.conclusion);
	for (var i = 0; i < step.hypotheses.length; i++) {
		this.addSymbolsFromStep(step.hypotheses[i]);
	}
};

GH.notationGuide.prototype.addSymbolsFromSexp = function(sexp) {
	var isString = (GH.typeOf(sexp) == 'string');
	if (isString) {
		var str = sexp.valueOf();
		if (!this.syms[str]) {
			return;
		}
		var kind = this.syms[str][1];
		if (!this.variables.hasOwnProperty(kind)) {
			this.variables[kind] = [str];
		} else {
			var i = 0;
			while (i < this.variables[kind].length && (this.variables[kind][i] < str)) {
				i++;
			}
			if (this.variables[kind][i] == str) {
				// String is already added to the variables
				return;
			}
			this.variables[kind].splice(i, 0, str);
		}
	} else {
		var str = sexp[0].valueOf();
		this.operators[str] = true;
		for (var i = 1; i < sexp.length; i++) {
			this.addSymbolsFromSexp(sexp[i]);
		}
	}
};

GH.notationGuide.variableData = [
  { kind: ['wff'], name: 'wffs', link: 'logic/wff' },
  { kind: ['nat'], name: 'numbers', link: 'arithmetic/numbers' },
  { kind: ['set'], name: 'sets', link: 'set' },
];

GH.notationGuide.guideData = [
	{ symbols: ['-.'],  latex: '\\( ¬ \\)', name: 'not', link: 'logic/not'},
	{ symbols: ['->'],  latex: '\\( → \\)', name: 'implies', link: 'logic/if'},
	{ symbols: ['<->'], latex: '\\( ↔ \\)', name: 'if and only if', link: 'logic/iff'},
	{ symbols: ['/\\'], latex: '\\( ∧ \\)', name: 'and', link: 'logic/and'},
	{ symbols: ['\\/'], latex: '\\( ∨ \\)', name: 'or', link: 'logic/or'},
	{ symbols: ['T'], latex: '\\( \\top \\)', name: 'true', link: 'logic/wff'},
	{ symbols: ['F'], latex: '\\( \\bot \\)', name: 'false', link: 'logic/wff'},
	
	{ symbols: ['A.'], latex: '\\( ∀ \\)', name: 'for all', link: 'predicate/all'},
	{ symbols: ['E.'], latex: '\\( ∃ \\)', name: 'there exists', link: 'predicate/exists'},
	{ symbols: ['E!'], latex: '\\( ∃! \\)', name: 'there exists one', link: 'predicate/unique'},
	{ symbols: ['E*'], latex: '\\( ∃* \\)', name: 'at most one', link: 'predicate/most-one'},
	{ symbols: ['[/]'], latex: '\\( [/] \\)', name: 'substitution', link: 'predicate/substitution'},
	{ symbols: ['rwff'], name: 'relatively well-formed formula'},
	
	{ symbols: ['='],   latex: '\\( = \\)', name: 'equals', link: 'arithmetic/equality'},
	{ symbols: ['n.='], latex: '\\( = \\)', name: 'natural number equality', link: 'arithmetic/equality'},
	{ symbols: ['=z'],  latex: '\\( = \\)', name: 'integer equals', link: 'arithmetic/equality'},
	{ symbols: ['=q'],  latex: '\\( = \\)', name: 'rational equals', link: 'arithmetic/equality'},
	{ symbols: ['<='],  latex: '\\( ≤ \\)', name: 'less than or equal to', link: 'arithmetic/less-than-equal'},
	{ symbols: ['<'],   latex: '\\( < \\)', name: 'less than', link: 'arithmetic/less-than'},
	{ symbols: ['>='],  latex: '\\( ≥ \\)', name: 'greater than or equal to', link: 'arithmetic/less-than-equal'},
	{ symbols: ['>'],   latex: '\\( > \\)', name: 'greater than', link: 'arithmetic/less-than'},
	{ symbols: ['<=z'], latex: '\\( ≤ \\)', name: 'integer less than or equal to', link: 'arithmetic/less-than-equal'},
	{ symbols: ['<z'],  latex: '\\( < \\)', name: 'integer less than', link: 'arithmetic/less-than'},
	{ symbols: ['>=z'], latex: '\\( ≥ \\)', name: 'integer greater than or equal to', link: 'arithmetic/less-than-equal'},
	{ symbols: ['>z'],  latex: '\\( > \\)', name: 'integer greater than', link: 'arithmetic/less-than'},
	{ symbols: ['<=q'], latex: '\\( ≤ \\)', name: 'rational less than or equal to', link: 'arithmetic/less-than-equal'},
	{ symbols: ['<q'],  latex: '\\( < \\)', name: 'rational less than', link: 'arithmetic/less-than'},
	{ symbols: ['>=q'], latex: '\\( ≥ \\)', name: 'rational greater than or equal to', link: 'arithmetic/less-than-equal'},
	{ symbols: ['>q'],  latex: '\\( > \\)', name: 'rational greater than', link: 'arithmetic/less-than'},
	{ symbols: ['=q'],  latex: '\\( = \\)', name: 'rational equals', link: 'arithmetic/equality'},
	
	{ symbols: ['S'],   latex: '\\( x\' \\)', name: 'successor', link: 'arithmetic/successor'},
	{ symbols: ['+'],   latex: '\\( + \\)', name: 'plus', link: 'arithmetic/add'},
	{ symbols: ['+z'],  latex: '\\( + \\)', name: 'integer plus', link: 'arithmetic/add'},
	{ symbols: ['+q'],  latex: '\\( + \\)', name: 'rational plus', link: 'arithmetic/add'},
	{ symbols: ['*'],   latex: '\\( \\cdot \\)', name: 'times', link: 'arithmetic/multiply'},
	{ symbols: ['*z'],  latex: '\\( \\cdot \\)', name: 'integer times', link: 'arithmetic/multiply'},
	{ symbols: ['*q'],  latex: '\\( \\cdot \\)', name: 'rational times', link: 'arithmetic/multiply'},
	{ symbols: ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '10'],             latex: '\\( 0-10 \\)', name: 'numbers', link: 'arithmetic/numbers'},
	{ symbols: ['0z', '1z', '2z', '3z', '4z', '5z', '6z', '7z', '8z', '9z', '10z'],  latex: '\\( 0-10 \\)', name: 'integers', link: 'arithmetic/numbers'},
	{ symbols: ['0q', '1q', '2q', '3q', '4q', '5q', '6q', '7q', '8q', '9q', '10q'],  latex: '\\( 0-10 \\)', name: 'rationals', link: 'arithmetic/numbers'},
	{ symbols: ['.1'],  latex: '\\( 0.1 \\)', name: 'decimal notation'},
	{ symbols: ['.-'],  latex: '\\( - \\)', name: 'half minus', link: 'arithmetic/half-minus'},
	{ symbols: ['-'],   latex: '\\( - \\)', name: 'minus', link: 'arithmetic/minus'},
	{ symbols: ['-q'],  latex: '\\( - \\)', name: 'rational minus', link: 'arithmetic/minus'},
	{ symbols: ['-n'],  latex: '\\( - \\)', name: 'negative sign', link: 'arithmetic/negative-sign'},
	{ symbols: ['-qn'], latex: '\\( - \\)', name: 'negative sign', link: 'arithmetic/negative-sign'},
	{ symbols: ['ifn'], latex: '\\( \\left\\{ \\begin{array}{l} x \\\\ y \\end{array} \\right. \\)', name: 'ternary conditional', link: 'arithmetic/ifn'},
	{ symbols: ['fibonacci'], latex: '\\( F_{x} \\)', name: 'Fibonacci number', link: 'arithmetic/fibonacci'},
	{ symbols: ['tri'],       latex: '\\( F_{x} \\)', name: 'triangular number', link: 'arithmetic/triangle'},

	{ symbols: ['int'], latex: 'int', name: 'natural to integer'},
	{ symbols: ['zn'], latex: 'zn', name: 'integer to natural'},
	{ symbols: ['zpos'], latex: 'positive', name: 'positive integer', link: 'arithmetic/positive'},
	{ symbols: ['zneg'], latex: 'negative', name: 'negative integer', link: 'arithmetic/negative'},
	{ symbols: ['qpos'], latex: 'positive', name: 'positive rational', link: 'arithmetic/positive'},
	{ symbols: ['qneg'], latex: 'negative', name: 'negative rational', link: 'arithmetic/negative'},
	
	{ symbols: ['NaN'], latex: 'NaN', name: 'not a number', link: 'arithmetic/rationals/NaN'},
	{ symbols: ['rationals'], latex: 'rationals', name: 'set of rationals', link: 'arithmetic/rationals/rationals-set'},
	{ symbols: ['top'],    latex: '\\( x_{t} \\)', name: 'top (numerator)', link: 'arithmetic/rationals/top'},
	{ symbols: ['bottom'], latex: '\\( x_{b} \\)', name: 'bottom (denominator)', link: 'arithmetic/rationals/bottom'},
	{ symbols: ['</>'],    latex: '\\( \\frac{a} {b} \\)', name: 'fraction', link: 'arithmetic/rationals/fraction'},
	{ symbols: ['/'],      latex: '\\( \\frac{a} {b} \\)', name: 'division', link: 'arithmetic/divide'},
	
	{ symbols: ['e.'],   latex: '\\( ∈ \\)',  name: 'element of', link: 'set/element-of'},
	{ symbols: ['{|}'],  latex: '\\( \\{|\\} \\)', name: 'set abstraction', link: 'set/abstraction'},
	{ symbols: ['{/}'],  latex: '\\( \\emptyset \\)', name: 'empty set', link: 'set/empty-set'},
	{ symbols: ['iota'],  name: 'iota', link: 'set/iota'},
	{ symbols: ['=_'],  latex: '\\( = \\)', name: 'set equality', link: 'set/equality'},
	{ symbols: ['C_'],  latex: '\\( ⊆ \\)', name: 'subset', link: 'set/subset'},
	{ symbols: ['C.'],  latex: '\\( ⊂ \\)', name: 'proper subset', link: 'set/proper-subset'},
	{ symbols: ['u.'],  latex: '\\( ∪ \\)', name: 'union', link: 'set/union', link: 'set/union'},
	{ symbols: ['i^i'], latex: '\\( ∩ \\)', name: 'intersection', link: 'set/intersection', link: 'set/intersection'},
	{ symbols: ['min'], name: 'set minimum', link: 'set/minimum'},
	{ symbols: ['{...}'], latex: '\\( \\{a \\ldots b} \\)', name: 'set interval', link: 'tuple/interval'},
	
	{ symbols: ['<,>'], latex: '\\( (x, y) \\)', name: 'ordered pair', link: 'tuple/ordered-pair'},
	{ symbols: ['head'], latex: '\\( x_{h} \\)', name: 'head', link: 'tuple/head'},
	{ symbols: ['tail'], latex: '\\( x_{t} \\)', name: 'tail', link: 'tuple/tail'},
	{ symbols: ['<+>'],  latex: '\\(    x_1    +   x_2 + \\cdots + x_N \\)',    name: 'sum a finite sequence', link: 'tuple/add'},
	{ symbols: ['<*>'],  latex: '\\(    x_1 \\cdot x_2   \\cdots   x_N \\)',    name: 'multiply a finite sequence', link: 'tuple/multiply'},
	{ symbols: ['<{}>'], latex: '\\( \\{x_1    ,   x_2 , \\ldots , x_N \\}\\)', name: 'a finite set', link: 'tuple/set'},
	// { symbols: ['length'], name: 'tuple length'}, // The length of the javascript array interferes with this.
	{ symbols: ['_'], latex: 'x_y', name: 'tuple index', link: 'tuple/index'},
	{ symbols: ['push'], name: 'push onto tuple stack'},
	{ symbols: ['pop'], name: 'pop off of tuple stack'},
	{ symbols: ['<>'], latex: '(a, b, c)', name: 'tuple', link: 'tuple/tuple'},

	{ symbols: ['|'],  name: 'divides', link: 'number-theory/divides'},
	{ symbols: ['even'],  name: 'even number', link: 'number-theory/even'},
	{ symbols: ['odd'],  name: 'odd number', link: 'number-theory/odd'},
	{ symbols: ['prime'],  name: 'prime', link: 'number-theory/prime'},
	{ symbols: ['primeset'], latex: 'Primes', name: 'the set of primes', link: 'number-theory/prime'},
	{ symbols: ['fun'], name: 'is a function', link: 'function/fun'},
	{ symbols: ['lincom'], name: 'linear combination'},
	{ symbols: ['gcd'], name: 'greatest common denominator'},
	{ symbols: ['mod'], name: 'modulo', link: 'arithmetic/mod'},
	{ symbols: ['=mod'], latex: '\\( \\equiv_A \\)', name: 'congruent modulo A', link: 'arithmetic/modcon'},
	{ symbols: ['div'], latex: '÷', name: 'whole number division', link: 'arithmetic/div'},
	{ symbols: ['beta'], name: 'Godel\'s beta function'},
	{ symbols: ['relprim'], name: 'relatively prime'},
	{ symbols: ['lambda'], latex: '\\( ↦ \\)', name: 'lambda function', link: 'function/lambda'},
	{ symbols: ['apply'], latex: '\\( S(x) \\)', name: 'function application', link: 'function/apply'},
	{ symbols: ['recursep'], name: 'recursive predicate'},
	{ symbols: ['recurse'], latex: '\\( S^a(x) \\)', name: 'recursive function', link: 'function/recurse'},
	{ symbols: ['sum-step'], name: 'summation construction step', link: 'arithmetic/sum'},
	{ symbols: ['sum'], latex: '\\( \\sum \\)', name: 'summation'},
	{ symbols: ['{.|}'], latex: '\\(\\{S(x)|φ\\} \\)', name: 'apply function to a set'},
	{ symbols: ['product-step'], name: 'product construction step'},
	{ symbols: ['product'], latex: '\\( \\prod \\)', name: 'product', link: 'arithmetic/product'},
	{ symbols: ['!'], name: 'factorial', link: 'arithmetic/factorial'},
	{ symbols: ['nCr'], latex: '\\( \\binom{x}{y} \\)', name: 'binomial coefficient'},
	{ symbols: ['exp'], latex: '\\( x^y \\)', name: 'exponent', link: 'arithmetic/exponent'},

	{ symbols: ['sqrt'], latex: '\\(\\sqrt{x}\\)', name: 'square root'},
	{ symbols: ['abs'], latex: '\\(|x|\\)', name: 'absolute value'},
	{ symbols: ['upperbound'], name: 'upper bound'},
	{ symbols: ['supremum'], name: 'supremum'},
	{ symbols: ['sup'], name: 'supremum'},
];