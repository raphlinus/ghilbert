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
	if (operator == 'E.') 	return ['bind', 'wff', 'wff'];
	if (operator == '=') 	return ['nat', 'nat', 'wff'];
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
	if (operator == 'int') 	return ['nat', 'int'];
	if (operator == '=z') 	return ['int', 'int', 'wff'];
	if (operator == '<=z') 	return ['int', 'int', 'wff'];
	if (operator == '<z') 	return ['int', 'int', 'wff'];
	if (operator == '>=z') 	return ['int', 'int', 'wff'];
	if (operator == '>z') 	return ['int', 'int', 'wff'];
	if (operator == '+z') 	return ['int', 'int', 'int'];
	if (operator == '-') 	return ['int', 'int', 'int'];
	if (operator == '*z') 	return ['int', 'int', 'int'];
	if (operator == '-n') 	return ['int', 'int'];
	if (operator == '-qn') 	return ['rat', 'rat'];
	if (operator == '=q') 	return ['rat', 'rat', 'wff'];
	if (operator == '<q') 	return ['rat', 'rat', 'wff'];
	if (operator == '<=q') 	return ['rat', 'rat', 'wff'];
	if (operator == '>q') 	return ['rat', 'rat', 'wff'];
	if (operator == '>=q') 	return ['rat', 'rat', 'wff'];
	if (operator == '*q') 	return ['rat', 'rat', 'rat'];
	if (operator == '+q') 	return ['rat', 'rat', 'rat'];
	if (operator == '-q') 	return ['rat', 'rat', 'rat'];
	if (operator == '/') 	return ['rat', 'rat', 'rat'];
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
	} else if (operator == '=') {		return 'Eq';
	} else if (operator == '=z') {		return 'Zeq';
	} else if (operator == '=q') {		return 'Qeq';
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
	} else if (operator == '+z') {		return 'Zadd';
	} else if (operator == '*z') {		return 'Zmul';
	} else if (operator == '+q') {		return 'Qadd';
	} else if (operator == '*q') {		return 'Qmul';
	} else if (operator == '/') {		return 'Qdiv';
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

GH.operatorUtil.getThmName = function(operator) {
	       if (operator == '-.') {		return 'not';
	} else if (operator == '->') {		return 'im';		
	} else if (operator == '<->') {		return 'bi';
	} else if (operator == '\\/') {		return 'or';
	} else if (operator == '/\\') {		return 'an';
	} else if (operator == 'A.') {		return 'al';
	} else if (operator == 'E.') {		return 'ex';
	} else if (operator == '=') {		return 'eq';
	} else if (operator == '=z') {		return 'zeq';
	} else if (operator == '=q') {		return 'eqq';
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
	} else if (operator == '/') {		return 'qdiv';
	} else if (operator == '<=') {		return 'le';
	} else if (operator == '<') {		return 'lt';
	} else if (operator == '>=') {		return 'ge';
	} else if (operator == '>') {		return 'gt';
	} else if (operator == '|') {		return 'divides';
	} else if (operator == 'S') {		return 'suc';
	} else if (operator == '+') {		return 'add';
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

GH.operatorUtil.getUnicode = function(operator) {
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

GH.operatorUtil.EQUIVALENCE_OPERATORS = ['<->', '=', '=z', '=q', '=_'];

GH.operatorUtil.EQUIVALENCE_MAP = [
	[['wff'],         '<->'],
	[['nat', 'bind'], '='],
	[['int'],         '=z'],
	[['rat'],         '=q'],
	[['set'],         '=_']
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
GH.notationGuide = function(syms) {
	this.titleElement = null;
	this.bodyElement = null;
	this.isOpen = false;
	this.steps = [];
	this.variables = {};
	this.operators = [];
	this.precomputed = false;
	this.syms = syms;
};

GH.notationGuide.prototype.render = function() {
	var guideContainer = document.createElement("div");
	this.titleElement = document.createElement("div");
	this.titleElement.setAttribute('class', 'notation-closed');
	this.titleElement.setAttribute('onclick', 'window.direct.notationGuide.toggle()');
	this.titleElement.innerHTML = 'Notation Help';

	this.bodyElement = document.createElement("div");
	this.bodyElement.setAttribute('class', 'notation-body');

	stack.appendChild(guideContainer);
	guideContainer.appendChild(this.titleElement);
	guideContainer.appendChild(this.bodyElement);
};

GH.notationGuide.prototype.clear = function() {
	this.steps = [];
	this.variables = {};
	this.operators = [];
};

GH.notationGuide.prototype.addStep = function(step) {
	this.steps.push(step);
};

GH.notationGuide.prototype.addGuideElement = function(guide, symbol) {
	var guideElement = document.createElement('span');
	guideElement.setAttribute('class', 'notation-guide');
	if (guide.hasOwnProperty('link')) {
		guideElement.innerHTML = symbol + ' <a href="/wiki/peano/' + guide.link + '">' + guide.name + '</a>';
	} else {
		guideElement.innerHTML = symbol + ' ' + '<span class="guide-no-link">' + guide.name + '</span>';
	}
	this.bodyElement.appendChild(guideElement);
};

GH.notationGuide.prototype.toggle = function() {
	this.isOpen = !this.isOpen;
	if (this.isOpen) {
		this.titleElement.setAttribute('class', 'notation-open');
		this.bodyElement.setAttribute('style', '');
		if (!this.precomputed) {
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
					this.addGuideElement(variableData, symbol);
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
					var symbol = guide.hasOwnProperty('unicode') ? guide.unicode : guide.symbols[0];
					this.addGuideElement(guide, symbol);
				}
			}
		}
	} else {
		this.titleElement.setAttribute('class', 'notation-closed');
		this.bodyElement.setAttribute('style', 'display: none');
	}
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
	{ symbols: ['-.'], unicode: '¬', name: 'not', link: 'logic/not'},
	{ symbols: ['->'], unicode: '→', name: 'if', link: 'logic/if'},
	{ symbols: ['<->'], unicode: '↔', name: 'if and only if', link: 'logic/iff'},
	{ symbols: ['/\\'], unicode: '∧', name: 'and', link: 'logic/and'},
	{ symbols: ['\\/'], unicode: '∨', name: 'and', link: 'logic/or'},
	{ symbols: ['T'], unicode: 'T', name: 'true', link: 'logic/wff'},
	{ symbols: ['F'], unicode: 'F', name: 'false', link: 'logic/wff'},
	
	{ symbols: ['A.'], unicode: '∀', name: 'for all', link: 'predicate/all'},
	{ symbols: ['E.'], unicode: '∃', name: 'there exists', link: 'predicate/exists'},
	{ symbols: ['E!'], unicode: '∃!', name: 'there exists one', link: 'predicate/unique'},
	{ symbols: ['E*'], unicode: '∃*', name: 'at most one', link: 'predicate/most-one'},
	{ symbols: ['[/]'], unicode: '[/]', name: 'substitution', link: 'predicate/substitution'},
	{ symbols: ['rwff'], name: 'relatively well-formed formula'},
	
	{ symbols: ['='],  unicode: '=', name: 'equals', link: 'arithmetic/equality'},
	{ symbols: ['=z'],  unicode: '=', name: 'integer equals', link: 'arithmetic/equality'},
	{ symbols: ['=q'],  unicode: '=', name: 'rational equals', link: 'arithmetic/equality'},
	{ symbols: ['<='], unicode: '≤', name: 'less than or equal to', link: 'arithmetic/less-than-equal'},
	{ symbols: ['<'],  unicode: '<', name: 'less than', link: 'arithmetic/less-than'},
	{ symbols: ['>='], unicode: '≥', name: 'greater than or equal to', link: 'arithmetic/less-than-equal'},
	{ symbols: ['>'],  unicode: '>', name: 'greater than', link: 'arithmetic/less-than'},
	{ symbols: ['<=z'], unicode: '≤', name: 'integer less than or equal to', link: 'arithmetic/less-than-equal'},
	{ symbols: ['<z'],  unicode: '<', name: 'integer less than', link: 'arithmetic/less-than'},
	{ symbols: ['>=z'], unicode: '≥', name: 'integer greater than or equal to', link: 'arithmetic/less-than-equal'},
	{ symbols: ['>z'],  unicode: '>', name: 'integer greater than', link: 'arithmetic/less-than'},
	{ symbols: ['<=q'], unicode: '≤', name: 'rational less than or equal to', link: 'arithmetic/less-than-equal'},
	{ symbols: ['<q'],  unicode: '<', name: 'rational less than', link: 'arithmetic/less-than'},
	{ symbols: ['>=q'], unicode: '≥', name: 'rational greater than or equal to', link: 'arithmetic/less-than-equal'},
	{ symbols: ['>q'],  unicode: '>', name: 'rational greater than', link: 'arithmetic/less-than'},
	{ symbols: ['=q'],  unicode: '=', name: 'rational equals', link: 'arithmetic/equality'},
	
	{ symbols: ['S'],  unicode: 'x\'', name: 'successor', link: 'arithmetic/successor'},
	{ symbols: ['+'],  unicode: '+', name: 'plus', link: 'arithmetic/add'},
	{ symbols: ['+z'],  unicode: '+', name: 'integer plus', link: 'arithmetic/add'},
	{ symbols: ['+q'],  unicode: '+', name: 'rational plus', link: 'arithmetic/add'},
	{ symbols: ['*'],  unicode: '∙', name: 'times', link: 'arithmetic/multiply'},
	{ symbols: ['*z'],  unicode: '∙', name: 'integer times', link: 'arithmetic/multiply'},
	{ symbols: ['*q'],  unicode: '∙', name: 'rational times', link: 'arithmetic/multiply'},
	{ symbols: ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '10'],  unicode: '0-10', name: 'numbers', link: 'arithmetic/numbers'},
	{ symbols: ['0z', '1z', '2z', '3z', '4z', '5z', '6z', '7z', '8z', '9z', '10z'],  unicode: '0-10', name: 'integers', link: 'arithmetic/numbers'},
	{ symbols: ['0q', '1q', '2q', '3q', '4q', '5q', '6q', '7q', '8q', '9q', '10q'],  unicode: '0-10', name: 'rationals', link: 'arithmetic/numbers'},
	{ symbols: ['.1'],  unicode: '0.1', name: 'decimal notation'},
	{ symbols: ['.-'],  unicode: '-', name: 'half minus', link: 'arithmetic/half-minus'},
	{ symbols: ['-'],  unicode: '-', name: 'minus', link: 'arithmetic/minus'},
	{ symbols: ['-q'],  unicode: '-', name: 'rational minus', link: 'arithmetic/minus'},
	{ symbols: ['-n'],  unicode: '-', name: 'negative sign', link: 'arithmetic/negative-sign'},
	{ symbols: ['-qn'],  unicode: '-', name: 'negative sign', link: 'arithmetic/negative-sign'},
	{ symbols: ['ifn'], name: 'ternary conditional', link: 'arithmetic/ifn'},
	{ symbols: ['fibonacci'], unicode: 'F<sub>A</sub>', name: 'Fibonacci number', link: 'arithmetic/fibonacci'},
	{ symbols: ['tri'], unicode: 'T<sub>A</sub>', name: 'triangular number', link: 'arithmetic/triangle'},

	{ symbols: ['int'], unicode: 'int', name: 'natural to integer'},
	{ symbols: ['zn'], unicode: 'zn', name: 'integer to natural'},
	{ symbols: ['zpos'], unicode: 'positive', name: 'positive integer', link: 'arithmetic/positive'},
	{ symbols: ['zneg'], unicode: 'negative', name: 'negative integer', link: 'arithmetic/negative'},
	{ symbols: ['qpos'], unicode: 'positive', name: 'positive rational', link: 'arithmetic/positive'},
	{ symbols: ['qneg'], unicode: 'negative', name: 'negative rational', link: 'arithmetic/negative'},
	
	{ symbols: ['NaN'], unicode: 'NaN', name: 'not a number', link: 'arithmetic/rationals/NaN'},
	{ symbols: ['rationals'], unicode: 'rationals', name: 'set of rationals', link: 'arithmetic/rationals/rationals-set'},
	{ symbols: ['top'], unicode: 'A<sub>t</sub>', name: 'top (numerator)', link: 'arithmetic/rationals/top'},
	{ symbols: ['bottom'], unicode: 'A<sub>b</sub>', name: 'bottom (denominator)', link: 'arithmetic/rationals/bottom'},
	{ symbols: ['</>'], unicode: 'A / B', name: 'fraction', link: 'arithmetic/rationals/fraction'},
	{ symbols: ['/'], unicode: 'A / B', name: 'division', link: 'arithmetic/divide'},
	
	{ symbols: ['e.'],  unicode: '∈', name: 'element of', link: 'set/element-of'},
	{ symbols: ['{|}'],  unicode: '{|}', name: 'set abstraction', link: 'set/abstraction'},
	{ symbols: ['{/}'],  unicode: '∅', name: 'empty set', link: 'set/empty-set'},
	{ symbols: ['iota'],  name: 'iota', link: 'set/iota'},
	{ symbols: ['=_'],  unicode: '=', name: 'set equality', link: 'set/equality'},
	{ symbols: ['C_'],  unicode: '⊆', name: 'subset', link: 'set/subset'},
	{ symbols: ['C.'],  unicode: '⊂', name: 'proper subset', link: 'set/proper-subset'},
	{ symbols: ['u.'],  unicode: '∪', name: 'union', link: 'set/union', link: 'set/union'},
	{ symbols: ['i^i'], unicode: '∩', name: 'intersection', link: 'set/intersection', link: 'set/intersection'},
	{ symbols: ['min'], name: 'set minimum', link: 'set/minimum'},
	{ symbols: ['{...}'], unicode: '{A...B}', name: 'set interval', link: 'tuple/interval'},
	
	{ symbols: ['<,>'], unicode: '(A, B)', name: 'ordered pair', link: 'tuple/ordered-pair'},
	{ symbols: ['head'], unicode: 'A<sub>h</sub>', name: 'head', link: 'tuple/head'},
	{ symbols: ['tail'], unicode: 'A<sub>t</sub>', name: 'tail', link: 'tuple/tail'},
	{ symbols: ['<+>'], unicode: 'A<sub>1</sub>+A<sub>2</sub>+...+A<sub>N</sub>', name: 'sum a finite sequence', link: 'tuple/add'},
	{ symbols: ['<*>'], unicode: 'A<sub>1</sub>∙A<sub>2</sub>∙∙∙A<sub>N</sub>', name: 'multiply a finite sequence', link: 'tuple/multiply'},
	{ symbols: ['<{}>'], unicode: '{A<sub>1</sub>, A<sub>2</sub>,...,A<sub>N</sub>}', name: 'a finite set', link: 'tuple/set'},
	// { symbols: ['length'], name: 'tuple length'}, // The length of the javascript array interferes with this.
	{ symbols: ['_'], unicode: 'A <sub> B </sub>', name: 'tuple index', link: 'tuple/index'},
	{ symbols: ['push'], name: 'push onto tuple stack'},
	{ symbols: ['pop'], name: 'pop off of tuple stack'},
	{ symbols: ['<>'], unicode: '(A, B, C)', name: 'tuple', link: 'tuple/tuple'},

	{ symbols: ['|'],  name: 'divides', link: 'number-theory/divides'},
	{ symbols: ['even'],  name: 'even number', link: 'number-theory/even'},
	{ symbols: ['odd'],  name: 'odd number', link: 'number-theory/odd'},
	{ symbols: ['prime'],  name: 'prime', link: 'number-theory/prime'},
	{ symbols: ['primeset'], unicode: 'Primes', name: 'the set of primes', link: 'number-theory/prime'},
	{ symbols: ['sqrt'], name: 'square root'},
	{ symbols: ['fun'], name: 'is a function', link: 'function/fun'},
	{ symbols: ['lincom'], name: 'linear combination'},
	{ symbols: ['gcd'], name: 'greatest common denominator'},
	{ symbols: ['mod'], name: 'modulo', link: 'arithmetic/mod'},
	{ symbols: ['=mod'], unicode: '≡<sub>A</sub>', name: 'congruent modulo A', link: 'arithmetic/modcon'},
	{ symbols: ['div'], unicode: '÷', name: 'whole number division', link: 'arithmetic/div'},
	{ symbols: ['beta'], name: 'Godel\'s beta function'},
	{ symbols: ['relprim'], name: 'relatively prime'},
	{ symbols: ['lambda'], unicode: '↦', name: 'lambda function', link: 'function/lambda'},
	{ symbols: ['apply'], unicode: 'S(A)', name: 'function application', link: 'function/apply'},
	{ symbols: ['recursep'], name: 'recursive predicate'},
	{ symbols: ['recurse'], unicode: 'S<sup> A </sup>(B)', name: 'recursive function', link: 'function/recurse'},
	{ symbols: ['sum-step'], name: 'summation construction step', link: 'arithmetic/sum'},
	{ symbols: ['sum'], unicode: 'Σ', name: 'summation'},
	{ symbols: ['{.|}'], unicode: '{S(x)|φ}', name: 'apply function to a set'},
	{ symbols: ['product-step'], name: 'product construction step'},
	{ symbols: ['product'], unicode: 'Π', name: 'product', link: 'arithmetic/product'},
	{ symbols: ['!'], name: 'factorial', link: 'arithmetic/factorial'},
	{ symbols: ['nCr'], unicode: '<sup> A </sup> <sub> B </sub>', name: 'binomial coefficient'},
	{ symbols: ['exp'], unicode: 'A <sup> B </sup>', name: 'exponent', link: 'arithmetic/exponent'},
];