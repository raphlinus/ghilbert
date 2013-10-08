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
	} else if (operator == '<=') {		return 'Le';
	} else if (operator == '<') {		return 'Lt';
	} else if (operator == '|') {		return 'Divs';
	} else if (operator == 'S') {		return 'Suc';
	} else if (operator == '+') {		return 'Add';
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
	} else if (operator == '.-') {	    return 'HM';
	} else if (operator == '<*>') {	    return 'TProd';
	} else if (operator == '<+>') {	    return 'TSum';
	} else if (operator == '<{}>') {	return 'TSet';
	} else if (operator == '{.|}') {	return 'Apset';
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
	} else if (operator == '<=') {		return 'le';
	} else if (operator == '<') {		return 'lt';
	} else if (operator == '|') {		return 'divides';
	} else if (operator == 'S') {		return 'suc';
	} else if (operator == '+') {		return 'add';
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
	} else if (operator == '<*>') {	    return 'tupleproduct';
	} else if (operator == '<+>') {	    return 'tuplesum';
	} else if (operator == '<{}>') {	return 'tupleset';
	} else if (operator == '{.|}') {	return 'applyset';
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

GH.operatorUtil.getEquivalenceOperator = function(type) {
	if ((type == 'nat') || (type == 'bind')) {
		return '=';
	} else if (type == 'wff') {
		return '<->';
	} else if (type == 'set') {
		return '=_';
	} else {
		alert('Equivalence operator for unknown type ' + type);
	}
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