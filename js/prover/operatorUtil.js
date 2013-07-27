GH.operatorUtil = {};

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
	if (operator == '|') 	return ['nat', 'nat', 'wff'];
	if (operator == 'prime') 	return ['nat', 'wff'];
	if (operator == 'S') 	return ['nat', 'nat'];
	if (operator == '+') 	return ['nat', 'nat', 'nat'];
	if (operator == '*') 	return ['nat', 'nat', 'nat'];
	if (operator == '=_') 	return ['set', 'set', 'wff'];
	if (operator == '{|}') 	return ['bind', 'wff', 'set'];
	if (operator == 'e.') 	return ['nat', 'set', 'wff'];
	if (operator == '{}') 	return ['nat', 'set'];
	if (operator == 'u.') 	return ['set', 'set', 'set'];
	if (operator == 'i^i') 	return ['set', 'set', 'set'];
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
	} else if (operator == 'prime') {	return 'Prim';
	} else if (operator == 'S') {		return 'Suc';
	} else if (operator == '+') {		return 'Add';
	} else if (operator == '*') {		return 'Mul';
	} else if (operator == 'e.') {		return 'El';
	} else if (operator == '=_') {		return 'Seq';
	} else if (operator == '{|}') {		return 'Ab';
	} else if (operator == '{}') {		return 'Sn';
	} else if (operator == 'u.') {		return 'Un';
	} else if (operator == 'i^i') {		return 'In';
	} else {
		alert('Operator ' + operator + ' is not named.');
		return '';
	}
};

GH.operatorUtil.isReduced = function(sexp) {
	var type = GH.operatorUtil.getType(sexp);
	if (!type) {
		return true;
	}
	if (type == 'nat') {
		return GH.numUtil.isReduced(sexp);
	} else if (type == 'set') {
		return GH.setUtil.isReduced(sexp);
	}
};

// Creates an s-expression from an operator and several operands.
GH.operatorUtil.create = function(operator, operands) {
	var types = GH.operatorUtil.getOperatorTypes(operator);
	if (operands.length != types.length - 1) {
		alert(operands.length + ' operands for a ' + operator + ' operation.');
	}
	var sexpOperands = [];
	for (var i = 0; i < operands.length; i++) {
		// Add the operands if it's already an s-expression, otherwise convert it.
		if (operands[i] instanceof GH.sExpression) {
			sexpOperands.push(operands[i].copy());
		} else {
			if (types[i] == 'nat') {
				sexpOperands.push(GH.numUtil.createNum(operands[i]));
			} else if (types[i] == 'set') {
				sexpOperands.push(GH.setUtil.createSet(operands[i]));
			} else {
				alert('Creating type ' + types[i] + ' is not supported.');
			}
		}
	}
	return new GH.sExpression.createOperator(operator, sexpOperands);
};
