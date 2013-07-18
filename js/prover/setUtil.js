GH.setUtil = {};

GH.setUtil.isReduced = function(sexp) {
	return (GH.setUtil.sexpToArray(sexp) != null);
};

GH.setUtil.sexpToArray = function(sexp) {
	if ((sexp.operator == '{}') && (GH.numUtil.isReduced(sexp.child()))) {
		return [GH.numUtil.decimalNumberSexp(sexp.child())];
	}
	if ((sexp.operator == 'u.') && (sexp.left().operator == '{}')) {
		var leftSet = GH.setUtil.sexpToArray(sexp.left());
		var rightSet = GH.setUtil.sexpToArray(sexp.right());
		if (leftSet && rightSet && (leftSet.length == 1) &&
		   (rightSet.indexOf(leftSet[0]) == -1)) {  // Do not allow duplicates.
			return leftSet.concat(rightSet);
		}
	}
	return null;
};


GH.setUtil.createSet = function(setArray) {
	if (setArray.length == 0) {
		return new GH.sExpression('{/}', -1, -1, true);  // Empty Set
	} else if (setArray.length == 1) {
		return new GH.sExpression.createOperator('{}', [GH.numUtil.createNum(setArray[0])]);
	} else {
		var firstNum = setArray.shift();
		return new GH.sExpression.createOperator(
		    'u.', [GH.setUtil.createSet([firstNum]), GH.setUtil.createSet(setArray)]);
	}
};