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
		return new GH.sExpression('({/})', -1, -1, true);  // Empty Set
	} else if (setArray.length == 1) {
		return new GH.sExpression.createOperator('{}', [GH.numUtil.createNum(setArray[0])]);
	} else {
		var firstNum = setArray.shift();
		return new GH.sExpression.createOperator(
		    'u.', [GH.setUtil.createSet([firstNum]), GH.setUtil.createSet(setArray)]);
	}
};

GH.setUtil.removeArrayDuplicates = function(inputArray) {
	var outputArray = [];
	for (var  i = 0; i < inputArray.length; i++) {
		if ((i == 0) || (inputArray[i] != inputArray[i - 1])) {
			outputArray.push(inputArray[i]);
		}
	}
	return outputArray;
};

GH.setUtil.equals = function(leftSet, rightSet) {
	if (leftSet.length != rightSet.length) {
		return false;
	}
	for (var i = 0; i < leftSet.length; i++) {
		if (leftSet[i] != rightSet[i]) {
			return false;
		}
	}
	return true;
};

// Find the first element that is in the left set, but not in the right set.
GH.setUtil.getMissingElement = function(leftSet, rightSet) {
	for (var i = 0; i < leftSet.length; i++) {
		var isMissing = true;
		for (var j = 0; (j < rightSet.length) && isMissing; j++) {
			if (leftSet[i] == rightSet[j]) {
				isMissing = false;
			}
		}
		if (isMissing) {
			return leftSet[i];
		}
	}
	return null;
};

GH.setUtil.setDifference = function(leftSet, rightSet) {
	var diff = [];
	for (var i = 0; i < leftSet.length; i++) {
		var isMissing = true;
		for (var j = 0; (j < rightSet.length) && isMissing; j++) {
			if (leftSet[i] == rightSet[j]) {
				isMissing = false;
			}
		}
		if (isMissing) {
			diff.push(leftSet[i]);
		}
	}
	return diff;
};