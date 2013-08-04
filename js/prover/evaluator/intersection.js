GH.ProofGenerator.evaluatorIntersection = function(prover) {
  this.prover = prover;
  this.operators = ['i^i'];
};

GH.ProofGenerator.evaluatorIntersection.prototype.action = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	var intersection = this.calculate(sexp);
	if ((leftSet.length == intersection.length) && (rightSet.length == intersection.length)) {
		return new GH.action('inidm', [sexp.left()]);
	}
	return new GH.action('doIntersection', []);
};

GH.ProofGenerator.evaluatorIntersection.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorIntersection.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorIntersection.prototype.inline = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	var intersection = this.calculate(sexp);
	if (leftSet.indexOf(rightSet[0]) == -1) {
		if (rightSet.length == 1) {
			return this.removeRightSingleton(sexp, rightSet[0], leftSet);
		} else {
			return this.removeRightElement(sexp);
		}
	} else if (rightSet.indexOf(leftSet[0]) == -1) {
		if (leftSet.length == 1) {
			return this.removeLeftSingleton(sexp, leftSet[0], rightSet);
		} else {
			return this.removeLeftElement(sexp);
		}
	} else if (leftSet[0] == rightSet[0]) {
		if (leftSet.length == 1) {
			return this.removeRightElement(sexp);
		} else if (rightSet.length == 1) {
			return this.removeLeftElement(sexp);
		} else {
			return this.intersectingElements(sexp);
		}
	} else {
		alert('Intersecting unordered sets.');
	}
	return null;
};

GH.ProofGenerator.evaluatorIntersection.prototype.removeRightSingleton = function(sexp, rightNum, leftSet) {
	var inLeftSet = GH.sExpression.createOperator('e.', [sexp.right().child(), sexp.left()]);
	this.prover.evaluate(inLeftSet);
	this.prover.print([], 'emptyIn2');
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorIntersection.prototype.removeLeftSingleton = function(sexp, leftNum, rightSet) {
	var inRightSet = GH.sExpression.createOperator('e.', [sexp.left().child(), sexp.right()]);
	this.prover.evaluate(inRightSet);
	this.prover.print([], 'emptyIn1');
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorIntersection.prototype.removeRightElement = function(sexp) {
	sexp = sexp.copy();
	var result = this.prover.distributeRight(sexp);
	result = this.prover.evaluate(result.left()).parent;
	result = this.prover.evaluate(result.right()).parent;
	return this.prover.evaluate(result);
};

GH.ProofGenerator.evaluatorIntersection.prototype.removeLeftElement = function(sexp) {
	sexp = sexp.copy();
	var result = this.prover.distributeLeft(sexp);
	result = this.prover.evaluate(result.left()).parent;
	result = this.prover.evaluate(result.right()).parent;
	return this.prover.evaluate(result);
};

GH.ProofGenerator.evaluatorIntersection.prototype.intersectingElements = function(sexp) {
	sexp = sexp.copy();
	var result = this.prover.undistributeRight(sexp);
	result = this.prover.evaluate(result.right()).parent;
	return this.prover.evaluate(result);
};

GH.ProofGenerator.evaluatorIntersection.prototype.calculate = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	var intersection = [];
	for (var i = 0; i < leftSet.length; i++) {
		var match = false;
		for (var j = 0; j < rightSet.length; j++) {
			if (leftSet[i] == rightSet[j]) {
				match = true;
			}
		}
		if (match) {
			intersection.push(leftSet[i]);
		}
	}
	return intersection;
};