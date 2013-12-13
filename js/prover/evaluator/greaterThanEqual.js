GH.ProofGenerator.evaluatorGreaterThanEqual = function(prover) {
  this.prover = prover;
  this.operators = ['>='];
};

GH.ProofGenerator.evaluatorGreaterThanEqual.prototype.variableAction = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (rightNum == 0) {
		return new GH.action('ge0', [sexp.left()]);
	}
	return null;
};

GH.ProofGenerator.evaluatorGreaterThanEqual.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (leftNum >= rightNum) {
		operatorName = 'greaterEq';
	} else {
		operatorName = 'notGreaterEq';
	}
	return new GH.action(leftNum + operatorName + rightNum, []);
};

GH.ProofGenerator.evaluatorGreaterThanEqual.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorGreaterThanEqual.prototype.inline = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (leftNum < rightNum) {
		this.prover.evaluate(this.prover.create('<', [sexp.left(), sexp.right()]));
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '¬≥');
	} else if (leftNum == rightNum) {
		this.prover.evaluate(this.prover.create('=', [sexp.left(), sexp.right()]));
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '≥');
	} else if (leftNum > rightNum) {
		this.prover.evaluate(this.prover.create('>', [sexp.left(), sexp.right()]));
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '≥');
	} 
	return null;
};

GH.ProofGenerator.evaluatorGreaterThanEqual.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorGreaterThanEqual.prototype.theoremName = function(sexp) {
	return 'One-Digit Inequality';
};

GH.ProofGenerator.evaluatorGreaterThanEqual.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return leftNum >= rightNum;
};
