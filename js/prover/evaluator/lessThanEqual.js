GH.ProofGenerator.evaluatorLessThanEqual = function(prover) {
  this.prover = prover;
  this.operators = ['<='];
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.variableAction = function(sexp) {
	return null;
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (leftNum <= rightNum) {
		operatorName = 'lessEq';
	} else {
		operatorName = 'notLessEq';
	}
	return new GH.action(leftNum + operatorName + rightNum, []);
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.inline = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (leftNum < rightNum) {
		this.prover.evaluate(this.prover.create('<', [sexp.left(), sexp.right()]));
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '≤');
	} else if (leftNum == rightNum) {
		this.prover.evaluate(this.prover.create('=', [sexp.left(), sexp.right()]));
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '≤');
	} else if (leftNum > rightNum) {
		this.prover.evaluate(this.prover.create('>', [sexp.left(), sexp.right()]));
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '¬≤');
	} 
	return null;
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.theoremName = function(sexp) {
	return 'One-Digit Inequality';
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return leftNum <= rightNum;
};
