GH.ProofGenerator.evaluatorDivides = function(prover) {
  this.prover = prover;
  this.operators = ['|'];
};

GH.ProofGenerator.evaluatorDivides.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (this.calculate(sexp)) {
		return new GH.action(leftNum + 'divides' + rightNum, []);
	} else {
		return new GH.action(leftNum + 'notdivides' + rightNum, []);
	}
};

GH.ProofGenerator.evaluatorDivides.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorDivides.prototype.inline = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (this.calculate(sexp)) {
		return this.proveDivision(sexp, leftNum, rightNum);
	} else {
		return this.proveNoDivision(sexp, leftNum, rightNum);
	}
};

GH.ProofGenerator.evaluatorDivides.prototype.theoremName = function(sexp) {	
	return 'Divisibility';
};

GH.ProofGenerator.evaluatorDivides.prototype.proveDivision = function(sexp, leftNum, rightNum) {
	var xNum = rightNum / leftNum;
	this.prover.evaluate(this.prover.create('*', [leftNum, xNum]));
	this.prover.print([], 'proveDivides');
	return this.prover.getLast();
};

// Prove that A does not divide B.
GH.ProofGenerator.evaluatorDivides.prototype.proveNoDivision = function(sexp, leftNum, rightNum) {
	var c = Math.floor(rightNum / leftNum);
	c = GH.numUtil.createNum(c);
	var A = GH.numUtil.createNum(leftNum);
	var B = GH.numUtil.createNum(rightNum);
	this.prover.print([A, c, B], 'notDivides');
	
	var Ac = GH.sExpression.createOperator('*', [A, c]);          // A * c
	var lessPart = GH.sExpression.createOperator('<', [Ac, B]);   // A * c < B
	this.prover.evaluate(lessPart);

	var one = GH.numUtil.createNum(1);
	var c1 = GH.sExpression.createOperator('+', [c, one]);        // c + 1
	var Ac1 = GH.sExpression.createOperator('*', [A, c1]);          // A * (c + 1)
	var greaterPart = GH.sExpression.createOperator('<', [B, Ac1]);   // B < A * (c + 1)
	this.prover.evaluate(greaterPart);
	this.prover.print([], 'pm3.2i');
	return this.prover.remove();
};

GH.ProofGenerator.evaluatorDivides.prototype.canAddTheorem = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return ((leftNum >= 2) && (leftNum < rightNum) && (rightNum >= 2) && (rightNum < 20));
};

GH.ProofGenerator.evaluatorDivides.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return (rightNum % leftNum) == 0;
};
