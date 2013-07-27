GH.ProofGenerator.evaluatorDivides = function(prover) {
  this.prover = prover;
  this.operators = ['|'];
};

GH.ProofGenerator.evaluatorDivides.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return new GH.action(leftNum + 'divides' + rightNum, []);
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

GH.ProofGenerator.evaluatorDivides.prototype.proveDivision = function(sexp, leftNum, rightNum) {
	var xNum = rightNum / leftNum;
	var x = GH.sExpression.createVariable('x');
	var xNum = GH.numUtil.createNum(xNum);
	this.prover.print([sexp.left(), sexp.right(), x], 'df-divides');

	// TODO: Implement this using an evaluatorExists.	
	this.prover.print([x, xNum], 'tyex');
	var existence = this.prover.getLast();
	this.prover.print([sexp.left(), x, xNum], 'mulcant2');
	var cancellation = this.prover.getLast();
	cancellation = this.prover.evaluate(cancellation.left());
	this.prover.remove();
	cancellation = this.prover.getLast();
	cancellation = this.prover.commute(cancellation);
	existence = this.prover.replace(existence.right());
	existence = this.prover.evaluate(existence.right());
	
	return this.prover.remove();
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
	return false;
};

GH.ProofGenerator.evaluatorDivides.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return (rightNum % leftNum) == 0;
};
