GH.ProofGenerator.evaluatorDivides = function(prover) {
  this.prover = prover;
};

GH.ProofGenerator.evaluatorDivides.prototype.stepName = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());
	return leftNum + 'divides' + rightNum;
};

GH.ProofGenerator.evaluatorDivides.prototype.isApplicable = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());
	if (isNaN(leftNum) || isNaN(rightNum)) {
		return false;
	}
	return true;
};

GH.ProofGenerator.evaluatorDivides.prototype.hyps = function(sexp) {
	return [];
};

GH.ProofGenerator.evaluatorDivides.prototype.inline = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());
	if (rightNum % leftNum == 0) {
		this.proveDivision(sexp, leftNum, rightNum);
	} else {
		this.proveNoDivision(sexp, leftNum, rightNum);
	}
	return true;
};

GH.ProofGenerator.evaluatorDivides.prototype.proveDivision = function(sexp, leftNum, rightNum) {
	var xNum = rightNum / leftNum;
	var x = GH.sExpression.createVariable('x');
	var xNum = GH.numUtil.numToSexp(xNum);
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
	
	this.prover.remove();
//	var product = GH.sExpression.createOperator('*', [GH.numUtil.numToSexp(leftNum), GH.numUtil.numToSexp(x)])
//	this.prover.evaluate(product);
};

// Prove that A does not divide B.
GH.ProofGenerator.evaluatorDivides.prototype.proveNoDivision = function(sexp, leftNum, rightNum) {
	var c = Math.floor(rightNum / leftNum);
	c = GH.numUtil.numToSexp(c);
	var A = GH.numUtil.numToSexp(leftNum);
	var B = GH.numUtil.numToSexp(rightNum);
	this.prover.print([A, c, B], 'notDivides');
	
	var Ac = GH.sExpression.createOperator('*', [A, c]);          // A * c
	var lessPart = GH.sExpression.createOperator('<', [Ac, B]);   // A * c < B
	this.prover.evaluate(lessPart);

	var one = GH.numUtil.numToSexp(1);
	var c1 = GH.sExpression.createOperator('+', [c, one]);        // c + 1
	var Ac1 = GH.sExpression.createOperator('*', [A, c1]);          // A * (c + 1)
	var greaterPart = GH.sExpression.createOperator('<', [B, Ac1]);   // B < A * (c + 1)
	this.prover.evaluate(greaterPart);
	this.prover.print([], 'pm3.2i');
	this.prover.remove();
};

GH.ProofGenerator.evaluatorDivides.prototype.canAddTheorem = function(sexp) {
	return false;
};