GH.ProofGenerator.evaluatorExponent = function(prover) {
  this.prover = prover;
  this.operators = ['exp'];
};

GH.ProofGenerator.evaluatorExponent.prototype.variableAction = function(sexp) {
	var base  = this.prover.calculate(sexp.left());
	var exponent = this.prover.calculate(sexp.right());

	if (exponent == 0) {
		return new GH.action('exp0', [sexp.left()]);
	} else if (exponent == 1) {
		return new GH.action('expid', [sexp.left()]);
	}
}

GH.ProofGenerator.evaluatorExponent.prototype.action = function(sexp) {
	var base  = this.prover.calculate(sexp.left());
	var exponent = this.prover.calculate(sexp.right());

	return new GH.action(base + 'power' + exponent, []);
};

GH.ProofGenerator.evaluatorExponent.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorExponent.prototype.inline = function(sexp) {
	var base  = this.prover.calculate(sexp.left());
	var exponent = this.prover.calculate(sexp.right());

	var result = this.prover.unevaluate(GH.operatorUtil.create('+', [exponent - 1, 1]), sexp.right()).parent;
	this.prover.print([sexp.left(), GH.numUtil.createNum(exponent - 1)], 'expplus1');
	result = this.prover.replace(result.right());
	result = this.prover.evaluate(result.right()).parent;
	return this.prover.evaluate(result);
};

GH.ProofGenerator.evaluatorExponent.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorExponent.prototype.calculate = function(sexp) {
	var base  = this.prover.calculate(sexp.left());
	var exponent = this.prover.calculate(sexp.right());
	return Math.pow(leftNum, rightNum);
};