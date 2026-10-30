GH.ProofGenerator.evaluatorDivide = function(prover) {
  this.prover = prover;
  this.operators = ['/'];
};

GH.ProofGenerator.evaluatorDivide.prototype.variableAction = function(sexp) {
	var denominator = this.prover.calculate(sexp.right());
	if (denominator == 1) {
		return new GH.action('divid', [sexp.left()]);
	}
	return null;
};

GH.ProofGenerator.evaluatorDivide.prototype.action = function(sexp) {
	var numerator   = this.prover.calculate(sexp.left());
	var denominator = this.prover.calculate(sexp.right());
	return new GH.action(numerator + 'divide' + denominator, []);
};

GH.ProofGenerator.evaluatorDivide.prototype.isApplicable = function(sexp) {
	var numerator   = this.prover.calculate(sexp.left());
	var denominator = this.prover.calculate(sexp.right());
	return (denominator != 0) && ((GH.numUtil.gcd(numerator, denominator) != 1) || (denominator == 1));
};

GH.ProofGenerator.evaluatorDivide.prototype.inline = function(sexp) {
	var numerator   = this.prover.calculate(sexp.left());
	var denominator = this.prover.calculate(sexp.right());
	if (numerator == 0) {
		this.prover.equals0(sexp.right());
		this.prover.print([], '0divi');
		return true;
	} else if (numerator == denominator) {
		this.prover.equals0(sexp.right());
		this.prover.print([], 'frac1i');
		return true;
	}

	var gcd = GH.numUtil.gcd(numerator, denominator);
	sexp = this.prover.openExp(sexp, 'Separate Common Factor');
	sexp = this.prover.unevaluate(this.prover.create('*', [numerator   / gcd, gcd]), sexp.left());
	sexp = this.prover.unevaluate(this.prover.create('*', [denominator / gcd, gcd]), sexp.right());
	sexp = this.prover.closeExp();
	sexp = this.prover.openExp(sexp, 'Cancel Common Factor');

	this.prover.equals0(denominator / gcd);
	this.prover.equals0(gcd);
	this.prover.print([GH.numUtil.createNum(numerator / gcd)], 'fracFactorsi');
	sexp = this.prover.closeExp();

	if (this.prover.calculate(sexp.right()) == 1) {
		this.prover.evaluate(sexp);
	}
	return true;
};

GH.ProofGenerator.evaluatorDivide.prototype.theoremName = function(sexp) {	
	return 'Division';
};

GH.ProofGenerator.evaluatorDivide.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorDivide.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return (leftNum / rightNum);
};
