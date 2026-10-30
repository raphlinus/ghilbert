GH.ProofGenerator.evaluatorTriangle = function(prover) {
  this.prover = prover;
  this.operators = ['tri'];
};

GH.ProofGenerator.evaluatorTriangle.prototype.action = function(sexp) {
	var num = GH.numUtil.decimalNumberSexp(sexp.child());
	return new GH.action('triangle' + num, []);
};

GH.ProofGenerator.evaluatorTriangle.prototype.theoremName = function(sexp) {	
	return 'Triangle';
};

GH.ProofGenerator.evaluatorTriangle.prototype.isApplicable = function(sexp) {
	return true;
};

// triangle 0 should already be in the repository.
GH.ProofGenerator.evaluatorTriangle.prototype.inline = function(sexp) {
	var num = GH.numUtil.decimalNumberSexp(sexp.child());
	var predecessor = GH.numUtil.createNum(num - 1);
	
	var result = this.prover.openExp(sexp, 'Add Indices');
	this.prover.print([predecessor], 'trianglePlus1r');
	result = this.prover.getLast();
	result = this.prover.evaluate(result.left().child()).parent.parent;
	result = this.prover.closeExp(result);
	result = this.prover.openExp(result, 'Insert Previous Numbers');
	result = this.prover.evaluate(result.left().left()).parent.parent;
	result = this.prover.closeExp(result);
	result = this.prover.openExp(result, 'Sum Numbers');
	result = this.prover.evaluate(result);
	return this.prover.closeExp(result);
};

GH.ProofGenerator.evaluatorTriangle.prototype.canAddTheorem = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorTriangle.prototype.calculate = function(sexp) {
	var num = this.prover.calculate(sexp.child());
	return (num * (num + 1)) / 2;
};
