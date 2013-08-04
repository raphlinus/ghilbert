GH.ProofGenerator.evaluatorSuccessor = function(prover) {
  this.prover = prover;
  this.operators = ['S'];
};

GH.ProofGenerator.evaluatorSuccessor.prototype.action = function(sexp) {
	var num = GH.numUtil.decimalNumberSexp(sexp.child());
	return new GH.action('succeed' + num, []);
};

GH.ProofGenerator.evaluatorSuccessor.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorSuccessor.prototype.inline = function(sexp) {
	this.prover.print([sexp.child()], 'a1suc');
	var result = this.prover.getLast();
	result = result.copy();
	this.prover.evaluate(result.right());
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorSuccessor.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorSuccessor.prototype.calculate = function(sexp) {
	var num = this.prover.calculate(sexp.child());
	return num + 1;
};