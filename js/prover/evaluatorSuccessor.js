GH.ProofGenerator.evaluatorSuccessor = function(prover) {
  this.prover = prover;
};

GH.ProofGenerator.evaluatorSuccessor.prototype.stepName = function(sexp) {
	var num = GH.numUtil.decimalNumberSexp(sexp.child());
	return 'succeed' + num;
};

GH.ProofGenerator.evaluatorSuccessor.prototype.isApplicable = function(sexp) {
	var num = GH.numUtil.decimalNumberSexp(sexp.child());
	return !isNaN(num);
};

GH.ProofGenerator.evaluatorSuccessor.prototype.hyps = function(sexp) {
	return [];
};

GH.ProofGenerator.evaluatorSuccessor.prototype.inline = function(sexp) {
	this.prover.print([sexp.child()], 'a1suc');
	var result = this.prover.getLast();
	result = result.copy();
	this.prover.evaluate(result.right());
	return true;
};

GH.ProofGenerator.evaluatorSuccessor.prototype.addTheorem = function(sexp) {
	return false;
};