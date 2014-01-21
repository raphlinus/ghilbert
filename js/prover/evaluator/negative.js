GH.ProofGenerator.evaluatorNegative = function(prover) {
  this.prover = prover;
  this.operators = ['-n'];
};

GH.ProofGenerator.evaluatorNegative.prototype.isApplicable = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorNegative.prototype.calculate = function(sexp) {
	return -this.prover.calculate(sexp.child());
};