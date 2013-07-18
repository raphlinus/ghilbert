GH.ProofGenerator.evaluatorConstant = function(prover) {
  this.prover = prover;
  this.operators = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '10', '{/}'];
};

GH.ProofGenerator.evaluatorConstant.prototype.isApplicable = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorConstant.prototype.calculate = function(sexp) {
	if (sexp.operator == '{/}') {
		return [];
	}
	return parseInt(sexp.operator);
};