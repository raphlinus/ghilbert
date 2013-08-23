// Performs universal instantiation.
GH.ProofGenerator.instantiator = function(prover) {
  this.prover = prover;
};

GH.ProofGenerator.instantiator.prototype.action = function(sexp) {
	return new GH.action('undefined', []);
};

GH.ProofGenerator.instantiator.prototype.isApplicable = function(sexp) {
	return (sexp.operator == 'A.');
};

GH.ProofGenerator.instantiator.prototype.inline = function(sexp, instant) {
	var condition = GH.operatorUtil.create('=', [sexp.left(), instant]);
	var result = this.prover.condition(sexp.right(), condition);
	this.prover.print([], 'cla4g');
	this.prover.replace(sexp);
	return true;
};

GH.ProofGenerator.instantiator.prototype.canAddTheorem = function(sexp) {
	return false;
};