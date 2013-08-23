// Performs existential generalization.
GH.ProofGenerator.existGeneralizer = function(prover) {
  this.prover = prover;
};

GH.ProofGenerator.existGeneralizer.prototype.action = function(sexp) {
	return new GH.action('undefined', []);
};

GH.ProofGenerator.existGeneralizer.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.existGeneralizer.prototype.inline = function(sexp, example) {
	var condition = GH.operatorUtil.create('=', [sexp, example]);
	var result = this.prover.condition(this.prover.getLast(), condition);
	this.prover.commute(result.left());
	this.prover.reverseLastSteps();
	this.prover.remove();
	this.prover.print([example, sexp], 'tyex');
	result = this.prover.getLast();
	this.prover.reverseLastSteps();
	this.prover.replace(result.right());
	return true;
};

GH.ProofGenerator.existGeneralizer.prototype.canAddTheorem = function(sexp) {
	return false;
};