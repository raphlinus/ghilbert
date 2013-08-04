GH.ProofGenerator.evaluatorAnd = function(prover) {
  this.prover = prover;
  this.operators = ['/\\'];
};

GH.ProofGenerator.evaluatorAnd.prototype.action = function(sexp) {
	return new GH.action('undefinedAnd', []);
};

GH.ProofGenerator.evaluatorAnd.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorAnd.prototype.inline = function(sexp) {
	if (this.calculate(sexp)) {
		this.prover.evaluate(sexp.left().copy());
		this.prover.evaluate(sexp.right().copy());
		this.prover.print([], 'pm3.2i');
	}
	return true;
};

GH.ProofGenerator.evaluatorAnd.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorAnd.prototype.calculate = function(sexp) {
	return this.prover.calculate(sexp.left()) && this.prover.calculate(sexp.right());
};