GH.ProofGenerator.evaluatorNegative = function(prover) {
  this.prover = prover;
  this.operators = ['-n'];
};

GH.ProofGenerator.evaluatorNegative.prototype.action = function(sexp) {
	return new GH.action('undefined', []);
};

GH.ProofGenerator.evaluatorNegative.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorNegative.prototype.inline = function(sexp) {
	if (sexp.child().operator == '-n') {
		this.prover.print([sexp.child().child()], 'doubleneg');
		this.prover.getLast();
		sexp = this.prover.replace(sexp);
	} else if (sexp.child().operator == '0') {
		this.prover.print([], 'neg0');
		this.prover.getLast();
		sexp = this.prover.replace(sexp);
	} else {
		sexp = this.prover.openExp(sexp.child);
		sexp = this.prover.evaluate();
		return this.prover.closeExp(sexp);
	}
	return sexp;
};

GH.ProofGenerator.evaluatorNegative.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorNegative.prototype.calculate = function(sexp) {
	return -this.prover.calculate(sexp.child());
};