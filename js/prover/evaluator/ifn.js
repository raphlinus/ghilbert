GH.ProofGenerator.evaluatorIfn = function(prover) {
  this.prover = prover;
  this.operators = ['ifn'];
};

GH.ProofGenerator.evaluatorIfn.prototype.action = function(sexp) {
	return new GH.action('undefinedIfn', []);
};

GH.ProofGenerator.evaluatorIfn.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorIfn.prototype.inline = function(sexp) {
	if (this.prover.calculate(sexp.operands[0])) {
		this.prover.evaluate(sexp.operands[0]);
		this.prover.print([sexp.operands[0], sexp.operands[1], sexp.operands[2]], 'ifn1');
		this.prover.print([], 'ax-mp');
	} else {
		this.prover.evaluate(sexp.operands[0]);
		this.prover.print([sexp.operands[0], sexp.operands[1], sexp.operands[2]], 'ifn2');
		this.prover.print([], 'ax-mp');
	}
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorIfn.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorIfn.prototype.calculate = function(sexp) {
	if (this.prover.calculate(sexp.operands[0])) {
		return this.prover.calculate(sexp.operands[1]);
	} else {
		return this.prover.calculate(sexp.operands[2]);
	}
};