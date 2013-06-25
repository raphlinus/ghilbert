GH.ProofGenerator.evaluator = function(prover) {
  this.prover = prover;

  this.generators = [];
  this.generators.push(['+', new GH.ProofGenerator.evaluatorAdd(prover)]);
  this.generators.push(['*', new GH.ProofGenerator.evaluatorMultiply(prover)]);
};

GH.ProofGenerator.evaluator.prototype.stepName = function(sexp) {
	for (var i = 0; i < this.generators.length; i++) {
		if (this.generators[i][0] == sexp.operator_) {
			return this.generators[i][1].stepName(sexp);
		}
	}
	return null;
};

GH.ProofGenerator.evaluator.prototype.isApplicable = function(sexp) {
	for (var i = 0; i < this.generators.length; i++) {
		if (this.generators[i][0] == sexp.operator_) {
			return this.generators[i][1].isApplicable(sexp);
		}
	}
	return null;
};

GH.ProofGenerator.evaluator.prototype.hyps = function(sexp) {
	for (var i = 0; i < this.generators.length; i++) {
		if (this.generators[i][0] == sexp.operator_) {
			return this.generators[i][1].hyps(sexp);
		}
	}
	return null;
};

GH.ProofGenerator.evaluator.prototype.inline = function(sexp) {
	for (var i = 0; i < this.generators.length; i++) {
		if (this.generators[i][0] == sexp.operator_) {
			return this.generators[i][1].inline(sexp);
		}
	}
	return null;
};

GH.ProofGenerator.evaluator.prototype.addTheorem = function(sexp) {
	for (var i = 0; i < this.generators.length; i++) {
		if (this.generators[i][0] == sexp.operator_) {
			if (this.generators[i][1].addTheorem != null) {
				return this.generators[i][1].addTheorem(sexp);
			} else {
				return false;
			}
		}
	}
	return false;
};