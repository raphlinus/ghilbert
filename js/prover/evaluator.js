GH.ProofGenerator.evaluator = function(prover) {
  this.prover = prover;

  this.generators = [];
  this.generators.push([['+'], new GH.ProofGenerator.evaluatorAdd(prover)]);
  this.generators.push([['*'], new GH.ProofGenerator.evaluatorMultiply(prover)]);
  this.generators.push([['=', '<', '<='], new GH.ProofGenerator.evaluatorEquality(prover)]);
  this.generators.push([['S'], new GH.ProofGenerator.evaluatorSuccessor(prover)]);
};

GH.ProofGenerator.evaluator.prototype.stepName = function(sexp) {
	for (var i = 0; i < this.generators.length; i++) {
		var generator = this.generators[i];
		var operators = generator[0];
		for (var j = 0; j < operators.length; j++) {
			if (operators[j] == sexp.operator_) {
				return generator[1].stepName(sexp);
			}
		}
	}
	return null;
};

GH.ProofGenerator.evaluator.prototype.isApplicable = function(sexp) {
	// If we already know the expression is true, there's no reason to evaluate it.
	if (sexp.isProven) {
		return false;
	}
	for (var i = 0; i < this.generators.length; i++) {
		var generator = this.generators[i];
		var operators = generator[0];
		for (var j = 0; j < operators.length; j++) {
			if (operators[j] == sexp.operator_) {
				return generator[1].isApplicable(sexp);
			}
		}
	}
	return null;
};

GH.ProofGenerator.evaluator.prototype.hyps = function(sexp) {
	for (var i = 0; i < this.generators.length; i++) {
		var generator = this.generators[i];
		var operators = generator[0];
		for (var j = 0; j < operators.length; j++) {
			if (operators[j] == sexp.operator_) {
				return generator[1].hyps(sexp);
			}
		}
	}
	return null;
};

GH.ProofGenerator.evaluator.prototype.inline = function(sexp) {
	for (var i = 0; i < this.generators.length; i++) {
		var generator = this.generators[i];
		var operators = generator[0];
		for (var j = 0; j < operators.length; j++) {
			if (operators[j] == sexp.operator_) {
				return generator[1].inline(sexp);
			}
		}
	}
	return null;
};

GH.ProofGenerator.evaluator.prototype.addTheorem = function(sexp) {
	for (var i = 0; i < this.generators.length; i++) {
		var generator = this.generators[i];
		var operators = generator[0];
		for (var j = 0; j < operators.length; j++) {
			if (operators[j] == sexp.operator_) {
				if (generator[1].addTheorem != null) {
					return generator[1].addTheorem(sexp);
				} else {
					return false;
				}
			}
		}
	}
	return false;
};