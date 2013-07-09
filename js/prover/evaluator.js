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
			if (operators[j] == sexp.operator) {
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
			if (operators[j] == sexp.operator) {
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
			if (operators[j] == sexp.operator) {
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
			if (operators[j] == sexp.operator) {
				return generator[1].inline(sexp);
			}
		}
	}
	return null;
};

GH.ProofGenerator.evaluator.prototype.canAddTheorem = function(sexp) {
	for (var i = 0; i < this.generators.length; i++) {
		var generator = this.generators[i];
		var operators = generator[0];
		for (var j = 0; j < operators.length; j++) {
			if (operators[j] == sexp.operator) {
				return generator[1].canAddTheorem(sexp);
			}
		}
	}
	return false;
};

GH.ProofGenerator.evaluator.prototype.addTheorem = function(sexp) {
	for (var i = 0; i < this.generators.length; i++) {
		var generator = this.generators[i];
		var operators = generator[0];
		for (var j = 0; j < operators.length; j++) {
			if (operators[j] == sexp.operator) {
				generator[1].addTheorem(sexp)
			}
		}
	}
};

// Takes an operator and bounds on the operands and generate 
GH.ProofGenerator.evaluator.prototype.batchEvaluation = function(operator, leftBounds, rightBounds) {
	for (var i = leftBounds[0]; i <= leftBounds[1]; i++) {
		var leftNum = GH.numUtil.numToSexp(i);
		for (var j = rightBounds[0]; j <= rightBounds[1]; j++) {
			window.console.log(i + ', ' + j);
			var rightNum = GH.numUtil.numToSexp(j);
			var sexp = GH.sExpression.createOperator(operator, [leftNum, rightNum]);
			this.prover.evaluate(sexp);
		}
	}
	this.prover.direct.update(true);
};