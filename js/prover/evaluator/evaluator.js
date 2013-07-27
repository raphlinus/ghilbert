GH.ProofGenerator.evaluator = function(prover) {
  this.prover = prover;
  this.constant = new GH.ProofGenerator.evaluatorConstant(prover);

  this.generators = [];
  this.generators.push(new GH.ProofGenerator.evaluatorAdd(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorMultiply(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorEquality(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorSuccessor(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorDivides(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorElementOf(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorSingleton(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorUnion(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorIntersection(prover));
  this.generators.push(this.constant);
};

GH.ProofGenerator.evaluator.prototype.findGenerator = function(operator) {
	for (var i = 0; i < this.generators.length; i++) {
		var generator = this.generators[i];
		var operators = generator.operators;
		for (var j = 0; j < operators.length; j++) {
			if (operators[j] == operator) {
				return generator;
			}
		}
	}
	return null;
};

GH.ProofGenerator.evaluator.prototype.action = function(sexp) {
	var generator = this.findGenerator(sexp.operator);
	if (generator) {
		return generator.action(sexp);
	} else {
		return new GH.action(null, []);
	}
};

GH.ProofGenerator.evaluator.prototype.isApplicable = function(sexp) {
	// If we already know the expression is true, there's no reason to evaluate it.
	if (sexp.isProven) {
		return false;
	}
	// We cannot evaluate an expression with variables in it.
	if (this.hasVariables(sexp)) {
		return false;
	}
	// If the sexp is already a reduced decimal number, there's nothing more to do.
	if (GH.operatorUtil.isReduced(sexp)) {
		return false;
	}
	var generator = this.findGenerator(sexp.operator);
	if (generator) {
		return generator.isApplicable(sexp);
	} else {
		return false;
	}
};

GH.ProofGenerator.evaluator.prototype.inline = function(sexp) {
	var generator = this.findGenerator(sexp.operator);
	if (generator) {
		if (GH.operatorUtil.getType(sexp) != 'wff') {
			var allReduced = true;
			for (var i = 0; i < sexp.operands.length; i++) {
				if (!GH.operatorUtil.isReduced(sexp.operands[i])) {
					sexp = this.prover.replaceWith(this.prover.evaluator, sexp.operands[i]).parent;
					allReduced = false;
				}
			}
			if (!allReduced) {
				this.prover.evaluate(sexp);
				return true;
			} else {
				return generator.inline(sexp);
			}
		} else {
			var result = generator.inline(sexp);
			if (!result) {
				return false;
			}
			for (var i = 0; i < sexp.operands.length; i++) {
				if (!GH.operatorUtil.isReduced(sexp.operands[i])) {
					var copy = sexp.operands[i].copy();
					copy = this.prover.evaluate(copy);
					this.prover.commute(copy.parent);
					result = this.prover.replace(result.operands[i]).parent;
				}
			}
			return true;
		}
	} else {
		return null;
	}
};

GH.ProofGenerator.evaluator.prototype.canAddTheorem = function(sexp) {
	var generator = this.findGenerator(sexp.operator);
	if (generator) {
		return generator.canAddTheorem(sexp);
	} else {
		return false;
	}
};

GH.ProofGenerator.evaluator.prototype.addTheorem = function(sexp) {
	var generator = this.findGenerator(sexp.operator);
	if (generator) {
		generator.addTheorem(sexp);
	}
};

GH.ProofGenerator.evaluator.prototype.calculate = function(sexp) {
	var generator = this.findGenerator(sexp.operator);
	if (generator) {
		return generator.calculate(sexp);
	} else {
		return null;
	}
};

// Returns true, if any part of the expression has a variable in it.
// Returns false, if everything is a constant.
GH.ProofGenerator.evaluator.prototype.hasVariables = function(sexp) {
	if (sexp.operands.length > 0) {
		for (var i = 0; i < sexp.operands.length; i++) {
			if (this.hasVariables(sexp.operands[i])) {
				return true;
			}
		}
		return false;
	} else {
		var constants = this.constant.operators;
		for (var j = 0; j < constants.length; j++) {
			if (constants[j] == sexp.operator) {
				return false;
			}
		}
		return true;
	}
};

// Takes an operator and bounds on the operands and generate 
GH.ProofGenerator.evaluator.prototype.batchEvaluation = function(operator, leftBounds, rightBounds) {
	for (var i = leftBounds[0]; i <= leftBounds[1]; i++) {
		var leftNum = GH.numUtil.createNum(i);
		for (var j = rightBounds[0]; j <= rightBounds[1]; j++) {
			window.console.log(i + ', ' + j);
			var rightNum = GH.numUtil.createNum(j);
			var sexp = GH.sExpression.createOperator(operator, [leftNum, rightNum]);
			this.prover.evaluate(sexp);
		}
	}
	this.prover.direct.update(true);
};

