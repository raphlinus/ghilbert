GH.ProofGenerator.evaluator = function(prover) {
  this.prover = prover;
  this.constant = new GH.ProofGenerator.evaluatorConstant(prover);

  this.generators = [];
  this.generators.push(new GH.ProofGenerator.evaluatorAdd(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorAnd(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorMultiply(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorEquality(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorNegative(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorLessThan(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorLessThanEqual(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorGreaterThan(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorGreaterThanEqual(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorSuccessor(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorDivides(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorPrime(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorDiv(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorElementOf(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorSingleton(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorUnion(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorIntersection(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorSetEquality(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorSubset(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorProperSubset(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorModulo(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorExponent(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorIfn(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorInterval(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorHalfMinus(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorSubstitution(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorApply(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorSum(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorProduct(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorFactorial(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorFibonacci(prover));
  this.generators.push(new GH.ProofGenerator.evaluatorTriangle(prover));
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


GH.ProofGenerator.evaluator.prototype.generatorAction = function(sexp) {
	var generator = this.findGenerator(sexp.operator);
	if (generator.variableAction) {
		var variableAction = generator.variableAction(sexp);
		if (variableAction != null) {
			return variableAction;
		}
	}
	if (generator) {
		return generator.action(sexp);
	} else {
		return new GH.action(null, []);
	}
};

GH.ProofGenerator.evaluator.prototype.action = function(sexp) {
	// Return null if any of the operands are not reduced.
	for (var i = 0; i < sexp.operands.length; i++) {
		var operand = sexp.operands[i];
		if ((!this.prover.operatorUtil.isReduced(operand)) && (!this.hasVariables(operand))) {
			return new GH.action(null, []);
		}
	}
	return this.generatorAction(sexp);
};

GH.ProofGenerator.evaluator.prototype.isApplicable = function(sexp) {
	// If we already know the expression is true, there's no reason to evaluate it.
	if (sexp.isProven) {
		return false;
	}
	// If the sexp is already a reduced decimal number, there's nothing more to do.
	if (this.prover.operatorUtil.isReduced(sexp)) {
		return false;
	}
	var generator = this.findGenerator(sexp.operator);
	
	if (generator) {
		// Only certain actions can handle expressions with variables in them.
		if (this.hasVariables(sexp)) {
			if (!generator.variableAction || (generator.variableAction(sexp) == null)) {
				return false;
			}
		}
		return generator.isApplicable(sexp);
	} else {
		return false;
	}
};

GH.ProofGenerator.evaluator.prototype.inline = function(sexp) {
	var generator = this.findGenerator(sexp.operator);
	if (generator) {
		if ((this.prover.getType(sexp) != 'wff') || (sexp.operator == '[/]')) {
			var allReduced = true;
			for (var i = 0; i < sexp.operands.length; i++) {
				if ((!this.prover.operatorUtil.isReduced(sexp.operands[i])) &&
				     (!generator.isOperandReducable || generator.isOperandReducable(i)) &&
				     (this.prover.getType(sexp.operands[i]) != 'wff')) {// Don't evaluate wffs. They don't have parents.
					sexp = this.prover.evaluate(sexp.operands[i]).parent;
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
			var result = this.prover.reduce(sexp);
			var action = this.generatorAction(result);
			// There might be an action available if an operand is not reduced.
			if (this.prover.symbolDefined(action.name)) {
				this.prover.print(action.hyps, action.name);
				result = this.prover.getLast();
			} else {
				result = generator.inline(result);
			}
			if (!result) {
				return false;
			}
			if (result.operator == '-.') {
				result = result.child();
			}
			for (var i = 0; i < sexp.operands.length; i++) {
				if (!this.prover.operatorUtil.isReduced(sexp.operands[i])) {
					result = this.prover.unevaluate(sexp.operands[i], result.operands[i]).parent;
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
		for (var i = 0; i < sexp.operands.length; i++) {
			if (!GH.numUtil.isReduced(sexp.operands[i])) {
				return false;
			}
		}
		return generator.canAddTheorem(sexp);
	} else {
		return false;
	}
};

GH.ProofGenerator.evaluator.prototype.addTheorem = function(sexp) {
	var generator = this.findGenerator(sexp.operator);
	if (generator) {
		var result = this.calculate(sexp);
		var type = this.prover.getType(sexp);
		var conclusion = sexp.toString();
		if (type == 'wff') {
			if (!result) {
				conclusion = '(-. ' + sexp.toString() + ')';
			}
		} else if (type == 'nat') {
			conclusion = '(= ' + sexp.toString() + ' ' + GH.numUtil.numToSexpString(result) + ')'
		} else if (type == 'set') {
			conclusion = '(=_ ' + sexp.toString() + ' ' + GH.setUtil.createSet(result).toString() + ')'
		} else {
			alert('Adding theorem with type ' + type + ' is not yet supported.');
		}

		sexp = sexp.copy();
		this.prover.println('## <title> ' + generator.theoremName(sexp) + ' </title>');
		this.prover.println('thm (' + this.action(sexp).name + ' () () ' + conclusion);
		this.prover.depth++;
		generator.inline(sexp);
		this.prover.depth--;
		this.prover.println(')');
	}
};

GH.ProofGenerator.evaluator.prototype.calculate = function(sexp) {
	var generator = this.findGenerator(sexp.operator);
	if (this.hasVariables(sexp)) {
		return null;
	}
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

// For unary operators
GH.ProofGenerator.evaluator.prototype.batchEvaluation1 = function(operator, bounds) {
	for (var i = bounds[0]; i <= bounds[1]; i++) {
		var num = GH.numUtil.createNum(i);
		window.console.log(i);
		var sexp = GH.sExpression.createOperator(operator, [num]);
		this.prover.evaluate(sexp);
	}
	this.prover.direct.update(true);
};
