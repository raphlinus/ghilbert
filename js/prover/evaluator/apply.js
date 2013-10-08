GH.ProofGenerator.evaluatorApply = function(prover) {
  this.prover = prover;
  this.operators = ['apply'];
};

GH.ProofGenerator.evaluatorApply.prototype.variableAction = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorApply.prototype.action = function(sexp) {
	return new GH.action('undefined-apply', []);
};

GH.ProofGenerator.evaluatorApply.prototype.isApplicable = function(sexp) {
	return (sexp.left().operator == 'lambda');
};

// Determine if the expression depends on the given variable.
GH.ProofGenerator.evaluatorApply.dependsOn = function(sexp, variable) {
	if (sexp.operands.length > 0) {
		for (var i = 0; i < sexp.operands.length; i++) {
			if (GH.ProofGenerator.evaluatorApply.dependsOn(sexp.operands[i], variable)) {
				return true;
			}
		}
		return false;
	} else {
		// This is just a check that sexp.operator == variable.operator.
		// It's a dumb way to do this, but the .beg and .end values make this more complicated.
		if (sexp.operator.length != variable.operator.length) {
			return false;
		}
		for (var i = 0; i < sexp.operator.length; i++) {
			if (sexp.operator[i] != variable.operator[i]) {
				return false;
			}
		}
		return true;
	}
};

GH.ProofGenerator.evaluatorApply.prototype.inline = function(sexp) {
	var bindingVariable = GH.Prover.variableGenerator.generateUnused(sexp, 'bind');
	var functionInput = sexp.left().left();
	var functionOutput = sexp.left().right();
	var applicationInput = sexp.right();

	if (functionInput.equals(functionOutput)) {
		this.prover.print([functionInput, applicationInput], 'applyfunid');
	} else if (GH.ProofGenerator.evaluatorApply.dependsOn(functionOutput, functionInput)) {
		var condition = this.prover.create('=', [functionInput, bindingVariable]);
		this.prover.condition(functionOutput, condition);
		condition = this.prover.create('=', [functionInput, applicationInput]);
		this.prover.condition(functionOutput, condition);
		this.prover.print([], 'applylambda');
	} else {
		// The function is a constant.
		this.prover.print([functionInput, functionOutput, applicationInput], 'applylambdaconst');
	}
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorApply.prototype.isOperandReducable = function(index) {
	return false;
};

GH.ProofGenerator.evaluatorApply.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorApply.prototype.calculate = function(sexp) {
	alert('EvaluateApply.calculate not defined.');
};