GH.ProofGenerator.baseTheorem = function(writer, name, rawThm) {
	this.writer = writer;
	this.name = name;
	this.rawThm = rawThm;
	this.parameters = null;
	
	var rawVars = this.rawThm[4];
	this.vars = [];
	this.varTypes = [];
	for (var i = 0; i < rawVars.length; i++) {
		this.vars.push(rawVars[i][2]);
		this.varTypes.push(rawVars[i][1]);
	}
};

GH.ProofGenerator.baseTheorem.prototype.getName = function() {
	return this.name;
};

GH.ProofGenerator.baseTheorem.prototype.action = function(sexps) {
	var inputs;
	if (this.rawThm[2].length > 0) {
		inputs = this.rawThm[2];
	} else {
		inputs = [this.rawThm[3][1]];
	}
	var mandHyps = [];
	for (var i = 0; i < this.vars.length; i++) {
		mandHyps.push(null);
	}
	if (sexps.length != inputs.length) {
		alert('Wrong number of inputs');
	}
	for (var i = 0; i< sexps.length; i++) {
		GH.ProofGenerator.baseTheorem.fillInHyps(sexps[i], inputs[i], this.vars, mandHyps);
	}
	GH.Prover.variableGenerator.fillInMissing(mandHyps, this.varTypes);
	return new GH.action(this.name, mandHyps);
};

GH.ProofGenerator.baseTheorem.fillInHyps = function(sexp, input, vars, mandHyps) {
	var index = -1;
	for (var i = 0; i < vars.length; i++) {
		if (input == vars[i]) {
			index = i;
		}
	}

	if (index >= 0) {
		mandHyps[index] = sexp;
	} else {
		for (var i = 1; i < input.length; i++) {
			GH.ProofGenerator.baseTheorem.fillInHyps(sexp.operands[i - 1], input[i], vars, mandHyps);
		}
	}
};

// Get the input and output parameters for the theorem header. The hypotheses and conclusion.
GH.ProofGenerator.baseTheorem.prototype.getParameters = function() {
	if (!this.parameters) {
		var variableGenerator = new GH.Prover.variableGenerator();
		var newVars = [];
		var rawVars = this.rawThm[4];
		for (var i = 0; i < rawVars.length; i++) {
			newVars.push(variableGenerator.generate(rawVars[i][1]));
		}

		var inputExps = [];
		for (var i = 0; i < this.rawThm[2].length; i++) {
			inputExps.push(GH.sExpression.fromRaw(this.rawThm[2][i]));
			GH.ProofGenerator.baseTheorem.swapVariables(inputExps[i], this.vars, newVars);
		}
		var outputExp = GH.sExpression.fromRaw(this.rawThm[3]);
		GH.ProofGenerator.baseTheorem.swapVariables(outputExp, this.vars, newVars);
		this.parameters = {inputs: inputExps, output: outputExp, variables: variableGenerator};
	}
	return this.parameters;
};

GH.ProofGenerator.baseTheorem.swapVariables = function(sexp, oldVars, newVars) {
	var index = oldVars.indexOf(sexp.operator);
	if (index >= 0) {
		sexp.operator = newVars[index];
	}
	for (var i = 0; i < sexp.operands.length; i++) {
		GH.ProofGenerator.baseTheorem.swapVariables(sexp.operands[i], oldVars, newVars);
	}
};

GH.ProofGenerator.baseTheorem.prototype.getOperator = function() {
	return this.rawThm[3][0];
};

// Base Theorems should already be in the database and should not need to be proven.
GH.ProofGenerator.baseTheorem.prototype.inline = null;
GH.ProofGenerator.baseTheorem.prototype.addTheorem = null;

GH.ProofGenerator.baseTheorem.prototype.canAddTheoremm = function(sexps) {
	return false;
};

