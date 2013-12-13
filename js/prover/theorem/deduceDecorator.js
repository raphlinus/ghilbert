GH.ProofGenerator.deduceDecorator = function(writer, theorem) {
	this.writer = writer;
	this.theorem = theorem;
};

GH.ProofGenerator.deduceDecorator.prototype.action = function(sexps) {
	return new GH.action(this.theorem.getName() + 'd', []);
};

// Get the input and output parameters. The hypotheses and conclusion.
GH.ProofGenerator.deduceDecorator.prototype.getParameters = function() {
	var baseParameters = this.theorem.getParameters();
	var antecedent = GH.sExpression.createVariable(baseParameters.variables.generate('wff'));
	var baseAntecent = baseParameters.output.left();
	var baseAntecents = [];
	while (baseAntecent.operator == '/\\') {
		baseAntecents.push(baseAntecent.left());
		baseAntecent = baseAntecent.right();
	}
	baseAntecents.push(baseAntecent);
	
	var inputs = [];
	for (var i = 0; i < baseAntecents.length; i++) {
		inputs.push(GH.sExpression.createOperator('->', [antecedent, baseAntecents[i]]));
	}
	var output = GH.sExpression.createOperator('->', [antecedent, baseParameters.output.right()]);
	return {inputs: inputs, output: output, variables: baseParameters.variables};
};

GH.ProofGenerator.deduceDecorator.prototype.inline = function(sexps) {
	var rightSide = [sexps[0].right()];
	for (var i = 1; i < sexps.length; i++) {
		this.writer.print([], 'jca');
	}
	this.writer.applyThm(this.theorem, rightSide);
	this.writer.print([], 'syl');
	return output;
};

GH.ProofGenerator.deduceDecorator.prototype.canAddTheorem = function(sexps) {
	return false;
};
