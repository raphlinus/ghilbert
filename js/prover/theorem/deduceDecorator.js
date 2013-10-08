GH.ProofGenerator.deduceDecorator = function(writer, theorem) {
	this.writer = writer;
	this.theorem = theorem;
};

GH.ProofGenerator.deduceDecorator.prototype.action = function(sexps) {
	return new GH.action(this.theorem.action(sexps).name + 'd', []);
};

// Get the input and output parameters. The hypotheses and conclusion.
GH.ProofGenerator.deduceDecorator.prototype.getParameters = function() {
	var baseParameters = this.theorem.getParameters();
	var antecedent = GH.sExpression.createVariable(baseParameters.variables.generate('wff'));
	var input  = GH.sExpression.createOperator('->', [antecedent, baseParameters.output.left()]);
	var output = GH.sExpression.createOperator('->', [antecedent, baseParameters.output.right()]);
	return {inputs: [input], output: output, variables: baseParameters.variables};
};

GH.ProofGenerator.deduceDecorator.prototype.inline = function(sexps) {
	var rightSide = [sexps[0].right()];
	this.writer.applyThm(this.theorem, rightSide);
	this.writer.print([], 'syl');
	return output;
};

GH.ProofGenerator.deduceDecorator.prototype.canAddTheorem = function(sexps) {
	return false;
};
