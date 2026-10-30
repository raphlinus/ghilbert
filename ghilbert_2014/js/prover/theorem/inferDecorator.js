GH.ProofGenerator.inferDecorator = function(writer, theorem) {
	this.writer = writer;
	this.theorem = theorem;
};

GH.ProofGenerator.inferDecorator.prototype.action = function(sexps) {
	return new GH.action(this.theorem.action(sexps).name + 'i', []);
};

// Get the input and output parameters. The hypotheses and conclusion.
GH.ProofGenerator.inferDecorator.prototype.getParameters = function() {
	var baseParameters = this.theorem.getParameters();
	return {inputs: [baseParameters.output.left()], output: baseParameters.output.right(), variables: baseParameters.variables};
};

GH.ProofGenerator.inferDecorator.prototype.inline = function(sexps) {
	this.writer.applyThm(this.theorem, sexps);
	var operator = this.theorem.getParameters().output.operator;
	if (operator == '->') {
		this.writer.print([], 'ax-mp');
	} else if (operator == '<->') {
		this.writer.print([], 'mpbi');
	} else {
		alert('Infer decorator does not apply to ' + operator);
	}
	return output;
};

GH.ProofGenerator.inferDecorator.prototype.canAddTheorem = function(sexps) {
	return false;
};
