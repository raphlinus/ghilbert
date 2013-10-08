// Theorem writer is for making modifications to existing theorems.
GH.theoremWriter = function(prover) {
	this.prover = prover;
};

GH.theoremWriter.attachToLast = function(lines, str) {
	lines[lines.length - 1] = lines[lines.length - 1].concat(str);
};

// TODO: Maybe combine this with prover code.
GH.theoremWriter.prototype.write = function(theorem) {
	this.prover.depth = 0;
	var variableGenerator = new GH.Prover.variableGenerator();
	var parameters = theorem.getParameters(variableGenerator);

	var header = [];
	var inputParameters = parameters.inputs.length > 0 ? parameters.inputs : [parameters.output.left()];
	header.push('thm (' + theorem.action(inputParameters).name + ' () (');
	for (var i = 0; i < parameters.inputs.length; i++) {
		header.push('     hyp' + (i + 1) + ' ' + parameters.inputs[i].toString());
	};
	GH.theoremWriter.attachToLast(header, ')');
	header.push('     ' + parameters.output.toString());
	this.printLines(header);

	this.prover.depth++;
	for (var i = 1; i <= parameters.inputs.length; i++) {
		this.prover.println('hyp' + i);
	}
	theorem.inline(inputParameters);
	this.prover.depth--;
	this.prover.println(')');
	this.prover.println('');
};

GH.theoremWriter.prototype.applyThm = function(theorem, sexps) {
	var action = theorem.action(sexps);
	if (this.prover.symbolDefined(action.name)) {
		this.print(action.hyps, action.name);
	} else if (theorem.canAddTheorem(sexps)) {
		alert('Can add Theorem not defined yet.');
	} else {
		theorem.inline(sexps);
	}
};

GH.theoremWriter.prototype.print = function(hyps, name) {
	this.prover.print(hyps, name);
};

GH.theoremWriter.prototype.printLines = function(lines) {
	for (var i = 0; i < lines.length; i++) {
		this.prover.println(lines[i]);
	}
};

GH.theoremWriter.prototype.reposition = function(sexp, oldPosition, newPosition) {
	return this.prover.reposition(sexp,oldPosition, newPosition);
};

// Generates inference proofs ending in i like lteq1i.
GH.theoremWriter.prototype.infer = function(generator, sexp) {
	this.prover.addTheorem(generator, sexp);
	var action = generator.action(sexp);
	var name = action.name;

	// Uses the proof if it already exists in the repository.
	if (!this.prover.symbolDefined(name + 'i')) {
		var baseTheorem = new GH.ProofGenerator.baseTheorem(this, name, this.prover.getSymbol(name));
		inferTheorem = new GH.ProofGenerator.inferDecorator(this, baseTheorem);
		this.write(inferTheorem);
	}
	return name + 'i';
};

// Generates inference proofs ending in d like lteq1d.
GH.theoremWriter.prototype.deduce = function(generator, sexp) {
	this.prover.addTheorem(generator, sexp);
	var action = generator.action(sexp);
	var name = action.name;

	// Uses the proof if it already exists in the repository.
	if (!this.prover.symbolDefined(name + 'd')) {
		var baseTheorem = new GH.ProofGenerator.baseTheorem(this, name, this.prover.getSymbol(name));
		deduceTheorem = new GH.ProofGenerator.deduceDecorator(this, baseTheorem);
		this.write(deduceTheorem);
	}
	return name + 'd';
};

