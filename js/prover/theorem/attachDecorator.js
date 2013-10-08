GH.ProofGenerator.attachDecorator = function(writer, theorem, operator, operandIndex) {
	this.writer = writer;
	this.theorem = theorem;
	this.operator = operator;
	this.operandIndex = operandIndex;

	var variableGenerator = new GH.Prover.variableGenerator();
	this.baseParameters = this.theorem.getParameters(variableGenerator);
	var baseOperator = this.baseParameters.output.operator;

	alert('Update replace');
	var replaceOperation = GH.ProofGenerator.replacer.getReplaceOperation(this.operator, baseOperator, index);
	this.replaceThm = replaceOperation && replaceOperation.name;
	this.resultOperator = replaceOperation && replaceOperation.resultOperator;
	this.parameters = null;
};

GH.ProofGenerator.attachDecorator.prototype.action = function(sexps) {
	if (sexps.length != 1) {
		alert('Attach Decorator should have one input.');
	}
	var postfix = GH.operatorUtil.getName(this.operator) + this.operandIndex + 1;
	var baseInput;
	if (this.baseParameters.inputs.length > 0) {
		baseInput = sexps;
	} else {
		baseInput = [sexps[0].operands[this.operandIndex]];
	}
	return new GH.action(this.theorem.action(baseInput).name + postfix, []);
};

GH.ProofGenerator.attachDecorator.prototype.getNewOperands = function(variableGenerator) {
	var operands = [];
	var types = GH.operatorUtil.getOperatorTypes(this.operator);
	for (var i = 0; i < types.length - 1; i++) {
		if (i == this.operandIndex) {
			operands.push(null);
		} else {
			operands.push(variableGenerator.generate(types[i]));
		}
	}
	return operands;
};

// Get the input and output parameters. The hypotheses and conclusion.
GH.ProofGenerator.attachDecorator.prototype.getParameters = function() {
	if (!this.parameters) {
		var parameters = this.theorem.getParameters();
		parameters.output = parameters.output.copy();
		var operands = this.getNewOperands(parameters.variables);
		operands[this.operandIndex] = parameters.output.left();
		var leftSide = GH.operatorUtil.create(this.operator, operands);
		
		operands[this.operandIndex] = parameters.output.right();
		var rightSide = GH.operatorUtil.create(this.operator, operands);
	
		parameters.output = GH.operatorUtil.create(this.resultOperator, [leftSide, rightSide]);
		this.parameters = parameters;
	}
	return this.parameters;
};

GH.ProofGenerator.attachDecorator.prototype.inline = function(sexps) {	var baseInput;
	if (this.baseParameters.inputs.length > 0) {
		baseInput = sexps;
	} else {
		baseInput = [sexps[0].operands[this.operandIndex]];
	}

	this.writer.applyThm(this.theorem, baseInput);

	var mandHyps = [];
	var types = GH.operatorUtil.getOperatorTypes(this.operator);
	for (var i = 0; i < types.length - 1; i++) {
		if (i != this.operandIndex) {
			mandHyps.push(sexps[0].operands[i]);
		}
	}
	this.writer.print(mandHyps, this.replaceThm);
};

GH.ProofGenerator.attachDecorator.prototype.isValid = function() {
	return !!this.replaceThm;
};

GH.ProofGenerator.attachDecorator.prototype.canAddTheorem = function(sexps) {
	return false;
};