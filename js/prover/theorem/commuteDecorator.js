GH.ProofGenerator.commuteDecorator = function(writer, theorem, order) {
	this.writer = writer;
	this.theorem = theorem;
	this.order = order; // The new order of operands.
};

GH.ProofGenerator.commuteDecorator.prototype.action = function(sexps) {
	if (sexps.length > 1) {
		alert('Commute Decorator assumes that all the parts are ANDed into one hypotheses.');
	}
	if (this.order.length >= 10) {
		alert('More than ten hypotheses may mess up the commute decorator\'s naming convention.');
	}
	var orderName = '';
	for (var i = 0; i < this.order.length; i++) {
		orderName += this.order[i];
	}
	return new GH.action(this.theorem.action(sexps).name + 'com' + orderName, []);
};

// Get the input and output parameters. The hypotheses and conclusion.
GH.ProofGenerator.commuteDecorator.prototype.getParameters = function() {
	var parameters = this.theorem.getParameters();
	var inputRoot;
	if (parameters.inputs.length > 0) {
		parameters.inputs[0] = parameters.inputs[0].copy();
		inputRoot = parameters.inputs[0];
	} else {
		parameters.output = parameters.output.copy();
		inputRoot = parameters.output.left();
	}

	// Grab the old values;
	var oldValues = [];
	var inputNode = inputRoot;
	for (var i = 0; i < this.order.length - 1; i++) {
		oldValues.push(inputNode.left());
		inputNode = inputNode.right();
	}
	oldValues.push(inputNode);

	// Find new order.
	var newValues = [];
	for (var i = 0; i < this.order.length; i++) {
		newValues[i] = oldValues[this.order[i]];
	}

	// Insert the values into their new position
	inputNode = inputRoot;
	for (var i = 0; i < this.order.length - 1; i++) {
		inputNode.operands[0] = newValues[i];
		inputNode = inputNode.right();
	}
	inputNode.parent.operands[1] = newValues[newValues.length - 1];

	return parameters;
};

GH.ProofGenerator.commuteDecorator.prototype.inline = function(sexps) {
	var reverseOrder = [];
	for (var i = 0; i < this.order.length; i++) {
		reverseOrder.push(this.order.indexOf(i));
	}
	var sequentialStr = '';
	var reverseStr = '';
	for (var i = 0; i < this.order.length - 1; i++) {
		sequentialStr += '(' + i + ' ';
		reverseStr += '(' + reverseOrder[i] + ' ';
	}
	sequentialStr += this.order.length - 1;
	reverseStr += reverseOrder[reverseOrder.length - 1];
	for (var i = 0; i < this.order.length - 1; i++) {
		sequentialStr += ')';
		reverseStr += ')';
	}
	sexps[0] = this.writer.reposition(sexps[0], sequentialStr, reverseStr);
	this.writer.applyThm(this.theorem, sexps);
};

GH.ProofGenerator.commuteDecorator.prototype.canAddTheorem = function(sexps) {
	return false;
};