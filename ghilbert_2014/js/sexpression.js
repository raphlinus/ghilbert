// Javascript for displaying proof steps. Steps are organized into proof blocks.
// by Paul Merrell, 2013


/**
 * Represents an s-expression.
 */
 GH.sExpression = function(operator, begin, end, isString) {
	this.parent = null;
	this.operator = operator;
	this.operands = [];
	this.siblingIndex = null;

	// If the expression comes from a string.	
	this.isString = isString;

	// Where the expression begins and ends within the textarea.
	this.begin = begin;
	this.end = end;

	// Set to true later, if the expression is a proven statement on the proof stack.
	this.isProven = false;
};

GH.sExpression.prototype.appendOperand = function(operand) {
	operand.parent = this;
	operand.siblingIndex = this.operands.length;
	this.operands.push(operand);
};

GH.sExpression.prototype.replaceOperand = function(operand, index) {
	operand.parent = this;
	operand.siblingIndex = index;
	this.operands[index] = operand;
};
 
GH.sExpression.fromRaw = function(expression) {
	var isString = (GH.typeset.typeOf(expression) == 'string');
	var operator = isString ? expression : expression[0];
	var result = new GH.sExpression(operator, expression.beg, expression.end, isString);

	if (!isString) {
		for (var i = 1; i < expression.length; i++) {
			result.appendOperand(GH.sExpression.fromRaw(expression[i]));
		}		
	}
	return result;
};

GH.sExpression.printRaw = function(expression) {
	return GH.sExpression.fromRaw(expression).toString();
};

// Create an s-expression for a number between 0 and 10.
GH.sExpression.createDigit = function(num) {
	return new GH.sExpression(num.toString(), -1, -1, false);
};

// Create an s-expression for a variable.
GH.sExpression.createVariable = function(name) {
	return new GH.sExpression(name, -1, -1, true);
};

GH.sExpression.createOperator = function(operator, operands) {
	var result = new GH.sExpression(operator, -1, -1, false);
	for (var i = 0; i < operands.length; i++) {
		result.appendOperand(operands[i]);
	}
	return result;
};

GH.sExpression.prototype.getRoot = function() {
	var result = this;
	while(result.parent) {
		result = result.parent;
	}
	return result;
};

GH.sExpression.fromString = function(str) {
	return GH.sExpression.fromRaw(GH.sExpression.stringToExpression(str));
};

GH.sExpression.stringToExpression = function(str) {
	var depth = 0;
	var starts = [];
	var ends = [];
	var start = null;
	var end = null;
	
	for (var i = 0; i < str.length; i++) {
		var c = str.charAt(i);
		if (c != ' ') {
			if ((start == null) && (depth == 1)) {
				start = i;
			}
		}

		if (c == '(') {
			depth++;
		} else if (c == ')') {
			if ((depth == 1) && (start != null)) {
				end = i;
			}
			depth--;
		} else if (c == ' ') {
			if ((depth == 1) && (start != null)) {
				end = i;
			}
		}
		if (end != null) {
			starts.push(start);
			ends.push(end);
			start = null;
			end = null;
		}
	}
	if (starts.length > 0) {
		var expressions = [];
		for (var i = 0; i < starts.length; i++) {
			expressions.push(GH.sExpression.stringToExpression(str.substring(starts[i], ends[i])));
		}
		return expressions;
	} else {
		return str;
	}
};

// Construct the expression from the operator and operands.
GH.sExpression.prototype.getExpression = function() {
	if (this.isString) {
		return this.operator;
	} else {
		var expression = [];
		expression.push(this.operator);
		for (var i = 0; i < this.operands.length; i++) {
			expression.push(this.operands[i].getExpression());
		}
		return expression;
	}
};

GH.sExpression.prototype.copy = function() {
	var newCopy = GH.sExpression.fromRaw(this.getExpression());
	newCopy.isProven = this.isProven;
	return newCopy;
};

GH.sExpression.prototype.child = function () {
	/* if (this.operands.length > 1) {
		alert('Warning this expression has more than one child.');
	} else if (this.operands.length == 0) {
		alert('Warning this expression has no children.');
	}*/
	return this.operands[0];
};

GH.sExpression.prototype.left = function () {
	if (this.operands.length < 2) {
		alert('Warning this expression does not have a left side.');
	}
	return this.operands[0];
};

GH.sExpression.prototype.right = function () {
	if (this.operands.length < 2) {
		alert('Warning this expression does not have a right side.');
	}
	return this.operands[1];
};

GH.sExpression.prototype.replace = function () {
	if (this.operands.length < 2) {
		alert('Warning this expression does not have a right side.');
	}
	return this.operands[1];
};

// Find all matches to sexp within this expression.
GH.sExpression.prototype.findExp = function(sexp) {
	var result = [];
	if (this.equals(sexp)) {
		result.push(this);
	}
	for (var i = 0; i < this.operands.length; i++) {
		result = result.concat(this.operands[i].findExp(sexp));
	}
	return result;
};

GH.sExpression.stripParams = function(operator) {
	delete operator['beg'];
	delete operator['end'];
	return operator;
};

// Returns true is the s-expressions are identical.
GH.sExpression.prototype.equals = function(sexp) {
	var numOperands = this.operands.length;
	GH.sExpression.stripParams(this.operator);
	GH.sExpression.stripParams(sexp.operator);
	if (this.operator.length != sexp.operator.length) {
		return false;
	}
	for (var i = 0; i < this.operator.length; i++) {
		if (this.operator[i] != sexp.operator[i]) {
			return false;
		}
	}
	if ((numOperands != sexp.operands.length)) {
		return false;
	}
	for (var i = 0; i < numOperands; i++) {
		if (!this.operands[i].equals(sexp.operands[i])) {
			return false;
		}
	}
	return true;
};

GH.sExpression.prototype.toString = function() {
	var result = [];	
	result.push(this.operator);
	for (var i = 0; i < this.operands.length; i++) {
		result.push(this.operands[i].toString());
	}
	result = result.join(' ');
	if (!this.isString) {
		result = '(' + result + ')';
	}
	return result;
};

GH.sExpression.prototype.getBeginning = function() {
	return this.begin;
};

GH.sExpression.prototype.isVariablePresent = function(variable) {
	if (this.operator.valueOf() == variable) {
		return true;
	}
	for (var i = 0; i < this.operands.length; i++) {
		if (this.operands[i].isVariablePresent(variable)) {
			return true;
		}
	}
	return false;
};
