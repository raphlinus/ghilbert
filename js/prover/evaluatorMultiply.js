GH.ProofGenerator.evaluatorMultiply = function(prover) {
  this.prover = prover;
};

GH.ProofGenerator.evaluatorMultiply.prototype.stepName = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());
	if (isNaN(leftNum) || isNaN(rightNum)) {
		return null;
	}
	if (!isNaN(GH.numUtil.decimalNumberSexp(sexp))) {
		return null;
	}
	
	leftNum  = GH.numUtil.decimalNumberSexp(sexp.left());
	rightNum = GH.numUtil.decimalNumberSexp(sexp.right());

	if (leftNum == 0) {
		return 'pa_ax5r';
	}
	if (rightNum == 0) {
		return 'pa_ax5'
	}
	if (leftNum == 1) {
		return 'mulidr'
	}
	if (rightNum == 1) {
		return 'mulid'
	}

	return leftNum + 'times' + rightNum;
};

GH.ProofGenerator.evaluatorMultiply.prototype.isApplicable = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());
	if (isNaN(leftNum) || isNaN(rightNum)) {
		return false
	}
	// If the full expression already is a decimal number, there is nothing to evaluate.
	if (!isNaN(GH.numUtil.decimalNumberSexp(sexp))) {
		// If the whole 
		return false;
	}
	return true;
};

GH.ProofGenerator.evaluatorMultiply.prototype.hyps = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());

	if ((leftNum == 0) || (leftNum == 1)) {
		return [sexp.right()];
	}
	if ((rightNum == 0) || (rightNum == 1)) {
		return [sexp.left()];
	}
	return [];
};

GH.ProofGenerator.evaluatorMultiply.prototype.inline = function(sexp) {
	var leftNum  = GH.numUtil.decimalNumberSexp(sexp.left());
	var rightNum = GH.numUtil.decimalNumberSexp(sexp.right());
	
	if (isNaN(leftNum) || isNaN(rightNum)) {
		var extraReplacement = ((!sexp.parent) && (GH.operatorUtil.getType(sexp) != 'wff'));
		if (isNaN(leftNum)) {
			sexp = this.prover.replaceLeft(this.prover.evaluator, sexp);
		}
		if (isNaN(rightNum)) {
			sexp = this.prover.replaceRight(this.prover.evaluator, sexp);
		}
		if (extraReplacement) {
			this.prover.replaceWith(this.prover.evaluator, sexp);
		} else {
			this.prover.apply(this.prover.evaluator, sexp);
		}
		return true;
	}

	if ((leftNum == 0) || (leftNum == 1) || (rightNum == 0) || (rightNum == 1)) {
		return false;
	} else if ((leftNum < 10) && (rightNum < 10)) {
		this.multiplySingleDigits(sexp, leftNum, rightNum);
	} else if (GH.numUtil.powerOfTenSexp(sexp.right()) != 0) {
		this.multiplyRightPowerOf10(sexp);
	} else if (GH.numUtil.powerOfTenSexp(sexp.left()) != 0) {
		this.multiplyLeftPowerOf10(sexp);
	} else if (rightNum < 10) {
		this.multiplyRightSingleDigit(sexp);
	} else {
		this.multiplyNumbers(sexp);
	}
	return true;
};

GH.ProofGenerator.evaluatorMultiply.prototype.canAddTheorem = function(sexp) {
	var leftNum  = GH.numUtil.decimalNumberSexp(sexp.left());
	var rightNum = GH.numUtil.decimalNumberSexp(sexp.right());
	return ((leftNum < 10) && (rightNum < 10));
};

GH.ProofGenerator.evaluatorMultiply.prototype.addTheorem = function(sexp) {	
	var leftNum  = GH.numUtil.decimalNumberSexp(sexp.left());
	var rightNum = GH.numUtil.decimalNumberSexp(sexp.right());
	var product = leftNum * rightNum;
	this.prover.println('## <title> One-digit Multiplication </title>');
	this.prover.println('thm (' + this.stepName(sexp) + ' () () (= ' + sexp.toString() + ' ' + GH.numUtil.numToSexpString(product) + ')');
	this.prover.depth++;
	this.inline(sexp);
	this.prover.depth--;
	this.prover.println(')');
};

GH.ProofGenerator.evaluatorMultiply.prototype.multiplySingleDigits = function(sexp, leftNum, rightNum) {
	sexp = sexp.copy();
	var expansion;
	var createDigit = GH.sExpression.createDigit;
	var createOperator = GH.sExpression.createOperator;
	switch(leftNum) {
		case 2:		expansion = createOperator('+', [createDigit(1), createDigit(1)]);   break;
		case 3:		expansion = createOperator('+', [createDigit(2), createDigit(1)]);   break;
		case 4:		expansion = createOperator('+', [createDigit(2), createDigit(2)]);   break;
		case 5:		expansion = createOperator('+', [createDigit(4), createDigit(1)]);   break;
		case 6:		expansion = createOperator('+', [createDigit(5), createDigit(1)]);   break;
		case 7:		expansion = createOperator('+', [createDigit(5), createDigit(2)]);   break;
		case 8:		expansion = createOperator('+', [createDigit(5), createDigit(3)]);   break;
		case 9:		expansion = createOperator('+', [createDigit(5), createDigit(4)]);   break;
	}
	expansion = this.prover.evaluate(expansion);
	expansion = this.prover.commute(expansion.parent);
	var result = this.prover.replace(sexp.left());
	result = this.prover.distributeLeft(result.parent);
	
	result = this.prover.replaceLeft(this.prover.evaluator, result);
	result = this.prover.replaceRight(this.prover.evaluator, result);
	// result = this.prover.apply(this.prover.evaluator, result);
	result = this.prover.replaceWith(this.prover.evaluator, result);
	return result;
};

GH.ProofGenerator.evaluatorMultiply.prototype.multiplyRightPowerOf10 = function(sexp) {
	sexp = sexp.copy();
	if (sexp.left().operator == '+') {
		sexp = this.prover.distributeLeft(sexp)
		sexp = this.prover.evaluate(sexp.right()).parent;
		sexp = this.prover.evaluate(sexp.left()).parent;
	} else if (sexp.left().operator == '*') {
		sexp = this.prover.associateRight(sexp)
		sexp = this.prover.evaluate(sexp.right()).parent;
	}
	return sexp;
};

GH.ProofGenerator.evaluatorMultiply.prototype.multiplyLeftPowerOf10 = function(sexp) {
	sexp = sexp.copy();
	sexp = this.prover.commute(sexp);
	return this.prover.evaluate(sexp);
};

GH.ProofGenerator.evaluatorMultiply.prototype.pullInMultiplier = function(sexp) {
	if (sexp.left() && sexp.left().operator == '*') {
		if (sexp.left().left().operator != '10') {
			sexp = this.prover.repositioner.reposition(sexp, '(A B) C', '(A C) B');
		} else {
			sexp = this.prover.commute(sexp);
		}
	}
	return sexp;
};

GH.ProofGenerator.evaluatorMultiply.prototype.pullOutMultiplier = function(sexp) {
	if (sexp.right() && sexp.right().operator == '*' && sexp.right().left().operator != '10') {
		sexp = this.prover.associateLeft(sexp);
	}
	return sexp;
};

/*
GH.ProofGenerator.evaluatorMultiply.prototype.multiplyRightSingleDigit = function(sexp) {
	sexp = sexp.copy();
	while(sexp.left().operator == '+') {
		sexp = this.prover.distributeLeft(sexp);
		// The associateLeft isn't really necessary. It's done to remove some parentheses.
		if (sexp.parent.operator == '+') {
			sexp = this.prover.associateLeft(sexp.parent);
		}
		sexp = sexp.right();
	}
	
	sexp = this.pullInMultiplier(sexp);
	if (sexp.parent) {
		sexp = sexp.parent;
		while(sexp.left().operator == '+') {
			sexp = sexp.left();
			sexp = this.pullInMultiplier(sexp.right()).parent;
		}
		sexp = sexp.left();
		sexp = this.pullInMultiplier(sexp);
	}
	sexp = sexp.getRoot().right();
};*/


// The left side is a single digit or a number times a power of ten.
// The right side is a single digit.
// This maybe should go into inline.
GH.ProofGenerator.evaluatorMultiply.prototype.multiplyTwoDigits = function(sexp) {
	if (sexp.left().operator == '*') {
		sexp = this.pullInMultiplier(sexp);
		sexp = this.prover.evaluate(sexp.left()).parent;
	}
	sexp = this.prover.evaluate(sexp);
	return sexp;
};

GH.ProofGenerator.evaluatorMultiply.prototype.multiplyRightSingleDigit = function(sexp) {
	sexp = sexp.copy();
	while(sexp.left().operator == '+') {
		sexp = this.prover.distributeLeft(sexp);
		sexp = sexp.right();
	}

	sexp = this.multiplyTwoDigits(sexp);
	while(sexp.parent.operator != '=') {
		sexp = sexp.parent.left();
		sexp = this.multiplyTwoDigits(sexp).parent;
		sexp = this.prover.evaluate(sexp);
	}	
	

/*	sexp = this.pullInMultiplier(sexp);
	if (sexp.parent) {
		sexp = sexp.parent;
		while(sexp.left().operator == '+') {
			sexp = sexp.left();
			sexp = this.pullInMultiplier(sexp.right()).parent;
		}
		sexp = sexp.left();
		sexp = this.pullInMultiplier(sexp);
	}
	sexp = sexp.getRoot().right();*/
};

// Multiply any number x, a single digit d and a power of ten b: (x * d) * b. For example (435 * 7) * 100
GH.ProofGenerator.evaluatorMultiply.prototype.doubleMultiply = function(sexp) {
	sexp = this.prover.evaluate(sexp.left()).parent;
	return this.prover.evaluate(sexp);
}

GH.ProofGenerator.evaluatorMultiply.prototype.multiplyNumbers = function(sexp) {
	sexp = sexp.copy();
	while(sexp.right().operator == '+') {
		sexp = this.prover.distributeRight(sexp);
		// The associateLeft isn't really necessary. It's done to remove some parentheses.
		if (sexp.parent.operator == '+') {
			sexp = this.prover.associateLeft(sexp.parent);
		}
		sexp = sexp.right();
	}
	sexp = this.pullOutMultiplier(sexp);
	if (sexp.parent) {
		sexp = sexp.parent;
		while(sexp.left().operator == '+') {
			sexp = sexp.left();
			sexp = this.pullOutMultiplier(sexp.right()).parent;
		}
		sexp = sexp.left();
		sexp = this.pullOutMultiplier(sexp);
	}
	sexp = this.doubleMultiply(sexp);
	while(sexp.parent.operator != '=') {
		sexp = sexp.parent.right();
		sexp = this.doubleMultiply(sexp).parent;
		sexp = this.prover.evaluate(sexp);
	}	
};