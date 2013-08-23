GH.ProofGenerator.evaluatorMultiply = function(prover) {
  this.prover = prover;
  this.operators = ['*'];
};

GH.ProofGenerator.evaluatorMultiply.prototype.variableAction = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());

	// TODO: Add a check that the numbers are reduced and not 0 * 5.
	if (leftNum == 0) {
		return new GH.action('pa_ax5r', [sexp.right()]);
	}
	if (rightNum == 0) {
		return new GH.action('pa_ax5', [sexp.left()]);
	}
	if (leftNum == 1) {
		return new GH.action('mulidr', [sexp.right()]);
	}
	if (rightNum == 1) {
		return new GH.action('mulid', [sexp.left()]);
	}
	return null;
};

GH.ProofGenerator.evaluatorMultiply.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());

	return new GH.action(leftNum + 'times' + rightNum, []);
};

GH.ProofGenerator.evaluatorMultiply.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorMultiply.prototype.inline = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());

	if ((leftNum == 0) || (leftNum == 1) || (rightNum == 0) || (rightNum == 1)) {
		return false;
	} else if ((leftNum < 10) && (rightNum < 10)) {
		return this.multiplySingleDigits(sexp, leftNum, rightNum);
	} else if (GH.numUtil.powerOfTenSexp(sexp.right()) != 0) {
		return this.multiplyRightPowerOf10(sexp);
	} else if (GH.numUtil.powerOfTenSexp(sexp.left()) != 0) {
		return this.multiplyLeftPowerOf10(sexp);
	} else if (rightNum < 10) {
		return this.multiplyRightSingleDigit(sexp);
	} else {
		return this.multiplyNumbers(sexp);
	}
	return true;
};

GH.ProofGenerator.evaluatorMultiply.prototype.canAddTheorem = function(sexp) {
	var leftNum  = GH.numUtil.decimalNumberSexp(sexp.left());
	var rightNum = GH.numUtil.decimalNumberSexp(sexp.right());
	return ((leftNum < 10) && (rightNum < 10));
};

GH.ProofGenerator.evaluatorMultiply.prototype.theoremName = function(sexp) {	
	return 'One-digit Multiplication';
};

GH.ProofGenerator.evaluatorMultiply.findSmallerDigits = function(num) {
	switch(num) {
		case 2:		return [1, 1];  // 2 = 1 + 1
		case 3:		return [2, 1];  // 3 = 2 + 1
		case 4:		return [2, 2];  // 4 = 2 + 2
		case 5:		return [4, 1];  // 5 = 4 + 1
		case 6:		return [5, 1];  // 6 = 5 + 1
		case 7:		return [5, 2]; 	// 7 = 5 + 2
		case 8:		return [5, 3]; 	// 8 = 5 + 3
		case 9:		return [5, 4]; 	// 9 = 5 + 4
	}
}

GH.ProofGenerator.evaluatorMultiply.prototype.multiplySingleDigits = function(sexp, leftNum, rightNum) {
	sexp = this.prover.openExp(sexp, 'One-Digit Multiplication');
	// Replace the smaller digit.
	if (leftNum < rightNum) {
		var smallerDigits = GH.ProofGenerator.evaluatorMultiply.findSmallerDigits(leftNum);
		result = this.prover.unevaluate(GH.operatorUtil.create('+', smallerDigits), sexp.left(), 'Seperate into Smaller Digits');
		result = this.prover.distributeLeft(result);
	} else {
		var smallerDigits = GH.ProofGenerator.evaluatorMultiply.findSmallerDigits(rightNum);
		result = this.prover.unevaluate(GH.operatorUtil.create('+', smallerDigits), sexp.right(), 'Seperate into Smaller Digits');
		result = this.prover.distributeRight(result);
	}
	
	result = this.prover.openExp(result, 'Multiply Smaller Digits');
	result = this.prover.evaluate(result.left(), 'Multiply Left Side').parent;
	result = this.prover.evaluate(result.right(), 'Multiply Right Side').parent;
	result = this.prover.closeExp(result);
	result = this.prover.evaluate(result, 'Sum the Total');
	return this.prover.closeExp(result);
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

// The left side is a single digit or a number times a power of ten.
// The right side is a single digit.
// This maybe should go into inline.
GH.ProofGenerator.evaluatorMultiply.prototype.multiplyTwoDigits = function(sexp) {
	sexp = this.prover.openExp(sexp, 'Multiply Two Digits');
	if (sexp.left().operator == '*') {
		sexp = this.pullInMultiplier(sexp);
		sexp = this.prover.evaluate(sexp.left()).parent;
	}
	sexp = this.prover.evaluate(sexp);
	return this.prover.closeExp(sexp);
};

GH.ProofGenerator.evaluatorMultiply.prototype.multiplyRightSingleDigit = function(sexp) {
	sexp = this.prover.openExp(sexp, 'One-Digit times Multiple-Digits');
	sexp = this.prover.openExp(sexp, 'Rearrange Digits');
	while(sexp.left().operator == '+') {
		sexp = this.prover.distributeLeft(sexp);
		sexp = sexp.right();
	}
	sexp = this.prover.closeExp(sexp);
	while(sexp.operator == '+') {
		sexp = sexp.right();
	}

	sexp = this.multiplyTwoDigits(sexp);
	while(sexp.parent.operator != '=') {
		sexp = sexp.parent.left();
		sexp = this.multiplyTwoDigits(sexp).parent;
		sexp = this.prover.evaluate(sexp);
	}
	return this.prover.closeExp(sexp);
};

// Multiply any number x, a single digit d and a power of ten b: (x * d) * b. For example (435 * 7) * 100
GH.ProofGenerator.evaluatorMultiply.prototype.doubleMultiply = function(sexp) {
	sexp = this.prover.openExp(sexp, 'Multiply Two Individual Digits');
	sexp = this.prover.evaluate(sexp.left(), 'Multiply Significant Digits').parent;
	sexp = this.prover.evaluate(sexp, 'Multiply Base');
	return this.prover.closeExp(sexp);
}

GH.ProofGenerator.evaluatorMultiply.prototype.multiplyNumbers = function(sexp) {
	sexp = this.prover.openExp(sexp, 'Multiplication');
	sexp = this.prover.openExp(sexp, 'Distribute Digits');
	while(sexp.right().operator == '+') {
		sexp = this.prover.distributeRight(sexp);
		// The associateLeft isn't really necessary. It's done to remove some parentheses.
		if (sexp.parent.operator == '+') {
			sexp = this.prover.associateLeft(sexp.parent);
		}
		sexp = sexp.right();
	}
	sexp = this.prover.closeExp(sexp);

	sexp = this.prover.openExp(sexp, 'Pull Out Base 10');
	while(sexp.operator == '+') {
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
	sexp = this.prover.closeExp(sexp);
	sexp = this.prover.openExp(sexp, 'Multiply Each Digit');
	while(sexp.operator == '+') {
		sexp = this.doubleMultiply(sexp.right()).parent;
		sexp = sexp.left();
	}
	sexp = this.doubleMultiply(sexp).parent;
	sexp = this.prover.closeExp(sexp);
	while(sexp.parent && sexp.parent == '+') {
		sexp = sexp.parent;
	}
	sexp = this.prover.evaluate(sexp, 'Sum the Total');
	return this.prover.closeExp(sexp);
};

GH.ProofGenerator.evaluatorMultiply.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return leftNum * rightNum;
};