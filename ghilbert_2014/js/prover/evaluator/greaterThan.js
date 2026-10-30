GH.ProofGenerator.evaluatorGreaterThan = function(prover) {
  this.prover = prover;
  this.operators = ['>'];
};

GH.ProofGenerator.evaluatorGreaterThan.prototype.variableAction = function(sexp) {
	return null;
};

GH.ProofGenerator.evaluatorGreaterThan.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (leftNum >= rightNum) {
		operatorName = 'greater';
	} else {
		operatorName = 'notGreater';
	}
	return new GH.action(leftNum + operatorName + rightNum, []);
};

GH.ProofGenerator.evaluatorGreaterThan.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorGreaterThan.prototype.inline = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if ((rightNum == 0) && (10 >= leftNum) && (leftNum > 0)) {
		return this.numMoreThanZero(sexp, leftNum);
	} else if (leftNum < rightNum) {
		this.prover.evaluate(this.prover.create('<', [sexp.left(), sexp.right()]));
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '¬>');
	} else if (leftNum == rightNum) {
		this.prover.evaluate(this.prover.create('=', [sexp.left(), sexp.right()]));
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '¬>');
	} else if (leftNum > rightNum) {
		if ((leftNum <= 10) && (rightNum <= 10)) {
			return this.addToBothSides(sexp, leftNum - rightNum, 0, rightNum);
		} else {
			return this.inequality(sexp, leftNum, rightNum);
		}
	} 
	return null;
};

GH.ProofGenerator.evaluatorGreaterThan.prototype.numMoreThanZero = function(sexp, leftNum) {
	sexp = this.prover.openExp(sexp, 'Separate into smaller inequalities');
	var inequality1 = this.prover.create('>', [leftNum, leftNum - 1]);
	var inequality2 = this.prover.create('>', [leftNum - 1, 0]);
	var result1 = this.prover.evaluate(inequality1, 'Smaller Inequality');
	var result2 = this.prover.evaluate(inequality2, 'Smaller Inequality');
	sexp = this.prover.replace(result1.right());
	sexp = this.prover.closeExp(sexp);
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorGreaterThan.prototype.addToBothSides = function(sexp, leftNum, rightNum, addition) {
	var inequality = this.prover.create('>', [leftNum, rightNum]);   // leftNum > rightNum
	this.prover.openExp(sexp, 'Add To Both Sides');
	this.prover.openExp(sexp, 'Derive Smaller Inequality');
	this.prover.evaluate(inequality);
	this.prover.closeExp(sexp);

	this.prover.openExp(sexp, 'Add To Both Sides');
	var addExp = GH.numUtil.createNum(addition);
	this.prover.print([addExp], 'gtadd2i');
	this.prover.closeExp(sexp);
	result = this.prover.getLast();
	result = this.prover.evaluate(result.left(), 'Simplify Left Side').parent;
	result = this.prover.evaluate(result.right(), 'Simplify Right Side').parent;
	return this.prover.closeExp(result);
};

// TODO: Merge this with lessThan.
GH.ProofGenerator.evaluatorGreaterThan.prototype.inequality = function(sexp, leftNum, rightNum) {
	var commonDigits = 0;
	var leftHighest = GH.numUtil.mostSignificantDigit(leftNum);
	var rightHighest = GH.numUtil.mostSignificantDigit(rightNum);
	while (leftHighest == rightHighest) {
		commonDigits += leftHighest;
		leftHighest = GH.numUtil.mostSignificantDigit(leftNum - commonDigits);
		rightHighest = GH.numUtil.mostSignificantDigit(rightNum - commonDigits);
	}
	// Handle case with common digits such as 125 > 123.
	if (commonDigits) {
		return this.addToBothSides(sexp, leftNum - commonDigits, rightNum - commonDigits, commonDigits);
	}
	// Handle round numbers like 80 > 30.
	if ((leftNum - leftHighest == 0) && (rightNum - rightHighest == 0)) {
		var leftDigits  = GH.numUtil.numOfDigits(leftNum);
		var rightDigits = GH.numUtil.numOfDigits(rightNum);
		var base = Math.pow(10, GH.numUtil.numOfDigits(rightNum) - 1);
	    if ((leftDigits == rightDigits) ||
		   ((leftDigits - 1 == rightDigits) && (leftNum / base == 10))) {
			return this.roundNumbers(sexp, leftNum, rightNum);
		}
	}
	return this.arbitraryNumbers(sexp, leftNum, rightNum);
};

GH.ProofGenerator.evaluatorGreaterThan.prototype.roundNumbers = function(sexp, leftNum, rightNum) {
	var base = Math.pow(10, GH.numUtil.numOfDigits(rightNum) - 1);
	var leftMultiplier  = leftNum  / base;
	var rightMultiplier = rightNum / base;

	var multiplierInequality = this.prover.create('>', [leftMultiplier, rightMultiplier]);
	var baseInequality = this.prover.create('>', [base, 0]);
	this.prover.openExp(sexp, 'Highest Digit Inequality');
	this.prover.evaluate(multiplierInequality);
	this.prover.closeExp(sexp);
	this.prover.evaluate(baseInequality);
	this.prover.print([], 'gtmul2i');
	var result = this.prover.getLast();
	return this.prover.evaluate(result.right());	// For simplifying, 1 * 10 < 50 to 10 < 50
};

GH.ProofGenerator.evaluatorGreaterThan.prototype.close = function(result) {
	if (result) {
		return this.prover.closeExp(result);
	} else {
		return this.prover.getLast().right();
	}
};

GH.ProofGenerator.evaluatorGreaterThan.prototype.arbitraryNumbers = function(sexp, leftNum, rightNum) {
	var base = Math.pow(10, GH.numUtil.numOfDigits(leftNum) - 1);
	var rightResult = leftNum;
	var result = null;
	
	var roundDown = GH.numUtil.mostSignificantDigit(leftNum);
	if (rightResult > roundDown) {
		this.prover.evaluate(this.prover.create('>', [rightResult, roundDown]), 'Number Get Lower Rounding Down');
		rightResult = roundDown;
		result = this.close(result);
		result = this.prover.evaluate(result);
	}
	
	if (rightResult > base) {
		result = result && this.prover.openExp(result, 'First Digit is Lower');
		this.prover.evaluate(this.prover.create('>', [rightResult, base]));
		var tmpResult = this.prover.getLast().right();
		tmpResult = this.prover.evaluate(tmpResult);
		rightResult = base;
		result = this.close(result);
	}
	
	while ((base / 10 >= rightNum) && (base > 1)) {
		result = result && this.prover.openExp(result, 'Fewer Digits');
		base /= 10;
		this.prover.evaluate(this.prover.create('>', [rightResult, base]));
		rightResult = base;
		result = this.close(result);
	}
	if ((rightNum != base) && (base > 10)) {
		result = result && this.prover.openExp(result, 'First Digit is Lower');
		base /= 10;
		var rightMultiplier  = Math.floor(rightNum  / base);
		var newNum = (rightMultiplier + 1) * base;
		this.addToBothSides(sexp, rightResult - newNum, 0, newNum);
		rightResult = newNum;
		result = this.close(result);
	}
	if (rightNum != rightResult) {
		result = result && this.prover.openExp(result, 'Lower Remaining Digits');
		result = this.addToBothSides(sexp, rightResult - rightNum, 0, rightNum);
		result = this.close(result);
	}
	if (result.parent) {
		result = result.parent;
	}
	return result;
};

GH.ProofGenerator.evaluatorGreaterThan.prototype.canAddTheorem = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return ((rightNum <= 10) && (leftNum <= 10) && (leftNum > rightNum));
};

GH.ProofGenerator.evaluatorGreaterThan.prototype.theoremName = function(sexp) {
	return 'One-Digit Inequality';
};

GH.ProofGenerator.evaluatorGreaterThan.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return leftNum > rightNum;
};

