GH.ProofGenerator.evaluatorLessThanEqual = function(prover) {
  this.prover = prover;
  this.operators = ['<='];
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (leftNum == 0) {
		return new GH.action('0le', [GH.numUtil.createNum(rightNum)]);
	}
	if (leftNum <= rightNum) {
		operatorName = 'lessEq';
	} else {
		operatorName = 'greater';
	}
	return new GH.action(leftNum + operatorName + rightNum, []);
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.inline = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if ((rightNum == 0) && (leftNum > 0)) {
		return this.numMoreThanZero(sexp);
	} else if (leftNum < rightNum) {
		this.prover.evaluate(GH.operatorUtil.create('<', [sexp.left(), sexp.right()]));
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '<=');
	} else if (leftNum == rightNum) {
		this.prover.evaluate(GH.operatorUtil.create('=', [sexp.left(), sexp.right()]));
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '<=');
	} else if (leftNum > rightNum) {
		if ((leftNum <= 10) && (rightNum <= 10)) {
			return this.addToBothSides(sexp, leftNum - rightNum, 0, rightNum);
		} else {
			return this.inequality(sexp, leftNum, rightNum);
		}
	} 
	return null;
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.numMoreThanZero = function(sexp) {
	var equality = GH.operatorUtil.create('=',  [sexp.left(), sexp.right()]);
	var less     = GH.operatorUtil.create('<', [sexp.left(), sexp.right()]);
	this.prover.evaluate(equality, 'Number Not Zero');
	sexp = this.prover.openExp(sexp, 'Greater Than Or Equal To Zero');
	this.prover.evaluate(less);
	sexp = this.prover.closeExp(sexp);
	this.prover.print([], 'axgrtrii');
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.addToBothSides = function(sexp, leftNum, rightNum, addition) {
	var inequality = GH.operatorUtil.create('<=', [leftNum, rightNum]);   // leftNum > rightNum
	this.prover.openExp(sexp, 'Add To Both Sides');
	this.prover.openExp(sexp, 'Derive Smaller Inequality');
	this.prover.evaluate(inequality);
	this.prover.closeExp(sexp);

	this.prover.openExp(sexp, 'Add To Both Sides');
	var addExp = GH.numUtil.createNum(addition);
	this.prover.print([addExp], 'gtadd2i');
	this.prover.closeExp(sexp);
	result = this.prover.getLast();
	result = this.prover.evaluate(result.child().left(), 'Simplify Left Side').parent.parent;
	result = this.prover.evaluate(result.child().right(), 'Simplify Right Side').parent.parent;
	return this.prover.closeExp(result);
};

// TODO: Merge this with lessThan.
GH.ProofGenerator.evaluatorLessThanEqual.prototype.inequality = function(sexp, leftNum, rightNum) {
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

GH.ProofGenerator.evaluatorLessThanEqual.prototype.roundNumbers = function(sexp, leftNum, rightNum) {
	var base = Math.pow(10, GH.numUtil.numOfDigits(rightNum) - 1);
	var leftMultiplier  = leftNum  / base;
	var rightMultiplier = rightNum / base;

	var multiplierInequality = GH.operatorUtil.create('<=', [leftMultiplier, rightMultiplier]);
	var baseInequality = GH.operatorUtil.create('<=', [base, 0]);
	this.prover.openExp(sexp, 'Highest Digit Inequality');
	this.prover.evaluate(multiplierInequality);
	this.prover.closeExp(sexp);
	this.prover.evaluate(baseInequality);
	this.prover.print([], 'gtmul2i');
	var result = this.prover.getLast();
	return this.prover.evaluate(result.child().right());	// For simplifying, 1 * 10 < 50 to 10 < 50
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.close = function(result) {
	if (result) {
		return this.prover.closeExp(result);
	} else {
		return this.prover.getLast().child().right();
	}
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.arbitraryNumbers = function(sexp, leftNum, rightNum) {
	var base = Math.pow(10, GH.numUtil.numOfDigits(leftNum) - 1);
	var rightResult = leftNum;
	var result = null;
	
	var roundDown = GH.numUtil.mostSignificantDigit(leftNum);
	if (rightResult > roundDown) {
		this.prover.evaluate(GH.operatorUtil.create('<=', [rightResult, roundDown]));
		rightResult = roundDown;
		result = this.close(result);
		result = this.prover.evaluate(result);
		result = this.prover.openExp(result);
	}
	
	if (base >= rightNum) {
		this.prover.evaluate(GH.operatorUtil.create('<=', [rightResult, base]));
		result = this.prover.getLast().child().right();
		result = this.prover.evaluate(result);
		result = this.close(result);
		result = this.prover.openExp(result);
		rightResult = base;
	}
	
	while (base / 10 >= rightNum) {
		base /= 10;
		this.prover.evaluate(GH.operatorUtil.create('<=', [rightResult, base]));
		rightResult = base;
		result = this.close(result);
		result = this.prover.openExp(result);
	}
	if ((rightNum != base) && (base > 10)) {
		base /= 10;
		var rightMultiplier  = Math.floor(rightNum  / base);
		var newNum = (rightMultiplier + 1) * base;
		result = this.addToBothSides(sexp, rightResult - newNum, 0, newNum);
		result = this.close(result);
		result = this.prover.openExp(result);
		rightResult = newNum;
		//result = this.prover.openExp(result.right());
	}
	if (rightNum != rightResult) {
		if (!result) {
			result = this.prover.openExp(sexp	);
		}
		result = this.addToBothSides(sexp, rightResult - rightNum, 0, rightNum);
	}
	result = this.close(result);
	if (result.parent) {
		result = result.parent;
	}
	return result;
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorLessThanEqual.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return leftNum <= rightNum;
};
