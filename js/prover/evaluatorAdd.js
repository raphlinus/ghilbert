GH.ProofGenerator.evaluatorAdd = function(prover) {
  this.prover = prover;
};

GH.ProofGenerator.evaluatorAdd.prototype.stepName = function(sexp) {
	var leftNum  = GH.numUtil.decimalNumberSexp(sexp.left());
	var rightNum = GH.numUtil.decimalNumberSexp(sexp.right());

	if (leftNum == 0) {
		return 'pa_ax3r';
	}
	if (rightNum == 0) {
		return 'pa_ax3';
	}

	return leftNum + 'plus' + rightNum;
};

GH.ProofGenerator.evaluatorAdd.prototype.isApplicable = function(sexp) {
	// TODO: Change all of this to always apply unless there is a variable.
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());
	if (isNaN(leftNum) || isNaN(rightNum)) {
		return false;
	}
	// If the full expression already is a decimal number, there is nothing to evaluate.
	if (!isNaN(GH.numUtil.decimalNumberSexp(sexp))) {
		return false;
	}
	return true;
};

GH.ProofGenerator.evaluatorAdd.prototype.hyps = function(sexp) {
	var leftNum  = GH.numUtil.decimalNumberSexp(sexp.left());
	var rightNum = GH.numUtil.decimalNumberSexp(sexp.right());

	if (leftNum == 0) {
		return [sexp.right()];
	}
	if (rightNum == 0) {
		return [sexp.left()];
	}
	return [];
};

GH.ProofGenerator.evaluatorAdd.prototype.canAddTheorem = function(sexp) {
	var leftNum  = GH.numUtil.decimalNumberSexp(sexp.left());
	var rightNum = GH.numUtil.decimalNumberSexp(sexp.right());
	return ((1 < rightNum) && (rightNum <= 10) && (1 <= leftNum) && (leftNum <= 10));
};

GH.ProofGenerator.evaluatorAdd.prototype.addTheorem = function(sexp) {	
	var leftNum  = GH.numUtil.decimalNumberSexp(sexp.left());
	var rightNum = GH.numUtil.decimalNumberSexp(sexp.right());
	var sum = leftNum + rightNum;
	this.prover.println('## <title> One-digit Addition </title>');
	this.prover.println('thm (' + this.stepName(sexp) + ' () () (= ' + sexp.toString() + ' ' + GH.numUtil.numToSexpString(sum) + ')');
	this.prover.depth++;
	this.inline(sexp);
	this.prover.depth--;
	this.prover.println(')');
};

GH.ProofGenerator.evaluatorAdd.sameDigits = function(leftNum, rightNum) {
	var leftDigits  = GH.numUtil.numOfDigits(leftNum);
	var rightDigits = GH.numUtil.numOfDigits(rightNum);
	var base10 = Math.pow(10, leftDigits - 1);
	return (leftDigits == rightDigits) && (leftNum % base10 == 0) && (rightNum % base10 == 0);
};

GH.ProofGenerator.evaluatorAdd.prototype.inline = function(sexp) {
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

	if (leftNum == 0) {
		return false;
	} else if (rightNum == 0) {
		return false;
	} else if ((leftNum == 1) && (rightNum < 10)) {
		this.successorRight_(rightNum);
	} else if ((rightNum == 1) && (leftNum < 10)) {
		this.successorLeft_(leftNum);
	} else if ((rightNum == 10) && (leftNum < 10)) {
		this.prover.commute(sexp);
	} else if ((rightNum < 10) && (leftNum < 10)) {
		this.addSingleDigits_(sexp, leftNum, rightNum);
	} else {
		this.addNumbers_(sexp)
	}
	return true;
};

// Replace a single-digit number on the left with its successor.
// For example, 4 + 1 = 5.
// TODO: Make sure the symbols are defined.
GH.ProofGenerator.evaluatorAdd.prototype.successorLeft_ = function(leftNum) {
	this.prover.print([], 'df-' + (leftNum + 1));
	var result = this.prover.getLast();
	return this.prover.commute(result);
};

// Replace a single-digit number on the left with its successor.
// For example, 1 + 4 = 5.	
GH.ProofGenerator.evaluatorAdd.prototype.successorRight_ = function(rightNum) {
	this.prover.print([], 'df-' + (rightNum + 1));
	var replacement = this.prover.getLast();
	replacement = this.prover.applyRight(this.prover.commute, replacement);
	return this.prover.commute(replacement);
};

// Replace a single-digit number with its predessor on the left.
// For example, 5 = 4 + 1.
GH.ProofGenerator.evaluatorAdd.prototype.predecessorLeft_ = function(sexp) {
	var num = sexp.operator;
	this.prover.print([], 'df-' + num);
	return this.prover.replace(sexp);
};

// Replace a single-digit number with its predecessor on the right.
// For example, 5 = 1 + 4.
GH.ProofGenerator.evaluatorAdd.prototype.predecessorRight_ = function(sexp) {
	var num = sexp.operator;
	this.prover.print([], 'df-' + num);
	var replacement = this.prover.getLast();
	this.prover.commute(replacement.right());
	return this.prover.replace(sexp);
};

// Increment the left number and decrement the right.
// For example, 5 + 3 = 6 + 2.
GH.ProofGenerator.evaluatorAdd.prototype.incrementLeft_ = function(sexp) {
	var leftNum  = GH.numUtil.decimalNumberSexp(sexp.left());
	var result = sexp.copy();
	result = GH.Prover.applyRight(this.predecessorRight_, result, this);
	result = this.prover.associateLeft(result);
	this.successorLeft_(leftNum);
	return this.prover.replace(result.left()).parent;
};

// Increment the right number and decrement the left.
// For example, 5 + 3 = 4 + 4.
GH.ProofGenerator.evaluatorAdd.prototype.incrementRight_ = function(sexp) {
	var rightNum = GH.numUtil.decimalNumberSexp(sexp.right());
	var result = sexp.copy();	
	result = GH.Prover.applyLeft(this.predecessorLeft_, result, this);
	result = this.prover.associateRight(result);
	this.successorRight_(rightNum);
	return this.prover.replace(result.right()).parent;
};

// The body of the addSingleDigits proof generator. Takes an expression like 2 + 2
// and finds their sum: 2 + 2 = 4.
GH.ProofGenerator.evaluatorAdd.prototype.addSingleDigits_ = function(sexp, leftNum, rightNum) {
	this.prover.print([sexp.copy()], 'eqid');
	var result = this.prover.getLast().right();

	// We increment the higher number and decrement the lower number until
	// we've reach 10 or until the lower number is zero.
	if (rightNum < leftNum) {
		while ((rightNum > 0) && (leftNum < 10)) {
			if (rightNum > 1) {
				this.prover.applyHidden(this.incrementLeft_, result, this);
				result = this.prover.replace(result);
			} else {
				this.successorLeft_(leftNum);
				result = this.prover.replace(result);
			}
			rightNum--;
			leftNum++;
		}
	} else {
		while ((leftNum > 0) && (rightNum < 10)) {
			if (leftNum > 1) {
				this.prover.applyHidden(this.incrementRight_, result, this);
				result = this.prover.replace(result);
			} else {
				this.successorRight_(rightNum);
				result = this.prover.replace(result);
			}
			rightNum++;
			leftNum--;
		}
		if ((rightNum == 10) && (leftNum > 0)) {
			result = this.prover.commute(result);
		}
	}
	return result;
};

// Replace a number x with 1 * x.
GH.ProofGenerator.evaluatorAdd.prototype.multiplyByOneLeft = function(sexp) {
	if (((sexp.operator == '+') || (sexp.operator == '*')) && (sexp.left().operator == '1')) {
		return sexp;
	}
	// TODO: Clean this up.
	this.prover.print([sexp.copy()], 'mulid');
	this.prover.print([], 'eqcomi');
	this.prover.commute(this.prover.getLast().right());
	return this.prover.replace(sexp);
};


// Multiply the powers of ten by 1. For example: 100 + 8 = 1 * 100 + 8.
GH.ProofGenerator.evaluatorAdd.prototype.multiplyTensByOne = function(sexp) {
	if (((sexp.operator == '*') && (sexp.left().operator == '10')) || (sexp.operator == '10')) {
		return this.multiplyByOneLeft(sexp);
	} else if (sexp.operator == '+') {
		var result = GH.Prover.applyLeft(this.multiplyTensByOne, sexp, this);
		return GH.Prover.applyRight(this.multiplyTensByOne, result, this);
	} else {
		return sexp;
	}
};

// Find a symbol tree describing how the digits are currently arranged.
GH.ProofGenerator.evaluatorAdd.findOriginalTree = function(sexp, digitTable) {
	if (sexp.operator == '+') {
		return new GH.symbolTree(
		    null, 
		    GH.ProofGenerator.evaluatorAdd.findOriginalTree(sexp.left(), digitTable),
			GH.ProofGenerator.evaluatorAdd.findOriginalTree(sexp.right(), digitTable));
	} else {
		var num = GH.numUtil.sexpToNum(sexp);
		var symbol = String.fromCharCode(65 + digitTable.length);
		digitTable.push([symbol, num]);
		return new GH.symbolTree(symbol, null, null);
	}
};

// Create a new symbol tree with similar digits the organized together.
GH.ProofGenerator.evaluatorAdd.calculateNewTree = function(digitTable, originalTree) {
	var threshold = 10;
	var newBranches = [];
	while(digitTable.length > 0) {
		var newBranch = null;
		for (var i = 0; i < digitTable.length; i++) {
			if (digitTable[i][1] < threshold) {
				var symbol = digitTable.splice(i, 1)[0][0];
				var addition = new GH.symbolTree(symbol, null, null);
				newBranch = GH.symbolTree.addTrees(newBranch, addition, true);
				i--;
			}
		}
		newBranches.push(newBranch);
		threshold *= 10;
	}
	// Reverse the order to make the parantheses look cleaner.
	newBranches.reverse();
	var newTree = null;
	for (var i = 0; i < newBranches.length; i++) {
		newTree = GH.symbolTree.addTrees(newTree, newBranches[i], true);
	}
	return newTree;
};

// Reorganize the numbers so that common digits are together. For example: 45 + 67 = (40 + 60) + (5 + 7)
GH.ProofGenerator.evaluatorAdd.prototype.reorganizeDigits_ = function(sexp) {
	var digitTable = [];
	var originalTree = GH.ProofGenerator.evaluatorAdd.findOriginalTree(sexp, digitTable);
	var newTree = GH.ProofGenerator.evaluatorAdd.calculateNewTree(digitTable, originalTree);

	var result = this.prover.repositioner.repositionTree(sexp, originalTree, newTree);
	result = this.multiplyTensByOne(result);
	return this.undistributeAllLeft_(result);
};

// Add two arbitrary numbers.
GH.ProofGenerator.evaluatorAdd.prototype.addNumbers_ = function(sexp) {
	this.prover.print([sexp.copy()], 'eqid');
	sexp = this.prover.getLast().right();
	sexp = this.reorganizeDigits_(sexp);
	sexp = this.addIndividualDigits_(sexp);
	return this.addCleanUp_(sexp);
};

// Undistribute to the left all additions when possible.
GH.ProofGenerator.evaluatorAdd.prototype.undistributeAllLeft_ =  function(sexp) {
	var result = this.prover.undistributeLeft(sexp);
	if (sexp.operator == '+') {
		result = GH.Prover.applyLeft(this.undistributeAllLeft_, result, this);
		return GH.Prover.applyRight(this.undistributeAllLeft_, result, this);
	} else {
		return result;
	}
};

// Find the lowest digits that still need to be added together.
GH.ProofGenerator.evaluatorAdd.getNextDigitsToAdd_ = function(sexp) {
	if (sexp.operator == '+') {
		var leftNum  = GH.numUtil.decimalNumberSexp(sexp.left());
		var rightNum = GH.numUtil.decimalNumberSexp(sexp.right());
		if ((leftNum < 10) && (rightNum < 10)) {
			return sexp;
		}
		var nextDigits = GH.ProofGenerator.evaluatorAdd.getNextDigitsToAdd_(sexp.right());
		return nextDigits || GH.ProofGenerator.evaluatorAdd.getNextDigitsToAdd_(sexp.left());
	} else if (sexp.operator == '*') {
		return GH.ProofGenerator.evaluatorAdd.getNextDigitsToAdd_(sexp.left());
	} else {
		return null;
	}
};

// Add the individual digits together.
GH.ProofGenerator.evaluatorAdd.prototype.addIndividualDigits_ =  function(sexp) {
	var originalSexp = sexp;
	sexp = sexp.copy();
	var nextDigitsToAdd = GH.ProofGenerator.evaluatorAdd.getNextDigitsToAdd_(sexp);
	if (!nextDigitsToAdd) {
		return originalSexp;
	}

	while (nextDigitsToAdd) {
		// Perform the addition.
		sexp = this.prover.evaluate(nextDigitsToAdd);
		var carry = false;
		// Grab the number being carried if there is one and move it out of the lower digit.
		if (sexp.operator == '10') {
			carry = true;
			if (sexp.parent.operator == '*') {
				sexp = sexp.parent;
			}
		} else if (sexp.operator == '+') {
			carry = true;
			if (sexp.parent.operator == '*') {
				sexp = this.prover.distributeLeft(sexp.parent);
			}
			if ((sexp.parent.operator == '+') && (sexp.siblingIndex == 1)) {
				sexp = this.prover.associateLeft(sexp.parent).left().right();
			}
		}

		// Move the carry into the higher digit.
		if (carry && sexp.parent.operator == '+'){
			sexp = this.multiplyTensByOne(sexp).parent;
			if (sexp.left().operator == '+') {
				sexp = this.prover.associateRight(sexp).right();
			}
			sexp = this.prover.undistributeLeft(sexp);
			sexp = this.prover.associateRight(sexp.left());
		}

		while (sexp.parent.operator != '=') {
			sexp = sexp.parent;
		}
		nextDigitsToAdd = GH.ProofGenerator.evaluatorAdd.getNextDigitsToAdd_(sexp);
	}
	
	sexp = this.prover.replace(originalSexp);
	return sexp;
};

// Associate right all additions and simplify one multiplications: 1 * 10 = 10.
GH.ProofGenerator.evaluatorAdd.prototype.addCleanUp_ =  function(sexp) {
	while ((sexp.operator == '+') && (sexp.left().operator == '+')) {
		sexp = this.prover.associateRight(sexp);
	}
	if ((sexp.operator == '*') && (sexp.left().operator == '1')) {
		sexp = this.prover.evaluate(sexp);
	}
	if ((sexp.operator == '*') || (sexp.operator == '+')) {
		sexp = GH.Prover.applyLeft(this.addCleanUp_, sexp, this);
		sexp = GH.Prover.applyRight(this.addCleanUp_, sexp, this);
	}
	return sexp;
};