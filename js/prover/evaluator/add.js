GH.ProofGenerator.evaluatorAdd = function(prover) {
  this.prover = prover;
  this.operators = ['+'];
};

GH.ProofGenerator.evaluatorAdd.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());

	if (leftNum == 0) {
		return new GH.action('pa_ax3r', [sexp.right()]);
	}
	if (rightNum == 0) {
		return new GH.action('pa_ax3', [sexp.left()]);
	}
	if (!GH.numUtil.isReduced(sexp.left()) || (!GH.numUtil.isReduced(sexp.right()))) {
		return new GH.action(null, []);
	}
	return new GH.action(leftNum + 'plus' + rightNum, []);
};

GH.ProofGenerator.evaluatorAdd.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorAdd.prototype.canAddTheorem = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return ((1 < rightNum) && (rightNum <= 10) && (1 <= leftNum) && (leftNum <= 10) &&
	        GH.numUtil.isReduced(sexp.left()) && GH.numUtil.isReduced(sexp.right()));
};

GH.ProofGenerator.evaluatorAdd.prototype.addTheorem = function(sexp) {	
	var sum = this.calculate(sexp);
	sexp = sexp.copy();
	this.prover.println('## <title> One-digit Addition </title>');
	this.prover.println('thm (' + this.action(sexp).name + ' () () (= ' + sexp.toString() + ' ' + GH.numUtil.numToSexpString(sum) + ')');
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
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());

	if (leftNum == 0) {
		return false;
	} else if (rightNum == 0) {
		return false;
	} else if ((leftNum == 1) && (rightNum < 10)) {
		return this.successorRight_(rightNum);
	} else if ((rightNum == 1) && (leftNum < 10)) {
		return this.successorLeft_(leftNum);
	} else if ((rightNum == 10) && (leftNum < 10)) {
		return this.prover.commute(sexp);
	} else if ((rightNum < 10) && (leftNum < 10)) {
		return this.addSingleDigits_(sexp, leftNum, rightNum);
	} else {
		return this.addNumbers_(sexp)
	}
	return false;
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
	replacement = this.prover.commute(replacement.right()).parent;
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
	var result = this.prover.openExp(sexp, 'Increment Left');
	result = GH.Prover.applyRight(this.predecessorRight_, result, this);
	result = this.prover.associateLeft(result);
	var name = 'Definition of ' + this.prover.calculate(result.left());
	result = this.prover.evaluate(result.left(), name).parent;
	return this.prover.closeExp(result);
};

// Increment the right number and decrement the left.
// For example, 5 + 3 = 4 + 4.
GH.ProofGenerator.evaluatorAdd.prototype.incrementRight_ = function(sexp) {
	var result = this.prover.openExp(sexp, 'Increment Right');
	result = GH.Prover.applyLeft(this.predecessorLeft_, result, this);
	result = this.prover.associateRight(result);
	var name = 'Definition of ' + this.prover.calculate(result.right());
	result = this.prover.evaluate(result.right(), name).parent;
	return this.prover.closeExp(result);
};

// The body of the addSingleDigits proof generator. Takes an expression like 2 + 2
// and finds their sum: 2 + 2 = 4.
GH.ProofGenerator.evaluatorAdd.prototype.addSingleDigits_ = function(sexp, leftNum, rightNum) {
	sexp = this.prover.openExp(sexp, 'One-digit Addition');
	// this.prover.print([sexp], 'eqid');
	// var result = this.prover.getLast().right();
	var result = sexp;

	// We increment the higher number and decrement the lower number until
	// we've reach 10 or until the lower number is zero.
	if (rightNum < leftNum) {
		while ((rightNum > 0) && (leftNum < 10)) {
			if (rightNum > 1) {
				result = this.incrementLeft_(result);
			} else {
				var name = 'Definition of ' + this.prover.calculate(result);
				this.prover.evaluate(result, name);
			}
			rightNum--;
			leftNum++;
		}
	} else {
		while ((leftNum > 0) && (rightNum < 10)) {
			if (leftNum > 1) {
				result = this.incrementRight_(result);
			} else {
				var name = 'Definition of ' + this.prover.calculate(result);
				this.prover.evaluate(result, name);
			}
			rightNum++;
			leftNum--;
		}
		if ((rightNum == 10) && (leftNum > 0)) {
			result = this.prover.commute(result);
		}
	}
	return this.prover.closeExp(result);
};

// Replace a number x with 1 * x.
GH.ProofGenerator.evaluatorAdd.prototype.multiplyByOneLeft = function(sexp) {
	if (((sexp.operator == '+') || (sexp.operator == '*')) && (sexp.left().operator == '1')) {
		return sexp;
	}
	return this.prover.unevaluate(GH.operatorUtil.create('*', [1, sexp]), sexp);
};


// Multiply the powers of ten by 1. For example: 100 + 8 = 1 * 100 + 8.
GH.ProofGenerator.evaluatorAdd.prototype.multiplyTensByOne = function(sexp) {
	sexp = this.prover.openExp(sexp, 'Multiply By One');
	if (((sexp.operator == '*') && (sexp.left().operator == '10')) || (sexp.operator == '10')) {
		sexp = this.multiplyByOneLeft(sexp);
	} else if (sexp.operator == '+') {
		sexp = GH.Prover.applyLeft(this.multiplyTensByOne, sexp, this);
		sexp = GH.Prover.applyRight(this.multiplyTensByOne, sexp, this);
	}
	return this.prover.closeExp(sexp);
};

// Find a symbol tree describing how the digits are currently arranged.
GH.ProofGenerator.evaluatorAdd.prototype.findOriginalTree = function(sexp, digitTable) {
	if (sexp.operator == '+') {
		return new GH.symbolTree(
		    null, 
		    this.findOriginalTree(sexp.left(), digitTable),
			this.findOriginalTree(sexp.right(), digitTable));
	} else {
		var num = this.prover.calculate(sexp);
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
	sexp = this.prover.openExp(sexp, 'Group Common Digits');
	var digitTable = [];
	var originalTree = this.findOriginalTree(sexp, digitTable);
	var newTree = GH.ProofGenerator.evaluatorAdd.calculateNewTree(digitTable, originalTree);

	var result = this.prover.repositioner.repositionTree(sexp, originalTree, newTree);
	result = this.multiplyTensByOne(result);
	result = this.undistributeAllLeft_(result);
	return this.prover.closeExp(result);
	
};

// Add two arbitrary numbers.
GH.ProofGenerator.evaluatorAdd.prototype.addNumbers_ = function(sexp) {
	sexp = this.prover.openExp(sexp, 'Addition');
	//this.prover.print([sexp], 'eqid');
	//sexp = this.prover.getLast().right();
	
	sexp = this.reorganizeDigits_(sexp);
	sexp = this.addIndividualDigits_(sexp);
	sexp = this.addCleanUp_(sexp);
	return this.prover.closeExp(sexp);
};

// Undistribute to the left all additions when possible.
GH.ProofGenerator.evaluatorAdd.prototype.undistributeAllLeft_ =  function(sexp) {
	var result = this.prover.undistributeLeft(sexp);
	if (sexp.operator == '+') {
		result = GH.Prover.applyLeft(this.undistributeAllLeft_, result, this);
		result = GH.Prover.applyRight(this.undistributeAllLeft_, result, this);
	}
	return result;
};

GH.ProofGenerator.evaluatorAdd.hasMultiplication = function(sexp) {
	if (sexp.operator == '*') {
		return true;
	} else if (sexp.operator == '+') {
		return GH.ProofGenerator.evaluatorAdd.hasMultiplication(sexp.left()) ||
			   GH.ProofGenerator.evaluatorAdd.hasMultiplication(sexp.right());
	} else {
		return false;
	}
};

// Find the lowest digits that still need to be added together.
GH.ProofGenerator.evaluatorAdd.prototype.getNextDigitsToAdd_ = function(sexp) {
	if (sexp.operator == '+') {
		if (!GH.ProofGenerator.evaluatorAdd.hasMultiplication(sexp)) {
			return sexp;
		}
		var nextDigits = this.getNextDigitsToAdd_(sexp.right());
		return nextDigits || this.getNextDigitsToAdd_(sexp.left());
	} else if (sexp.operator == '*') {
		return this.getNextDigitsToAdd_(sexp.left());
	} else {
		return null;
	}
};

GH.ProofGenerator.evaluatorAdd.prototype.addIndividualDigits_ =  function(sexp) {
	var nextDigitsToAdd = this.getNextDigitsToAdd_(sexp);
	while (nextDigitsToAdd) {
		sexp = this.prover.evaluate(nextDigitsToAdd, 'Single-digit Addition');
		if (this.prover.calculate(sexp) >= 10) {
			sexp = this.carry_(sexp);
		}
		while (sexp.parent.operator != '=') {
			sexp = sexp.parent;
		}
		nextDigitsToAdd = this.getNextDigitsToAdd_(sexp);
	}
	return sexp;
};

// Add the individual digits together.
GH.ProofGenerator.evaluatorAdd.prototype.carry_ =  function(sexp) {
	// Open the expression further up so we can complete the carrying.
	var position = [];
	if (sexp.parent.operator == '*') {
		position.push(sexp.siblingIndex);
		sexp = sexp.parent;
	}
	if (sexp.parent.operator == '+') {
		position.push(sexp.siblingIndex);
		sexp = sexp.parent;
	}
	sexp = this.prover.openExp(sexp, 'Carry the One');
	while (position.length > 0) {
		sexp = sexp.operands[position.pop()];
	}
	
	// Grab the number being carried if there is one and move it out of the lower digit.
	if (sexp.operator == '10') {
		if (sexp.parent.operator == '*') {
			sexp = sexp.parent;
		}
	} else if (sexp.operator == '+') {
		if (sexp.parent.operator == '*') {
			sexp = this.prover.distributeLeft(sexp.parent);
		}
		if ((sexp.parent.operator == '+') && (sexp.siblingIndex == 1)) {
			sexp = this.prover.associateLeft(sexp.parent).left().right();
		}
	}

	// Move the carry into the higher digit.
	if (sexp.parent && sexp.parent.operator == '+'){
		sexp = this.multiplyTensByOne(sexp).parent;
		if (sexp.left().operator == '+') {
			sexp = this.prover.associateRight(sexp).right();
		}
		sexp = this.prover.undistributeLeft(sexp);
		// sexp = this.prover.associateRight(sexp.left());
	}
	return this.prover.closeExp(sexp);
};

// Associate right all additions and simplify one multiplications: 1 * 10 = 10.
GH.ProofGenerator.evaluatorAdd.prototype.addCleanUp_ =  function(sexp) {
	sexp = this.prover.openExp(sexp, 'Simplify');
	while ((sexp.operator == '+') && (sexp.left().operator == '+')) {
		sexp = this.prover.associateRight(sexp);
	}
	if ((sexp.operator == '*') && (sexp.left().operator == '1')) {
		sexp = this.prover.evaluate(sexp, 'Multiplicative Identity');
	}
	if ((sexp.operator == '*') || (sexp.operator == '+')) {
		sexp = GH.Prover.applyLeft(this.addCleanUp_, sexp, this);
		sexp = GH.Prover.applyRight(this.addCleanUp_, sexp, this);
	}
	return this.prover.closeExp(sexp);
};

GH.ProofGenerator.evaluatorAdd.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return leftNum + rightNum;
};