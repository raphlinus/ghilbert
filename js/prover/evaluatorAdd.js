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
		return 'pa_ax3'
	}

	return leftNum + 'plus' + rightNum;
};

GH.ProofGenerator.evaluatorAdd.prototype.isApplicable = function(sexp) {
	// TODO: Change all of this to always apply unless there is a variable.
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());
	if (isNaN(leftNum) || isNaN(rightNum)) {
		return false
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

GH.ProofGenerator.evaluatorAdd.prototype.addTheorem = function(sexp) {
	return false;
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

	if (isNaN(leftNum)) {
		sexp = this.prover.replaceLeft(this.prover.evaluator, sexp);
		return this.prover.replaceWith(this.prover.evaluator, sexp);
	}
	if (isNaN(rightNum)) {
		sexp = this.prover.replaceRight(this.prover.evaluator, sexp);
		return this.prover.replaceWith(this.prover.evaluator, sexp);
	}

	if (leftNum == 0) {
		return false;
	} else if (rightNum == 0) {
		return false;
	} else if ((leftNum == 1) && (rightNum > 0) && (rightNum < 10)) {
		this.successorRight_(rightNum);
	} else if ((rightNum == 1) && (leftNum > 0) && (leftNum < 10)) {
		this.successorLeft_(leftNum);
	} else if ((rightNum <= 10) && (leftNum <= 10)) {
		this.addSingleDigits_(sexp, leftNum, rightNum);
	} else if (GH.ProofGenerator.evaluatorAdd.sameDigits(leftNum, rightNum)) {
		this.addHigherDigits_(sexp, leftNum, rightNum);
	} else {
		this.addTwoNumbers_(sexp)
	}
	return true;
};

// Replace a single-digit number on the left with its successor.
// For example, 4 + 1 = 5.
// TODO: Make sure the symbols are defined.
GH.ProofGenerator.evaluatorAdd.prototype.successorLeft_ = function(leftNum) {
	this.prover.print([], 'df-' + (leftNum + 1));
	var result = this.prover.getLast();
	this.prover.commute(result);
};

// Replace a single-digit number on the left with its successor.
// For example, 1 + 4 = 5.	
GH.ProofGenerator.evaluatorAdd.prototype.successorRight_ = function(rightNum) {
	this.prover.print([], 'df-' + (rightNum + 1));
	var replacement = this.prover.getLast();
	replacement = this.prover.applyRight(this.prover.commute, replacement);
	this.prover.commute(replacement);
};

// Replace a single-digit number with its predessor on the left.
// For example, 5 = 4 + 1.
GH.ProofGenerator.evaluatorAdd.prototype.predecessorLeft_ = function(sexp) {
	var num = sexp.operator_;
	this.prover.print([], 'df-' + num);
	return this.prover.replace(sexp);
};

// Replace a single-digit number with its predecessor on the right.
// For example, 5 = 1 + 4.
GH.ProofGenerator.evaluatorAdd.prototype.predecessorRight_ = function(sexp) {
	var num = sexp.operator_;
	this.prover.print([], 'df-' + num);
	var replacement = this.prover.getLast();
	this.prover.commute(replacement.right());
	return this.prover.replace(sexp);
};

// The body of the addSingleDigits proof generator. Takes an expression like 2 + 2
// and finds their sum: 2 + 2 = 4.
GH.ProofGenerator.evaluatorAdd.prototype.addSingleDigits_ = function(sexp, leftNum, rightNum) {
	var result = sexp.copy();

	// We increment the higher number and decrement the lower number until
	// we've reach 10 or until the lower number is zero.
	if (rightNum < leftNum) {
		while ((rightNum > 0) && (leftNum < 10)) {
			if (rightNum > 1) {
				result = GH.Prover.applyRight(this.predecessorRight_, result, this);
				result = this.prover.associateLeft(result);
				this.successorLeft_(leftNum);
				result = this.prover.replace(result.left()).parent_;
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
				result = GH.Prover.applyLeft(this.predecessorLeft_, result, this);
				result = this.prover.associateRight(result);
				this.successorRight_(rightNum);
				result = this.prover.replace(result.right()).parent_;
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


// Adds two multi-digit numbers. This represents adding the 10's or 100's digit.
// Both numbers must have the same number of digits and only the highest digit can
// be non-zero. The numbers should be in long-form.
GH.ProofGenerator.evaluatorAdd.prototype.addHigherDigits_ = function(sexp) {
	var result = sexp.copy(null);                                     // Example:
	                                                                  // 5 * 10 + 6 * 10
	result = this.prover.undistributeLeft(result);                    // (5 + 6) * 10
	result = this.prover.replaceLeft(this.prover.evaluator, result);  // (10 + 1) * 10
	
	// If the result is a two digit number. Distribute the carry.
	if (result.left().operator_ == '+') {
		result = this.prover.distributeLeft(result);       // 10 * 10 +  1 * 10
	}
	return result;
};





// Replace a number x with 1 * x.
GH.ProofGenerator.evaluatorAdd.prototype.multiplyByOneLeft = function(sexp) {
	if (((sexp.operator_ == '+') || (sexp.operator_ == '*')) && (sexp.left().operator_ == '1')) {
		return sexp;
	}
	// TODO: Clean this up.
	this.prover.print([sexp.copy()], 'mulid');
	this.prover.print([], 'eqcomi');
	this.prover.commute(this.prover.getLast().right());
	return this.prover.replace(sexp);
};

// Computes the sum of two numbers. Both numbers are converted into a long form that is easier to compute
// with. The result is converted back into the short form.
GH.ProofGenerator.evaluatorAdd.prototype.addTwoNumbers_ = function(sexp) {
	var result = sexp;
	result = GH.Prover.applyLeft(this.numberLongForm, result, this);
	result = GH.Prover.applyRight(this.numberLongForm, result, this);
	result = this.addTwoLongFormNumbers(result);
	if (this.prover.evaluator.isApplicable(result)) {
		return this.prover.replaceWith(this.prover.evaluator, result);  // Evaluate to put the number back into short form.
	} else {
		return result;
	}
};

// Converts an s-expression representing a number in a long form. Digits with a 1 or 0 are expanded out.
// For example, 120 is normally represented as:   120 =     10 * 10 + 2 * 10. 
// In long-form it is represented as:             120 = 1 * 10 * 10 + 2 * 10 + 0.
GH.ProofGenerator.evaluatorAdd.prototype.numberLongForm = function(sexp) {
	var num = GH.numUtil.sexpToNum(sexp);
	var digits = GH.numUtil.numOfDigits(num);
	var result = sexp.copy();
	var rightEmpty = false;
	var depth = 0;
	var changed = false;
	for (var i = digits - 1; i >= 0; i--) {
		var value = Math.floor(num / Math.pow(10, i));
		num = num % Math.pow(10, i);

		if ((value == 1) && (i > 0)) {
			// If a digit has a value of 1, multipy it by 1.
			if ((result.operator_ == '+') ) {
				changed = true;
				result = GH.Prover.applyLeft(this.multiplyByOneLeft, result, this);
				result = result.right();
				depth++;
			} else if ((result.operator_ == '*') || (result.operator_ = '10')) {
				changed = true;
				result = this.multiplyByOneLeft(result);
			}
		} else if ((value > 1) && (result.operator_ == '+')) {
			result = result.right();
			depth++;
		} else if (value == 0) {
			changed = true;
			// If a digit has a value of 0, add zero times the base 10 number.
			if (num == 0) {
				// TODO: Stop duplicating zero digits everytime we go through this function.
				this.prover.print([result], 'pa_ax3')
				this.prover.print([], 'eqcomi');
				result = this.prover.replace(result);
				if (i > 0) {
					// TODO: Clean this up.
					this.prover.print([GH.numUtil.numToSexp(Math.pow(10, i))], 'pa_ax5r')
					this.prover.print([], 'eqcomi');
					result = this.prover.replace(result.right());
				} else {
					result = result.right();
					depth++;
				}
			} else {
				this.prover.print([result], 'pa_ax3r')
				this.prover.print([], 'eqcomi');
				result = this.prover.replace(result);
				if (i > 0) {
					this.prover.print([GH.numUtil.numToSexp(Math.pow(10, i))], 'pa_ax5r')
					this.prover.print([], 'eqcomi');
					result = this.prover.replace(result.left());
					result = result.parent_;
				}
				result = result.right();
				depth++;
			}
		}
	}
	if (changed) {
		return this.prover.replace(sexp);
	} else {
		return sexp;
	}
};

// Convert a number in long form back into the standard short form.
// Simplify multiplication and addition.
GH.ProofGenerator.evaluatorAdd.prototype.numberShortForm = function(sexp) {
	if (sexp.operator_ == '+') {
		var result = sexp;
		result = GH.Prover.applyLeft(this.numberShortForm, sexp, this);
		result = GH.Prover.applyRight(this.numberShortForm, result, this);
		return this.additiveIdentity(result);
	} else {
		return this.simplifyTimes(sexp);
	}
};

// Computes the sum of two numbers in long form.
GH.ProofGenerator.evaluatorAdd.prototype.addTwoLongFormNumbers = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());
	var leftDigits = GH.numUtil.getDigitNum(sexp.left());
	var rightDigits = GH.numUtil.getDigitNum(sexp.right());
	var maxDigits = Math.max(leftDigits, rightDigits);
		
	var digit = Math.pow(10, maxDigits - 1);
	var upperDigit = digit * 10;
	var lowerCarry = (((leftNum %      digit) + (rightNum %      digit)) / digit >= 1);
	var upperCarry = (((leftNum % upperDigit) + (rightNum % upperDigit)) / upperDigit >= 1);
	var lowerZero  = (((leftNum + rightNum) % upperDigit) / digit < 1);
				
	var result = sexp;
	if (leftDigits == 1 && rightDigits == 1) {
		result = this.prover.evaluate(result);
	} else if (leftDigits != rightDigits) {
		if (leftDigits > rightDigits) {
			result = this.prover.associateRight(result);
		} else {
			result = this.prover.reposition(result, 'A (B C)', 'B (A C)');
		}
		// TODO: Use evaluate instead.
		result = GH.Prover.applyRight(this.addTwoLongFormNumbers, result, this);
			
		// Handle a carry.
		if (lowerCarry) {
			result = this.prover.associateLeft(result);
			//result = this.prover.reposition(result, 'A (B C)', '(A B) C'); // Same as associateLeft
			// result = this.prover.replaceLeft(this.prover.evaluator, result);
			result = result.left();
			this.addHigherDigits_(result);
			result = this.prover.replace(result);
		}		
	} else if (leftDigits == rightDigits) {
		result = this.prover.reposition(result, '(A B) (C D)', '(A C) (B D)'); // This is the same as add4.
		result = GH.Prover.applyRight(this.addTwoLongFormNumbers, result, this);
	
		// Handle a carry.
		if (lowerCarry) {
			result = this.prover.reposition(result, '(A B) (carry D)', '(A (B carry)) D');
			result = result.left().right();
			// result = this.prover.replaceWith(this.prover.evaluator, result);
			this.addHigherDigits_(result);
			result = this.prover.replace(result);
			result = result.parent_.parent_;
		}
		//result = this.prover.replaceLeft(this.prover.evaluator, result);
		result = result.left();
		this.addHigherDigits_(result);
		result = this.prover.replace(result);
		result = result.parent_;

		if (upperCarry && !lowerZero) {
			result = this.prover.associateRight(result);
		}
	}
	result = this.numberLongForm(result);
	return result;
};
