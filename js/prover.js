// Javascript for generating Ghilbert proof steps automatically.
// by Paul Merrell, 2013

GH.Prover = function() {
	this.depth = 0;
};

GH.Prover.prototype.indent = function() {
	for (var i = 0; i < this.depth; i++) {
		window.direct.text.insertText('  ');
	}
};

// Print text into the proof and add a new line.
GH.Prover.insertText = function(text) {
	window.direct.text.insertText(text);
};

// Print text into the proof and add a new line.
GH.Prover.println = function(text) {
	window.direct.prover.indent();
	GH.Prover.insertText(text + '\n');
};

// Insert a known theorem into the proof with all it's mandatory hypotheses.
GH.Prover.print = function(mandHyps, step) {
	window.direct.prover.indent();
	for (var i = 0; i < mandHyps.length; i++) {
		GH.Prover.insertText(mandHyps[i].toString() + ' ');
	}
	GH.Prover.insertText(step + '\n');
};

// This is a bit of a hack.
GH.Prover.printBeforeLastStep = function(text) {
	var theorems = window.direct.update();
	var start = theorems[theorems.length - 1].begin;
	window.direct.text.splice(start, 0, text);
};

// Returns a list of the theorems from the stack. The list contains
// all the conclusions of theorems converted into s-expressions.
GH.Prover.getTheorems = function() {
	var theorems = window.direct.update();
	if (!theorems) {
		return [];
	}
	
	var result = [];
	for (var i = 0; i < theorems.length; i++) {
		// TODO: Rename public variables and make conclusion an s-expression.
		result.push(new GH.sExpression(theorems[i].conclusion, null, null));
	}
	return result;
};
	
// Return the last theorem on the proof stack.
GH.Prover.getLast = function() {
	var theorems = GH.Prover.getTheorems();
	return theorems[theorems.length -  1];
};
	
// Convert from a number to an s-expression. Only the numbers 0 to 10 are defined
// in Ghilbert, so multi-digit numbers are formed by combining these digits according
// to the standard base-10 numbering system.
GH.Prover.numToSexp = function(num) {
	if (num < 0) {
		alert('Negative numbers not yet supported.');
		return;
	}
	
	// Handle single-digit numbers.
	if ((0 <= num) && (num <= 10)) {
		return '(' + num.toString() + ')';
	}
	
	// Find the value of the highest digit.
	var digit = 1;
	var value = num;
	while (value > 10) {
		value = Math.floor(value / 10);
		digit *= 10;
	}
	var upperDigit = value * digit;
	var remainder = num - upperDigit;   // Remainder stores the value of the lower digits.
	if (remainder == 0) {
		// If the lower digits are all zero, return the value of the upper digit.
		return '(* (' + value.toString() + ') ' + GH.Prover.numToSexp(digit) + ')';
	} else {
		// If there are lower digits, add the upper and lower digit numbers.
		var lowerDigits = GH.Prover.numToSexp(remainder);
		var upperDigits = GH.Prover.numToSexp(upperDigit);
		return '(+ ' + upperDigits + ' ' + lowerDigits + ') ';
	}
};
	
// Convert an s-expression into a number.
// Simply performs all the multiplication and additions within the expression.
GH.Prover.sexpToNum = function(sexp) {
	if (sexp.operator_ == '*') {
		return GH.Prover.sexpToNum(sexp.left()) * GH.Prover.sexpToNum(sexp.right());
	} else if (sexp.operator_ == '+') {
		return GH.Prover.sexpToNum(sexp.left()) + GH.Prover.sexpToNum(sexp.right());
	} else {
		return parseInt(sexp.operator_);
	}
};
	
// Returns true if x is a power of ten.
GH.Prover.isPowerOfTen = function(x) {
	while (x % 10 == 0) {
		x /= 10;
	}
	return (x == 1);
};
	
// Convert a number to an s-expression and insert it into the stack.
GH.Prover.printNum = function(num) {
	GH.Prover.println(GH.Prover.numToSexp(num));
};

// TODO: Rename and describe function.
GH.Prover.findPosition = function(sexp) {
	var indices = [];
	// Traverse up the tree from matcher up to the root and record which sibling
	// of the tree we traverse at each step.
	while (sexp.parent_ != null) {
		indices.push(sexp.siblingIndex_);
		sexp = sexp.parent_;
	}
	// Return the indices in reverse to tell how to descend through the tree.
	return indices.reverse();
};
	
/**
 * FindMatchingPosition takes two s-expressions. An s-expression is represented
 * as a position within a tree. sexp and matcher have a very close tree structure,
 * but sexp is at the root of the tree and matcher is somewhere within the tree.
 * In this function, sexp moves into the position where matcher is.
 */
GH.Prover.findMatchingPosition = function(sexp, matcher) {
	var indices = GH.Prover.findPosition(matcher);

	// Traverse down the sexp tree. This is just the reverse of the ascent up.
	for (var i = 0; i < indices.length; i++) {
		sexp = sexp.operands_[indices[i]];
	}
	return sexp;
};

/**
 * Replace an s-expression using a proof generator. The proof generator can automatically
 * generate theorems. Those theorems may or may not be in the repository. This function
 * is designed to work in either case. If the theorem is in the repository this function
 * will look it up and use it. If it is not in the repository, this function will
 * generate all the necessary steps to replace the s-expression.
 */
GH.Prover.replaceWith = function(generator, sexp) {
	GH.Prover.println('## <apply \'' + generator.description + '\'>');
	window.direct.prover.depth++;
	var name = generator.name(sexp);
	if (window.direct.vg.syms.hasOwnProperty(name)) {
		// Uses the proof if it already exists in the repository.
		var hyps = generator.hyps(sexp);
		GH.Prover.print(hyps, name);
	} else {
		// TODO: Generates a proof when the proof is not in the repository.
		generator.body(sexp);
	}
	var position = GH.Prover.findPosition(sexp);
	if (position.length > 0) {
		var subText = '## <substitute ';
		for (var i = 0; i < position.length; i++) {
			if (position[i] > 10) {
				alert('Operator has more than 10 operands.');
			}
			subText += position[i];
		}
		GH.Prover.println(subText + '>');
		window.direct.prover.depth++;
	}
	result = GH.Prover.getReplaced(sexp);
	if (position.length > 0) {
		window.direct.prover.depth--;
		GH.Prover.println('## </substitute>');
	}
	window.direct.prover.depth--;
	GH.Prover.println('## </apply \'' + generator.description + '\'>');
	return result;
};

/**
 * From an s-expression and an expected form extracts all the hypotheses out of
 * the sexp. For example, if sexp = 2 * (3 + 4) and expectedForm = A * B, it will
 * extract two hypotheses A: 2 and B: 3 + 4. The hypotheses may be returned in the
 * wrong order.
 */
GH.Prover.getUnorderedHyps = function(sexp, expectedForm, hyps) {
	var operandsExpected = expectedForm.operands_.length;
	var operandsActual   =         sexp.operands_.length;
	// Every variable in the expected form may represent a large expression that has many operands, so it is
	// not a problem if there are operands when we expect none.
	if ((operandsExpected != operandsActual) && (operandsExpected != 0)) {
		alert('Wrong number of operands. Expected ' + operandsExpected + ', but got ' + operandsActual + '.');
		return {};
	} else if (operandsExpected > 0) {
		var operatorExpected = expectedForm.operator_.toString();
		var operatorActual   =         sexp.operator_.toString();
		if ((operatorExpected != operatorActual) &&
		    (operatorExpected != 'operator')) {
			alert('Unexpected Operator. Expected ' + operatorExpected + ', but got ' + operatorActual + '.');
			return {};
		} else {
			for (var i = 0; i < operandsExpected; i++) {
				hyps = GH.Prover.getUnorderedHyps(sexp.operands_[i], expectedForm.operands_[i], hyps);
			}
			return hyps;
		}
	} else {
		var expression = expectedForm.getExpression();
		if ((expression in hyps) && (!hyps[expression].equals(sexp))) {
			alert(sexp.toString() + ' does not match ' + hyps[expression].toString() + '.');
			return [];
		} else {
			hyps[expression] = sexp;
			return hyps;
		}
	}
};

GH.Prover.defaultOrder = ['A', 'B', 'C', 'D', 'E', 'F'];

// From an s-expression and an expected form extracts all the hypotheses out of
// the sexp. For example, if sexp = 2 * (3 + 4) and expectedForm = A * B, it will
// extract two hypotheses A: 2 and B: 3 + 4. The hypotheses are returned in the
// default order.
GH.Prover.getHyps = function(sexp, expectedForm) {
	var hyps = GH.Prover.getUnorderedHyps(sexp, expectedForm, {});
	var hypsInOrder = [];
	for (var i = 0; i < GH.Prover.defaultOrder.length; i++) {
		var key = GH.Prover.defaultOrder[i];
		if (key in hyps) {
			hypsInOrder.push(hyps[key]);
		}
	}
	return hypsInOrder;
};

// From a set hypotheses and an expected form generates a s-expression. This
// performs the reverse operation of getHyps. If the expectedForm is A * B
// and the newHyps are A: 2 and B: 3 + 4, then it returns 2 * (3 + 4).
GH.Prover.setHyps = function(expectedForm, newHyps) {
	var sexp = expectedForm.copy(null);
	var hyps = GH.Prover.getUnorderedHyps(sexp, expectedForm, {});
	var keys = [];
	for (var i = 0; i < GH.Prover.defaultOrder.length; i++) {
		var key = GH.Prover.defaultOrder[i];
		if (key in hyps) {
			keys.push(key);
		}
	}
	return GH.Prover.setHypsWithKeys(sexp, keys, newHyps);
};

// Fill in an s-expresson from with a set of key and hyps.
// For example, if sexp = A * B, and keys = [A, B] and hyps = [2, 3 + 4],
// then this function returns the expression 2 * (3 + 4).
GH.Prover.setHypsWithKeys = function(sexp, keys, hyps) {
	var operandsNum = sexp.operands_.length;
	if (operandsNum > 0) {
		for (var i = 0; i < operandsNum; i++) {
			sexp = GH.Prover.setHypsWithKeys(sexp.operands_[i], keys, hyps).parent_;
		}
		return sexp;
	} else {
		var expression = sexp.getExpression();
		for (var i = 0; i < keys.length; i++) {
			if (keys[i] == expression) {
				var newSexp = hyps[i].copy();
				sexp.parent_.operands_[sexp.siblingIndex_] = newSexp;
				newSexp.parent_ = sexp.parent_;
				return newSexp;
			}
		}
		alert('Key never found.');
		return null;
	}	
};

/**
 * Generates a full theorem using a proof generator and an s-expression.
 * The name of the theorem, its inputs, and the body of the proof are all based on the
 * s-expression. A placeholder conclusion is initially used to prevent Ghilbert from
 * complaining. Once the real conclusion is generated, it replaces the fake conclusion.
 */
GH.Prover.addTheorem = function(generator, sexp) {
	GH.Prover.insertText('thm (' + generator.name(sexp) + ' ' + generator.header(sexp) + ' ');
	var conclusionPosition = window.direct.text.getCursorPosition();
	var fakeConclusion = '(= (0) (1))';
	GH.Prover.insertText(fakeConclusion);
	GH.Prover.insertText('\n');
	window.direct.prover.depth++;
	generator.body(sexp);
	window.direct.prover.depth--;
	GH.Prover.println(')');
	var conclusion = GH.Prover.getLast();
	window.direct.text.splice(conclusionPosition, fakeConclusion.length, conclusion);
	window.direct.update();
};


/**
 * Replaces part of an s-expression. The replacement must expresses some equivalence
 * relationship =, <->, etc. with the old part on the left and the new part on the right.
 * For example, replacee:    x     + 1 < 2
 *              replacement: x = 0
 *              result:          0 + 1 < 2
 *
 * This function uses a different Ghilbert step depending on the operator of the parent
 * of replacee and based on which operand the replacee is. Eventually, every operator
 * should be included in this function. This should also eventually be done automatically
 * from the defthm of the operator.
 */
GH.Prover.replace = function(replacee, replacement) {
	var parent = replacee.parent_;
	var siblingIndex = replacee.siblingIndex_;
	if (!parent) {
		return replacement.right();
	}
		
	var operator = parent.operator_;
	var isNumber = false;
	if (operator == '-.') {
		if (parent.parent_) {
			GH.Prover.print([], 'con4biir');
		} else {
			GH.Prover.print([], 'mtbi');
		}
	} else if (operator == '->') {
		if (siblingIndex == 0) {
			GH.Prover.print([], 'sylbi2');
		} else {
			GH.Prover.print([], 'sylib');
		}
	} else if (operator == '<->') {
		if (siblingIndex == 0) {
			GH.Prover.print([], 'bitr3icom');
		} else {
			GH.Prover.print([], 'bitri');
		}
	} else if (operator == '\\/') {
		// If the parent of the replacee has a parent, we want to generate a
		// conditional statement A <-> B, otherwise we do not. The same pattern
		// occurs for many operators.
		if (parent.parent_)
			if (siblingIndex == 0) {
				GH.Prover.print([parent.right()], 'orbi1i');
			} else {
				GH.Prover.print([parent.left()], 'orbi2i');
			}
		else {
			if (siblingIndex == 0) {
				GH.Prover.print([], 'orbi1ii');
			} else {
				GH.Prover.print([], 'orbi2ii');
			}
		}
	} else if (operator == '/\\') {
		if (parent.parent_) {
			if (siblingIndex == 0) {
				GH.Prover.print([parent.right()], 'anbi1i');
			} else {
				GH.Prover.print([parent.left()], 'anbi2i');
			}
		} else {
			if (siblingIndex == 0) {
				GH.Prover.print([], 'anbi1ii');
			} else {
				GH.Prover.print([], 'anbi2ii');
			}
		}
	} else if (operator == 'A.') {
		if (siblingIndex == 0) {
			alert('Cannot replace the left side of A.');
		} else {
			var mandHyp = [parent.left()];
			if (parent.parent_) {
				GH.Prover.print(mandHyp, 'albii');
			} else {
				GH.Prover.print(mandHyp, 'albiii');
			}
		}
	} else if (operator == 'E.') {
		if (siblingIndex == 0) {
			alert('Cannot replace the left side of E.');
		} else {
			var mandHyp = [parent.left()];
			if (parent.parent_) {
				GH.Prover.print(mandHyp, 'exbii');
			} else {
				GH.Prover.print(mandHyp, 'exbiii');
			}
		}
	} else if (operator == '=') {
		if (parent.parent_) {
			if (siblingIndex == 0) {
				GH.Prover.print([parent.right()], 'eqeq1i');
			} else {
				GH.Prover.print([parent.left()], 'eqeq2i');
			}
		} else {
			if (siblingIndex == 0) {
				GH.Prover.print([], 'eqtr5');
			} else {
				GH.Prover.print([], 'eqtr');
			}
		}
	} else if (operator == '<=') {
		if (parent.parent_) {
			if (siblingIndex == 0) {
				GH.Prover.print([parent.right()], 'leeq1i');
			} else {
				GH.Prover.print([parent.left()], 'leeq2i');
			}
		} else {
			if (siblingIndex == 0) {
				GH.Prover.print([], 'leeq1ii');
			} else {
				GH.Prover.print([], 'leeq2ii');
			}
		}
	} else if (operator == '<') {
		if (parent.parent_) {
			if (siblingIndex == 0) {
				GH.Prover.print([parent.right()], 'lteq1i');
			} else {
				GH.Prover.print([parent.left()], 'lteq2i');
			}
		} else {
			if (siblingIndex == 0) {
				GH.Prover.print([], 'lteq1ii');
			} else {
				GH.Prover.print([], 'lteq2ii');
			}
		}
	} else if (operator == '+') {
		isNumber = true;
		if (siblingIndex == 0) {			
			GH.Prover.print([replacement.left(), replacement.right(), parent.right()], 'addeq1');
		} else {
			GH.Prover.print([replacement.left(), replacement.right(), parent.left()], 'addeq2');
		}
		GH.Prover.print([], 'ax-mp');
	} else if (operator == '*') {
		isNumber = true;
		if (siblingIndex == 0) {			
			GH.Prover.print([replacement.left(), replacement.right(), parent.right()], 'muleq1');
		} else {
			GH.Prover.print([replacement.left(), replacement.right(), parent.left()], 'muleq2');
		}
		GH.Prover.print([], 'ax-mp');
	} else {
		alert('There is no rule for replacing operator ' + operator + '.');
	}

	// Recursively replace the entire replacee follow the expression up to the root.
	replacement = GH.Prover.getLast();
	if (parent.parent_) {
		return GH.Prover.replace(parent, replacement);
	} else {
		// If we are replacing a number without a parent such as the number 1 + 1 with 2, then
		// we would be generating the expression 1 + 1 = 2. We return the right side of this
		// expression, the number 2, not the logical expression defined with the equals =.
		if (isNumber) {
			return replacement.right();
		} else {
			return replacement;
		}
	}
};

// Replace the s-expression replacee using the last statement on the proof stack.
GH.Prover.getReplaced = function(replacee) {
	var replacement = GH.Prover.getLast();
	if (replacee.parent_) {
		var replaced = GH.Prover.replace(replacee, replacement);
		return GH.Prover.findMatchingPosition(replaced, replacee);
	} else {
		return replacement.right();
	}
};

// Commmute the operands of an s-expression.	
GH.Prover.commute = function(sexp) {
	// Commuting is unnecessary if the left and right sides are equal.
	if (sexp.left().equals(sexp.right())) {
		return sexp;
	}
	
	var operator = sexp.operator_;
	var mandHyps = [sexp.left(), sexp.right()];
	if (operator == '<->') {
		GH.Prover.print([], 'bicomi');
		return GH.Prover.getReplaced(sexp);
	} else if (operator == '/\\') {
		GH.Prover.print(mandHyps, 'ancom');
		return GH.Prover.getReplaced(sexp);
	} else if (operator == '\\/') {
		GH.Prover.print(mandHyps, 'orcom');
		return GH.Prover.getReplaced(sexp);
	} else if (operator == '=') {
		if (sexp.parent_) {
			GH.Prover.print(mandHyps, 'eqcom');
		} else {
			GH.Prover.print([], 'eqcomi');
		}
		return GH.Prover.getReplaced(sexp);
	} else if (operator == '+') {
		GH.Prover.print(mandHyps, 'addcom');
		return GH.Prover.getReplaced(sexp);
	} else if (operator == '*') {
		GH.Prover.print(mandHyps, 'mulcom');
		return GH.Prover.getReplaced(sexp);
	} else {
		alert('No rule available for commuting the ' + operator + ' operator.');
		return null;
	}
};

// Apply the associative property on an s-expression. This does the same thing as
// reposition(result, 'A (B C)', '(A B) C');
GH.Prover.associateLeft = function(sexp) {
	var operator = sexp.operator_;
	var mandHyps = [sexp.left(), sexp.right().left(), sexp.right().right()];
	if (operator == '+') {
		if (sexp.right().operator_ != '+') {
			alert('No rule available for associating the ' + operator + '  and ' + sexp.right().operator_ + ' operators.');
			return null;
		}
		GH.Prover.print(mandHyps, 'addass');
		GH.Prover.print([], 'eqcomi');
		return GH.Prover.getReplaced(sexp);
	} else {
		alert('No rule available for associating the ' + operator + ' operator.');
		return null;
	}
};

// Apply the associative property on an s-expression. This does the same thing as
// reposition(result, '(A B) C', 'A (B C)');	
GH.Prover.associateRight = function(sexp) {
	var operator = sexp.operator_;
	var mandHyps = [sexp.left().left(), sexp.left().right(), sexp.right()];
	if (operator == '+') {
		if (sexp.left().operator_ != '+') {
			alert('No rule available for associating the ' + operator + '  and ' + sexp.left().operator_ + ' operators.');
			return null;
		}
		GH.Prover.print(mandHyps, 'addass');
		return GH.Prover.getReplaced(sexp);
	} else {
		alert('No rule available for associating the ' + operator + ' operator.');
		return null;
	}
};

// Replace a single-digit number with its predessor on the left.
// For example, 5 = 4 + 1.
GH.Prover.predecessorLeft = function(sexp) {
	var num = sexp.operator_;
	GH.Prover.print([], 'df-' + num);
	return GH.Prover.getReplaced(sexp);
};

// Replace a single-digit number with its predecessor on the right.
// For example, 5 = 1 + 4.
GH.Prover.predecessorRight = function(sexp) {
	var num = sexp.operator_;
	GH.Prover.print([], 'df-' + num);
	var replacement = GH.Prover.getLast();
	GH.Prover.commute(replacement.right());
	return GH.Prover.getReplaced(sexp);
};

// Replace a single-digit number on the left with its successor.
// For example, 4 + 1 = 5.
GH.Prover.successorLeft = function(sexp) {
	var num = sexp.left().operator_;
	GH.Prover.print([], 'df-' + (parseInt(num) + 1));
	var replacement = GH.Prover.getLast();
	GH.Prover.commute(replacement);
	return GH.Prover.getReplaced(sexp);
};

// Replace a single-digit number on the left with its successor.
// For example, 1 + 4 = 5.	
GH.Prover.successorRight = function(sexp) {
	var num = sexp.right().operator_;
	GH.Prover.print([], 'df-' + (parseInt(num) + 1));
	var replacement = GH.Prover.getLast();
	replacement = GH.Prover.applyRight(GH.Prover.commute, replacement);
	GH.Prover.commute(replacement);
	return GH.Prover.getReplaced(sexp, replacement);
};

// Apply a function to the right side of an s-expression. This does not change
// the position of the s-expression.
GH.Prover.applyRight = function(applyFunc, sexp) {
	return applyFunc.call(this, sexp.right()).parent_;
};

// Apply a function to the left side of an s-expression. This does not change
// the position of the s-expression.
GH.Prover.applyLeft = function(applyFunc, sexp) {
	return applyFunc.call(this, sexp.left()).parent_;
};

// Replace the left side of an s-expression. This does not change the position
// of the s-expression.
GH.Prover.replaceLeft = function(generator, sexp) {
	return GH.Prover.replaceWith(generator, sexp.left()).parent_;
};

// Replace the right side of an s-expression. This does not change the position
// of the s-expression.
GH.Prover.replaceRight = function(generator, sexp) {
	return GH.Prover.replaceWith(generator, sexp.right()).parent_;
};

// Use the additive identity to simplify expressions like 5 + 0 to 5.
GH.Prover.additiveIdentity = function(sexp) {
	if (sexp.operator_ == '+') {
		if (sexp.left().operator_ == '0') {
			GH.Prover.print([sexp.right()], 'pa_ax3r');
			return GH.Prover.getReplaced(sexp);
		} else if (sexp.right().operator_ == '0') {
			GH.Prover.print([sexp.left()], 'pa_ax3r');
			GH.Prover.commute(GH.Prover.getLast().left());
			return GH.Prover.getReplaced(sexp);
		}
	}
	return sexp;
};

/**
 * GH.Prover.addSingleDigits is a proof generator. It contains several functions
 * for automatically adding two single digit numbers like 2 + 2 = 4. Each function
 * depending on the s-expression coming in. It will generate a different proof for
 * 2 + 3, 2 + 4, etc. with a different name.
 */
GH.Prover.addSingleDigits = {};

// Each generator has an expected form for the input s-expression.
GH.Prover.addSingleDigits.expectedForm = GH.sExpression.fromString('(+ A B)');

// Each generator has a description. It is displayed on the right step of the proof step.
GH.Prover.addSingleDigits.description = 'Add Single-Digits';

// Returns the name of the theorem given an s-expression.
GH.Prover.addSingleDigits.name = function(sexp) {
	var hyps = GH.Prover.getHyps(sexp, this.expectedForm);
	return hyps[0].operator_ + 'plus' + hyps[1].operator_;
};

// Returns the mandatory hypotheses for the theorem given an s-expression.
// addSingleDigits has no mandatory hypotheses.
GH.Prover.addSingleDigits.hyps = function(sexp) {
	return [];
};

// Returns a header of the theorem contain the theorem hypotheses and the freeness
// constraints. Both are empty in this case.
GH.Prover.addSingleDigits.header = function(sexp) {
	return '() ()';
};

// Generate a full theorem given two single digit numbers.
GH.Prover.addSingleDigits.makeTheorem = function(leftNum, rightNum) {
	// Create an s-expression in the expected form with the left and right numbers.
	var leftHyp  = GH.sExpression.fromString('(' + leftNum  + ')');
	var rightHyp = GH.sExpression.fromString('(' + rightNum + ')');
	var sexp = GH.Prover.setHyps(this.expectedForm, [leftHyp, rightHyp]);
	GH.Prover.addTheorem(this, sexp);
};

// The body of the addSingleDigits proof generator. Takes an expression like 2 + 2
// and finds their sum: 2 + 2 = 4.
GH.Prover.addSingleDigits.body = function(sexp) {
	var  leftNum = parseInt(sexp.left().operator_);
	var rightNum = parseInt(sexp.right().operator_);
	var result = sexp.copy();
	result = GH.Prover.additiveIdentity(result);

	// We increment the higher number and decrement the lower number until
	// we've reach 10 or until the lower number is zero.
	if (rightNum < leftNum) {
		while ((rightNum > 0) && (leftNum < 10)) {
			if (rightNum > 1) {
				result = GH.Prover.applyRight(GH.Prover.predecessorRight, result);
				result = GH.Prover.associateLeft(result);
				result = GH.Prover.applyLeft(GH.Prover.successorLeft, result);
			} else {
				result = GH.Prover.successorLeft(result);
			}
			rightNum--;
			leftNum++;
		}
	} else {
		while ((leftNum > 0) && (rightNum < 10)) {
			if (leftNum > 1) {
				result = GH.Prover.applyLeft(GH.Prover.predecessorLeft, result);
				result = GH.Prover.associateRight(result);
				result = GH.Prover.applyRight(GH.Prover.successorRight, result);
			} else {
				result = GH.Prover.successorRight(result);
			}
			rightNum++;
			leftNum--;
		}
		if ((rightNum == 10) && (leftNum > 0)) {
			result = GH.Prover.commute(result);
		}
	}
	return result;
};

// Replace a number x with 1 * x.
GH.Prover.multiplyByOneLeft = function(sexp) {
	if (((sexp.operator_ == '+') || (sexp.operator_ == '*')) && (sexp.left().operator_ == '1')) {
		return sexp;
	}
	GH.Prover.print([sexp], 'mulid');
	GH.Prover.print([], 'eqcomi');
	GH.Prover.commute(GH.Prover.getLast().right());
	return GH.Prover.getReplaced(sexp);
};

// Adds two multi-digit numbers. This represents adding the 10's or 100's digit.
// Both numbers must have the same number of digits and only the highest digit can
// be non-zero. The numbers should be in long-form.
GH.Prover.addHigherDigits = function(sexp) {
	var result = sexp.copy(null);                                          // Example:
	                                                                       // 5 * 10 + 6 * 10
	result = GH.Prover.replaceWith(GH.Prover.undistributeLeft, result);   // (5 + 6) * 10
	result = GH.Prover.replaceLeft(GH.Prover.addSingleDigits, result);     // (10 + 1) * 10
	
	// If the result is a two digit number. Distribute the carry.
	if (result.left().operator_ == '+') {              
		result = GH.Prover.replaceWith(GH.Prover.distributeLeft, result); // 10 * 10 +  1 * 10
	}

	//return result;
	return GH.Prover.getReplaced(sexp);
};


// Distribute the right operand to the left like this: (a + b) * c = a * c + b * c.
GH.Prover.distributeLeft = {};

GH.Prover.distributeLeft.expectedForm = GH.sExpression.fromString('(* (+ A B) C)');

GH.Prover.distributeLeft.description = 'Distributive Prop.';

GH.Prover.distributeLeft.name = function(sexp) {
	return 'distl';
};

// Returns the mandatory hypotheses using the expected form.
GH.Prover.distributeLeft.hyps = function(sexp) {
	return GH.Prover.getHyps(sexp, this.expectedForm);
};
// We assume that 'distl' is in the repository, so there is no body or header for GH.Prover.distributeLeft.

// This reverses the distribution left operation:  a * c + b * c = (a + b) * c
GH.Prover.undistributeLeft = {};

GH.Prover.undistributeLeft.expectedForm = GH.sExpression.fromString('(+ (* A C) (* B C))');

GH.Prover.undistributeLeft.name = function(sexp) {
	return 'undistl';
};

GH.Prover.undistributeLeft.description = 'Distributive Prop.';

GH.Prover.undistributeLeft.header = function(sexp) {
	return '() ()';
};

GH.Prover.undistributeLeft.hyps = function(sexp) {
	return GH.Prover.getHyps(sexp, this.expectedForm);
};

GH.Prover.undistributeLeft.body = function(sexp) {
	var hyps = GH.Prover.getHyps(sexp, this.expectedForm);
	GH.Prover.print(hyps, 'distl');
	GH.Prover.print([], 'eqcomi');
	return GH.Prover.getReplaced(sexp);
};

GH.Prover.undistributeLeft.makeTheorem = function() {
	GH.Prover.addTheorem(this, this.expectedForm);
};

// Computes the sum of two numbers. Both numbers are converted into a long form that is easier to compute
// with. The result is converted back into the short form.
GH.Prover.addTwoNumbers = function(sexp) {
	var result = sexp;
	result = GH.Prover.applyLeft(GH.Prover.numberLongForm, result);
	result = GH.Prover.applyRight(GH.Prover.numberLongForm, result);
	result = GH.Prover.addTwoLongFormNumbers(result);
	return GH.Prover.numberShortForm(result);
};

// Converts an s-expression representing a number in a long form. Digits with a 1 or 0 are expanded out.
// For example, 120 is normally represented as:   120 =     10 * 10 + 2 * 10. 
// In long-form it is represented as:             120 = 1 * 10 * 10 + 2 * 10 + 0.
GH.Prover.numberLongForm = function(sexp) {
	var num = GH.Prover.sexpToNum(sexp);
	var digits = GH.numOfDigits(num);
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
				result = GH.Prover.applyLeft(GH.Prover.multiplyByOneLeft, result);
				result = result.right();
				depth++;
			} else if ((result.operator_ == '*') || (result.operator_ = '10')) {
				changed = true;
				result = GH.Prover.multiplyByOneLeft(result);
			}
		} else if ((value > 1) && (result.operator_ == '+')) {
			result = result.right();
			depth++;
		} else if (value == 0) {
			changed = true;
			// If a digit has a value of 0, add zero times the base 10 number.
			if (num == 0) {
				// TODO: Stop duplicating zero digits everytime we go through this function.
				GH.Prover.print([result], 'pa_ax3')
				GH.Prover.print([], 'eqcomi');
				result = GH.Prover.getReplaced(result);
				if (i > 0) {
					GH.Prover.print([GH.Prover.numToSexp(Math.pow(10, i))], 'pa_ax5r')
					GH.Prover.print([], 'eqcomi');
					result = GH.Prover.getReplaced(result.right());
				} else {
					result = result.right();
					depth++;
				}
			} else {
				GH.Prover.print([result], 'pa_ax3r')
				GH.Prover.print([], 'eqcomi');
				result = GH.Prover.getReplaced(result);
				if (i > 0) {
					GH.Prover.print([GH.Prover.numToSexp(Math.pow(10, i))], 'pa_ax5r')
					GH.Prover.print([], 'eqcomi');
					result = GH.Prover.getReplaced(result.left());
					result = result.parent_;
				}
				result = result.right();
				depth++;
			}
		}
	}
	if (changed) {
		return GH.Prover.getReplaced(sexp);
	} else {
		return sexp;
	}
};

// Simplify multiplication in the following two ways:
//     1 * x = x
//     0 * x = 0
GH.Prover.simplifyTimes = function(sexp) {
	var result = sexp;
	if(result.operator_ == '*') {
		if (result.left().operator_ == '0') {
			GH.Prover.print([result.right()], 'pa_ax5r')
			result = GH.Prover.getReplaced(result);
		} else if (result.left().operator_ == '1') {
			GH.Prover.print([result.right()], 'mulid');
			var mulid = GH.Prover.getLast();
			GH.Prover.applyLeft(GH.Prover.commute, mulid);
			result = GH.Prover.getReplaced(result);
		}
	}
	return result;
};

// Convert a number in long form back into the standard short form.
// Simplify multiplication and addition.
GH.Prover.numberShortForm = function(sexp) {
	if (sexp.operator_ == '+') {
		var result = sexp;
		result = GH.Prover.applyLeft(GH.Prover.numberShortForm, sexp);
		result = GH.Prover.applyRight(GH.Prover.numberShortForm, result);
		return GH.Prover.additiveIdentity(result);
	} else {
		return GH.Prover.simplifyTimes(sexp);
	}
};

// Returns the number of digits of a number. The number can be in long form or short form.
GH.Prover.getDigitNum = function(sexp) {
	if (sexp.operator_ == '+') {
		return GH.Prover.getDigitNum(sexp.left());
	} else if (sexp.operator_ == '*') {
		return GH.numOfDigits(GH.Prover.sexpToNum(sexp.right()));
	} else {
		return 1;
	}
};

// Computes the sum of two numbers in long form.
GH.Prover.addTwoLongFormNumbers = function(sexp) {
	var leftNum  = GH.Prover.sexpToNum(sexp.left());
	var rightNum = GH.Prover.sexpToNum(sexp.right());
	var leftDigits = GH.Prover.getDigitNum(sexp.left());
	var rightDigits = GH.Prover.getDigitNum(sexp.right());
	var maxDigits = Math.max(leftDigits, rightDigits);
		
	var digit = Math.pow(10, maxDigits - 1);
	var upperDigit = digit * 10;
	var lowerCarry = (((leftNum %      digit) + (rightNum %      digit)) / digit >= 1);
	var upperCarry = (((leftNum % upperDigit) + (rightNum % upperDigit)) / upperDigit >= 1);
	var lowerZero  = (((leftNum + rightNum) % upperDigit) / digit < 1);
				
	var result = sexp;
	if (leftDigits == 1 && rightDigits == 1) {
		result = GH.Prover.replaceWith(GH.Prover.addSingleDigits, result);
	} else if (leftDigits != rightDigits) {
		if (leftDigits > rightDigits) {
			result = GH.Prover.associateRight(result);
		} else {
			result = GH.Prover.reposition(result, 'A (B C)', 'B (A C)');
		}
		result = GH.Prover.applyRight(GH.Prover.addTwoLongFormNumbers, result);
			
		// Handle a carry.
		if (lowerCarry) {
			result = GH.Prover.associateLeft(result);
			//result = GH.Prover.reposition(result, 'A (B C)', '(A B) C'); // Same as associateLeft
			result = GH.Prover.applyLeft(GH.Prover.addHigherDigits, result);
		}		
	} else if (leftDigits == rightDigits) {
		result = GH.Prover.reposition(result, '(A B) (C D)', '(A C) (B D)'); // This is the same as add4.
		result = GH.Prover.applyRight(GH.Prover.addTwoLongFormNumbers, result);
	
		// Handle a carry.
		if (lowerCarry) {
			result = GH.Prover.reposition(result, '(A B) (carry D)', '(A (B carry)) D');
			result = result.left().right();
			result = GH.Prover.addHigherDigits(result);
			result = result.parent_.parent_;
		}
		result = GH.Prover.applyLeft(GH.Prover.addHigherDigits, result);
		if (upperCarry && !lowerZero) {
			result = GH.Prover.associateRight(result);
		}
	}
	result = GH.Prover.numberLongForm(result);
	return result;
};

// Takes an s-expression and a symbol tree and continues to run the associateRight function
// wherever it is possible for both the symbol tree and the s-expression.
GH.Prover.associateAllRight = function(expTree) {
	var sexp = expTree.sexp;
	var tree = expTree.tree;
	if (tree.left && tree.left.left) {
		var result = GH.Prover.associateRight(sexp);
		tree.associateRight();
		return GH.Prover.associateAllRight({sexp: result, tree: tree});
	} else if (tree.right) {
		var result = GH.Prover.associateAllRight({sexp: sexp.right(), tree: tree.right});
		return {sexp: result.sexp.parent_, tree: tree};
	} else {
		return expTree;
	}
};

// Takes an s-expression and a symbol tree and continues to run the associateLeft function
// wherever it is possible for both the symbol tree and the s-expression.
GH.Prover.associateAllLeft = function(expTree) {
	var sexp = expTree.sexp;
	var tree = expTree.tree;
	if (tree.right && tree.right.right) {
		var result = GH.Prover.associateLeft(sexp);
		tree.associateLeft();
		return GH.Prover.associateAllLeft({sexp: result, tree: tree});
	} else if (tree.left) {
		var result = GH.Prover.associateAllLeft({sexp: sexp.left(), tree: tree.left});
		return {sexp: result.sexp.parent_, tree: tree};
	} else {
		return expTree;
	}
};

// Repositions the terms in an s-expression. Uses commutation and association rules to 
// change the s-expression between any two positions. Assumes that s-expression has operators
// that commute and associate. oldPosition and newPosition are strings that are converted into
// symbol trees. 
GH.Prover.reposition = function(sexp, oldPosition, newPosition) {
	var oldTree = GH.symbolTree.fromString(oldPosition);
	var newTree = GH.symbolTree.fromString(newPosition);
	return GH.Prover.repositionTree(sexp, oldTree, newTree);
};

// Repositions the terms in an s-expression. Uses commutation and association rules to 
// change the s-expression between two symbol trees. Assumes that s-expression has operators
// that commute and associate.

// First, associate all left, then reorder all the terms, and then use association rules to
// get into the new tree position.
GH.Prover.repositionTree = function(sexp, oldTree, newTree) {
	// TODO: Optimize by not modifying left or right if they were not changed.
	var leftAssociated = GH.Prover.associateAllLeft({sexp: sexp, tree: oldTree});
//	var result = leftAssociated.
	var symbolOrder = GH.symbolTree.getSymbolOrder(oldTree.getSymbolList(), newTree.getSymbolList());
	var reordered = GH.Prover.reorder(leftAssociated.sexp, symbolOrder);
	
	// leftAssociated.tree was set before the reordering, so it is not a perfect representation
	// of the state of the left, but for the reassociation step the order is irrelevant.
	return GH.Prover.reassociate(reordered, leftAssociated.tree, newTree);
};
	
// Uses a bubble sort.
GH.Prover.reorder = function(sexp, order) {
	var inorder = false;
	var result = sexp;
	while (!inorder) {
		inorder = true;
		for (var i = 0; i < order.length - 1; i++) {
			if (order[i] > order[i + 1]) {
				var temp = order[i];
				order[i] = order[i + 1];
				order[i + 1] = temp;
				inorder = false;
					
				result = GH.Prover.bubble(result, i, order.length);
			}
		}
	}
	return result;
};

// Swaps the order of two expressions, given the position of the
// expression to swap. The most basic operation in a bubble sort. 
GH.Prover.bubble = function(sexp, position, listLength) {
	var leftness = listLength - position - 2;
	for (var i = 0; i < leftness; i++) {
		sexp = sexp.left();
	}
	if (position == 0) {
		sexp = GH.Prover.commute(sexp);
	} else {
		sexp = GH.Prover.associateRight(sexp);
		sexp = GH.Prover.applyRight(GH.Prover.commute, sexp);
		sexp = GH.Prover.associateLeft(sexp);
	}
	for (var i = 0; i < leftness; i++) {
		sexp = sexp.parent_;
	}
	return sexp;
};

// Given an s-expression an a symbol tree representing the old order of
// operations and a symbol tree representing the new order of operations
// switches the order of operations until the tree have the same structure.
// The order of the operands does not change.
GH.Prover.reassociate = function(sexp, oldTree, newTree) {
	if (!oldTree.left) {
		return sexp;
	}
	
	var oldLeftness = oldTree.left.getSymbolList().length;
	var newLeftness = newTree.left.getSymbolList().length;
	while (oldLeftness < newLeftness) {
		sexp = GH.Prover.associateLeft(sexp);
		oldTree.associateLeft();
		oldLeftness = oldTree.left.getSymbolList().length;
	}
	while (oldLeftness > newLeftness) {
		sexp = GH.Prover.associateRight(sexp);
		oldTree.associateRight();
		oldLeftness = oldTree.left.getSymbolList().length;
	}
	if (oldLeftness != newLeftness) {
		alert('Reassociation failed.');
	}
	var result = sexp;
	result = GH.Prover.reassociate(result.left(),  oldTree.left,  newTree.left);
	result = result.parent_;
	result = GH.Prover.reassociate(result.right(), oldTree.right, newTree.right);
	result = result.parent_;
	
	return result;
};

GH.Prover.oneDigitNotZero = function(sexp) {
	var predecessor = parseInt(sexp.operator_) - 1;	
	GH.Prover.print(['(' + predecessor + ')'], 'pa_ax1');
	var result = GH.Prover.getLast().child().right();

	GH.Prover.print(['(' + predecessor + ')'], 'a1suc');
	result = GH.Prover.getReplaced(result, GH.Prover.getLast())
	GH.Prover.successorLeft(result);
};

GH.Prover.oneDigitInequality = function(leftNum, rightNum) {
	if (leftNum >= rightNum) {
		// Not written yet.
		return;
	}
	var diff = rightNum - leftNum;
	GH.Prover.println('x (' + diff + ') tyex');
	GH.Prover.println('x (' + diff + ') (' + leftNum + ') addeq2');
	
	var result = GH.Prover.getLast().right().right();
	result = GH.Prover.replaceWith(GH.Prover.addSingleDigits, result);
	
	GH.Prover.println('x 19.22i');
	GH.Prover.println('ax-mp');

    GH.Prover.println('(' + leftNum + ') (' + rightNum + ') x df-le');
    GH.Prover.println('mpbir');  // Could also use replace.

    // TODO: Put this is a not equal function
		// TODO: Don't use a fake s-expression.
		var fakeSexp = {operator_: diff};
		GH.Prover.oneDigitNotZero(fakeSexp);
		GH.Prover.println('(0) (' + leftNum + ') (' + diff + ') addcan')
		GH.Prover.println('mtbir');
	
		result = GH.Prover.getLast().child();
		result = GH.Prover.replaceRight(GH.Prover.addSingleDigits, result);
		result = GH.Prover.additiveIdentity(result.left());
		
	GH.Prover.println('pm3.2i');
	GH.Prover.println('(' + leftNum + ') (' + rightNum + ') df-lt');
	GH.Prover.println('bicomi');
	GH.Prover.println('mpbi');
};

	
/** 
 * A tree with each node having a string representing some symbol. This is used
 * to specify how to rearrange the terms in GH.Prover.reposition. The symbol 
 * tree is constructed by parsing a string with symbols interpersed with parentheses.
 */
GH.symbolTree = function(symbol, left, right) {
	this.symbol = symbol;
	this.left = left;
	this.right = right;
};

// Generates a symbol tree from an expression like '(A (B C)) D'.
GH.symbolTree.fromString = function(str) {
	var depth = 0;
	str = GH.symbolTree.removeParentheses(str);
	var leftStart = null;
	var leftEnd = null;
	var rightStart = null;
	var rightEnd = null;
	
	for (var i = 0; i < str.length; i++) {
		var c = str.charAt(i);
		if (c != ' ') {
			if (leftStart == null) {
				leftStart = i;
			}
			if ((rightStart == null) && (leftEnd != null)) {
				rightStart = i;
			}		
			if (rightStart != null) {
				rightEnd = i + 1;
			}
		}

		if (c == '(') {
			depth++;
		} else if (c == ')') {
			depth--;
		} else if (c == ' ') {
			if ((depth == 0) && (leftStart != null)) {
				leftEnd = i;
			}
		}
	}
	if (rightStart == null) {
		return new GH.symbolTree(str, null, null);
	} else {
		var leftTree  = GH.symbolTree.fromString(str.substring(leftStart,  leftEnd));
		var rightTree = GH.symbolTree.fromString(str.substring(rightStart, rightEnd));
		return new GH.symbolTree(null, leftTree, rightTree);
	}
};

// Returns what is inside the first and last parentheses, remove everything else
// including the parentheses.
GH.symbolTree.removeParentheses = function(str) {
	var i = 0;
	var depth = 0;
	while (str.charAt(i) == ' ') {
		i++;
	}

	// If there are symbols before the first parentheses, return the original string.
	if (str.charAt(i) != '(') {
		return str;
	}
	var start = i + 1;
	var end = null;
	for (; i < str.length; i++) {
		var c = str.charAt(i);
		if (c == '(') {
			depth++;
		} else if (c == ')') {
			depth--;
			if (depth == 0) {
				end = i;
			}
		} else if ((end != null) && (c != ' ')) {
			// If there are symbols after the last parentheses, return the original string.
			return str;
		}
	}
	return str.substring(start, end);
};


// Associates a symbol tree to the right. Input: (A B) C, Output: A (B C)
// Similiar to GH.Prover.associateRight, but that applies to s-expressions.
GH.symbolTree.prototype.associateRight = function() {
	var a = this.left.left;
	var b = this.left.right;
	var c = this.right;

	this.left = a;
	this.right = new GH.symbolTree(null, b, c);
};

// Associates a symbol tree to the left. Input: A (B C), Output: (A B) C
// Similiar to GH.Prover.associateLeft, but that applies to s-expressions.
GH.symbolTree.prototype.associateLeft = function() {
	var a = this.left;
	var b = this.right.left;
	var c = this.right.right;

	this.left = new GH.symbolTree(null, a, b)
	this.right = c;
};

// Output the tree as an array of symbols.
GH.symbolTree.prototype.getSymbolList = function() {
	if (this.symbol != null) {
		return [this.symbol];
	} else {
		return this.left.getSymbolList().concat(this.right.getSymbolList());
	}
}

// For two list returns an array specifying how to reorder the terms in the
// first list to equal the second list.
GH.symbolTree.getSymbolOrder = function(oldList, newList) {
	if (oldList.length != newList.length) {
		alert('The two symbol list do not have the same number of symbols.');
	}
	var order = [];
	for (var i = 0; i < oldList.length; i++) {
		var matches = 0;
		for (var j = 0; j < newList.length; j++) {
			if (oldList[i] == newList[j]) {
				matches++;
				order.push(j);
			}
		}
		if (matches != 1) {
			alert('Mismatch in the symbol lists.');
		}
	}
	return order;
};