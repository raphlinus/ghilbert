// Javascript for generating Ghilbert proof steps automatically.
// by Paul Merrell, 2013

GH.Prover = function(suggestArea, direct) {
	this.depth = 0;
	this.direct = direct;
	this.conclusions = [];
	this.stackExp = null;
	this.suggestButtons_ = document.createElement('div');
	suggestArea.appendChild(this.suggestButtons_);

	this.remover = new GH.remover(this);
	this.replacer = new GH.replacer(this);
	this.repositioner = new GH.repositioner(this);
	this.commuter = new GH.ProofGenerator.commuter(this);
	this.evaluator = new GH.ProofGenerator.evaluator(this);
	this.distributorLeft  = new GH.ProofGenerator.distributorLeft(this);
	this.distributorRight = new GH.ProofGenerator.distributorRight(this);
	this.undistributorLeft  = new GH.ProofGenerator.undistributorLeft(this);
	this.undistributorRight = new GH.ProofGenerator.undistributorRight(this);
	this.associatorLeft  = new GH.ProofGenerator.associatorLeft(this);
	this.associatorRight = new GH.ProofGenerator.associatorRight(this);
};

GH.Prover.prototype.update = function(theorems, stack) {
	// Remove the existing buttons.
	while(this.suggestButtons_.firstChild){
    	this.suggestButtons_.removeChild(this.suggestButtons_.firstChild);
	}
	
	this.conclusions = GH.Prover.getConclusions(theorems);
	this.stackExp = null;
	if (stack.length == 1) {
		this.stackExp = new GH.sExpression(stack[0][1], null, null);
		if (this.evaluator.isApplicable(this.stackExp)) {
			this.addSuggestion('Evaluate', 'window.direct.prover.handleEvaluate()');
		}
		if (this.distributorLeft.isApplicable(this.stackExp)) {
			this.addSuggestion('Dist. L', 'window.direct.prover.handleDistributeLeft()');
		}
		if (this.distributorRight.isApplicable(this.stackExp)) {
			this.addSuggestion('Dist. R', 'window.direct.prover.handleDistributeRight()');
		}
		if (this.undistributorLeft.isApplicable(this.stackExp)) {
			this.addSuggestion('Undist. L', 'window.direct.prover.handleUndistributeLeft()');
		}
		if (this.undistributorRight.isApplicable(this.stackExp)) {
			this.addSuggestion('Undist. R', 'window.direct.prover.handleUndistributeRight()');
		}
		if (this.associatorLeft.isApplicable(this.stackExp)) {
			this.addSuggestion('Ass. L', 'window.direct.prover.handleAssociateLeft()');
		}
		if (this.associatorRight.isApplicable(this.stackExp)) {
			this.addSuggestion('Ass. R', 'window.direct.prover.handleAssociateRight()');
		}
	}

	if (stack.length == 0) {
		if (this.conclusions.length >= 1) {
			var lastConclusion = this.conclusions[this.conclusions.length - 1];
			if (this.commuter.isApplicable(lastConclusion)) {
				this.addSuggestion('Commute', 'window.direct.prover.handleCommute()');
			}
		}
	
		if (this.conclusions.length >= 2) {
			var prevConclusion = this.conclusions[this.conclusions.length - 2];
			if (prevConclusion && this.replacer.isReplaceable(prevConclusion, lastConclusion)) {
				this.addSuggestion('Substitute', 'window.direct.prover.handleSubstitute()');
			}
			if (prevConclusion && this.remover.maybeRemove(prevConclusion, lastConclusion)) {
				this.addSuggestion('Remove', 'window.direct.prover.handleRemove()');
			}
		}
	}
};

GH.Prover.prototype.addSuggestion = function(name, clickHandler) {
	var suggestion = document.createElement('input');
	suggestion.setAttribute('type', 'button');
	suggestion.setAttribute('value', name);
	suggestion.setAttribute('onclick', clickHandler);
	this.suggestButtons_.appendChild(suggestion);
};

GH.Prover.prototype.indent = function() {
	for (var i = 0; i < this.depth; i++) {
		this.direct.text.insertText('  ');
	}
};

// Print text into the proof.
GH.Prover.prototype.insertText = function(text) {
	this.direct.text.insertText(text);
};

// Insert an array of text into the beginning of the proof.
GH.Prover.prototype.insertBeginning = function(text) {
	var position = 0;
	for (var i = 0; i < text.length; i++) {
		this.direct.text.splice(position, 0, text[i] + '\n');
		position += text[i].length + 1;
	}
};

// Print text into the proof and add a new line.
GH.Prover.prototype.println = function(text) {
	this.indent();
	this.insertText(text + '\n');
};

// Insert a known theorem into the proof with all it's mandatory hypotheses.
GH.Prover.prototype.print = function(mandHyps, step) {
	this.indent();
	for (var i = 0; i < mandHyps.length; i++) {
		this.insertText(mandHyps[i].toString() + ' ');
	}
	this.insertText(step + '\n');
};

GH.Prover.prototype.makeString = function(mandHyps, step, output) {
	var result = '';
	for (var i = 0; i < this.depth; i++) {
		result += '  ';
	}
	for (var i = 0; i < mandHyps.length; i++) {
		result += mandHyps[i].toString() + ' ';
	}
	result += step;
	output.push(result);
};

// Returns a list of the theorems from the stack. The list contains
// all the conclusions of theorems converted into s-expressions.
GH.Prover.prototype.getTheorems = function() {
	// TODO: It may be better to get the theorems from GH.Prover.update instead.
	var theorems = this.direct.update();
	return GH.Prover.getConclusions(theorems);
};

GH.Prover.getConclusions = function(theorems) {
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
GH.Prover.prototype.getLast = function() {
	var theorems = this.getTheorems();
	return theorems[theorems.length -  1];
};
	
// Convert a number to an s-expression and insert it into the stack.
GH.Prover.prototype.printNum = function(num) {
	this.println(GH.numUtil.numToSexp(num));
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

	var matcherRoot = matcher;
	while(matcherRoot.parent_) {
		matcherRoot = matcherRoot.parent_;
	}
	if (GH.Prover.getType(matcherRoot) != 'wff') {
		// If the original expression is not a wff, the result is an equilance statement. Take the right part.	
		sexp = sexp.right();
	}

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
GH.Prover.prototype.replaceWith = function(generator, sexp) {
	var name = generator.stepName(sexp);
	this.depth++;
	this.println('## <d>');
	this.depth++;
	if (this.direct.vg.syms.hasOwnProperty(name)) {
		// Uses the proof if it already exists in the repository.
		var hyps = generator.hyps(sexp);
		this.print(hyps, name);
	} else {
		// If not already defined, generate the proof either as a new theorem or inline.
		var added = generator.addTheorem(sexp);
		if (!added) {
			added = generator.inline(sexp);
			if (!added) {
				alert(name + ' is not in the repository and cannot be generated.');
			}
		}
	}
	this.depth--;
	this.println('## </d>');
	this.depth--;

	return this.replacer.addReplaceThm(sexp);
};

GH.Prover.prototype.handleRemove = function() {
	this.direct.text.moveCursorToEnd();
	this.insertText(' ');
	var removee = this.conclusions[this.conclusions.length - 2];
	var remover = this.conclusions[this.conclusions.length - 1];
	var output = this.remover.maybeRemove(removee, remover);
	for (var i = 0; i < output.length; i++) {
		this.println(output[i]);
	}
	this.direct.update();
	
	output = [];
	removee = this.conclusions[this.conclusions.length - 1];
	this.remover.removeBoolean(removee, output);
	for (var i = 0; i < output.length; i++) {
		this.println(output[i]);
	}
	this.direct.update();
	// TODO: Replace a wff multiple times if it appears multiple times.
};

GH.Prover.prototype.symbolDefined = function(name) {
	if (name == null) {
		return false;
	}
	if (this.direct.vg.syms.hasOwnProperty(name)) {
		return true;
	}
	var newSyms = this.direct.thmctx.newSyms;
	for (var i = 0; i < newSyms.length; i++) {
		if (newSyms[i] == name) {
			return true;
		}
	}
	return false;
};

GH.Prover.EQUIVALENCE_OPERATOR = {
	wff: '<->',
	nat: '=',
	bind: '='
};

GH.Prover.getOperatorTypes = function(operator) {
	if (operator == '-.') 	return ['wff', 'wff'];
	if (operator == '->') 	return ['wff', 'wff', 'wff'];
	if (operator == '<->') 	return ['wff', 'wff', 'wff'];
	if (operator == '\\/') 	return ['wff', 'wff', 'wff'];
	if (operator == '/\\') 	return ['wff', 'wff', 'wff'];
	if (operator == 'A.') 	return ['bind', 'wff', 'wff'];
	if (operator == 'E.') 	return ['bind', 'wff', 'wff'];
	if (operator == '=') 	return ['nat', 'nat', 'wff'];
	if (operator == '<=') 	return ['nat', 'nat', 'wff'];
	if (operator == '<') 	return ['nat', 'nat', 'wff'];
	if (operator == '+') 	return ['nat', 'nat', 'nat'];
	if (operator == '*') 	return ['nat', 'nat', 'nat'];
	return null;
};

GH.Prover.getType = function(sexp) {
	var operator = sexp.operator_;
	var operatorTypes = GH.Prover.getOperatorTypes(operator);
	return operatorTypes && operatorTypes[operatorTypes.length - 1];
};

/**
 * From an s-expression and an expected form extracts all the hypotheses out of
 * the sexp. For example, if sexp = 2 * (3 + 4) and expectedForm = A * B, it will
 * extract two hypotheses A: 2 and B: 3 + 4. The hypotheses may be returned in the
 * wrong order.
 */
GH.Prover.prototype.getUnorderedHyps = function(sexp, expectedForm, hyps) {
	var operandsExpected = expectedForm.operands_.length;
	var operandsActual   =         sexp.operands_.length;
	// Every variable in the expected form may represent a large expression that has many operands, so it is
	// not a problem if there are operands when we expect none.
	if ((operandsExpected != operandsActual) && (operandsExpected != 0)) {
		return null;
	} else if (operandsExpected > 0) {
		var operatorExpected = expectedForm.operator_.toString();
		var operatorActual   =         sexp.operator_.toString();
		if ((operatorExpected != operatorActual) && (operatorExpected != 'operator')) {
			return null;
		} else {
			for (var i = 0; i < operandsExpected; i++) {
				hyps = this.getUnorderedHyps(sexp.operands_[i], expectedForm.operands_[i], hyps);
				if (hyps == null) {
					return null;
				}
			}
			return hyps;
		}
	} else {
		var expression = expectedForm.getExpression();
		if ((expression in hyps) && (!hyps[expression].equals(sexp))) {
			return null;
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
GH.Prover.prototype.getHyps = function(sexp, expectedForm) {
	var hyps = this.getUnorderedHyps(sexp, expectedForm, {});
	if (hyps == null) {
		return null;
	}

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
GH.Prover.prototype.setHyps = function(expectedForm, newHyps) {
	var sexp = expectedForm.copy(null);
	var hyps = this.getUnorderedHyps(sexp, expectedForm, {});
	var keys = [];
	for (var i = 0; i < GH.Prover.defaultOrder.length; i++) {
		var key = GH.Prover.defaultOrder[i];
		if (key in hyps) {
			keys.push(key);
		}
	}
	return this.setHypsWithKeys(sexp, keys, newHyps);
};

// Fill in an s-expresson from with a set of key and hyps.
// For example, if sexp = A * B, and keys = [A, B] and hyps = [2, 3 + 4],
// then this function returns the expression 2 * (3 + 4).
GH.Prover.prototype.setHypsWithKeys = function(sexp, keys, hyps) {
	var operandsNum = sexp.operands_.length;
	if (operandsNum > 0) {
		for (var i = 0; i < operandsNum; i++) {
			sexp = this.setHypsWithKeys(sexp.operands_[i], keys, hyps).parent_;
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
GH.Prover.prototype.addTheorem = function(generator, sexp) {
	this.insertText('thm (' + generator.stepName(this, sexp) + ' ' + generator.header(this, sexp) + ' ');
	var conclusionPosition = this.direct.text.getCursorPosition();
	var fakeConclusion = '(= (0) (1))';
	this.insertText(fakeConclusion);
	this.insertText('\n');
	this.depth++;
	generator.body(prover, sexp);
	this.depth--;
	this.println(')');
	var conclusion = this.getLast();
	this.direct.text.splice(conclusionPosition, fakeConclusion.length, conclusion);
	this.direct.update();
};

GH.ProofGenerator = {};

GH.Prover.prototype.replace = function(sexp) {
	return this.replacer.getReplaced(sexp);
};

GH.Prover.prototype.reposition = function(sexp, oldPosition, newPosition) {
	return this.repositioner.reposition(sexp, oldPosition, newPosition);
};

GH.Prover.prototype.clearStack = function() {
	var begin = this.stackExp.begin;
	var end = this.stackExp.end;
	this.direct.text.splice(begin, end - begin, '');
};

GH.Prover.prototype.associateLeft = function(sexp) {
	return this.replaceWith(this.associatorLeft, sexp);
};

GH.Prover.prototype.associateRight = function(sexp) {
	return this.replaceWith(this.associatorRight, sexp);
};

GH.Prover.prototype.distributeLeft = function(sexp) {
	return this.replaceWith(this.distributorLeft, sexp);
};

GH.Prover.prototype.distributeRight = function(sexp) {
	return this.replaceWith(this.distributorRight, sexp);
};

GH.Prover.prototype.undistributeLeft = function(sexp) {
	return this.replaceWith(this.undistributorLeft, sexp);
};

GH.Prover.prototype.undistributeRight = function(sexp) {
	return this.replaceWith(this.undistributorRight, sexp);
};

GH.Prover.prototype.evaluate = function(sexp) {
	return this.replaceWith(this.evaluator, sexp);
};

GH.Prover.prototype.commute = function(sexp) {
	if (sexp.left().equals(sexp.right())) {  // No need to commute when both sides are the same.
		return sexp;
	} else {
		return this.replaceWith(this.commuter, sexp);
	}
};

GH.Prover.prototype.handleCommute = function() {
	this.direct.text.moveCursorToEnd();
	this.insertText(' ');
	var lastConclusion = this.conclusions[this.conclusions.length - 1];
	this.commute(lastConclusion);
};

GH.Prover.prototype.handleEvaluate = function() {
	this.clearStack();
	this.direct.text.moveCursorToEnd();
	this.insertText(' ');
	this.replaceWith(this.evaluator, this.stackExp);
};

GH.Prover.prototype.handleDistributeLeft = function() {
	this.clearStack();
	this.direct.text.moveCursorToEnd();
	this.insertText(' ');
	this.replaceWith(this.distributorLeft, this.stackExp);
};

GH.Prover.prototype.handleDistributeRight = function() {
	this.clearStack();
	this.direct.text.moveCursorToEnd();
	this.insertText(' ');
	this.replaceWith(this.distributorRight, this.stackExp);
};

GH.Prover.prototype.handleUndistributeLeft = function() {
	this.clearStack();
	this.direct.text.moveCursorToEnd();
	this.insertText(' ');
	this.replaceWith(this.undistributorLeft, this.stackExp);
};

GH.Prover.prototype.handleUndistributeRight = function() {
	this.clearStack();
	this.direct.text.moveCursorToEnd();
	this.insertText(' ');
	this.replaceWith(this.undistributorRight, this.stackExp);
};

GH.Prover.prototype.handleAssociateLeft = function() {
	this.clearStack();
	this.direct.text.moveCursorToEnd();
	this.insertText(' ');
	this.replaceWith(this.associatorLeft, this.stackExp);
};

GH.Prover.prototype.handleAssociateRight = function() {
	this.clearStack();
	this.direct.text.moveCursorToEnd();
	this.insertText(' ');
	this.replaceWith(this.associatorRight, this.stackExp);
};

GH.Prover.findMatch = function(sexp, matchee) {
	if (sexp.equals(matchee)) {
		return sexp;
	} else {
		for (var i = 0; i < sexp.operands_.length; i++) {
			var foundMatch = GH.Prover.findMatch(sexp.operands_[i], matchee);
			if (foundMatch) {
				return foundMatch;
			}
		}
		return null;
	}
};

GH.Prover.prototype.handleSubstitute = function() {
	this.direct.text.moveCursorToEnd();
	this.insertText(' ');
	var replacee = this.conclusions[this.conclusions.length - 2];
	var replacement = this.conclusions[this.conclusions.length - 1];
	var myMatch = GH.Prover.findMatch(replacee, replacement.left());
	replacee = this.replacer.addReplaceThm(myMatch);

	// TODO: Replace a value multiple times if it appears multiple times.
	/*while (myMatch) {
		replacee = this.replacer.addReplaceThm(myMatch);
		myMatch = GH.Prover.findMatch(replacee, replacement.left());
	}*/
};

// Apply a function to the right side of an s-expression. This does not change
// the position of the s-expression.
GH.Prover.applyRight = function(applyFunc, sexp, caller) {
	return applyFunc.call(caller, sexp.right()).parent_;
};

// Apply a function to the right side of an s-expression. This does not change
// the position of the s-expression.
GH.Prover.applyLeft = function(applyFunc, sexp, caller) {
	return applyFunc.call(caller, sexp.left()).parent_;
};

// Apply a function to the right side of an s-expression. This does not change
// the position of the s-expression.
GH.Prover.prototype.applyRight = function(applyFunc, sexp) {
	return applyFunc.call(this, sexp.right()).parent_;
};

// Apply a function to the left side of an s-expression. This does not change
// the position of the s-expression.
GH.Prover.prototype.applyLeft = function(applyFunc, sexp) {
	return applyFunc.call(this, sexp.left()).parent_;
};

// Replace the left side of an s-expression. This does not change the position
// of the s-expression.
GH.Prover.prototype.replaceLeft = function(generator, sexp) {
	return this.replaceWith(generator, sexp.left()).parent_;
};

// Replace the right side of an s-expression. This does not change the position
// of the s-expression.
GH.Prover.prototype.replaceRight = function(generator, sexp) {
	return this.replaceWith(generator, sexp.right()).parent_;
};