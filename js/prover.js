// Javascript for generating Ghilbert proof steps automatically.
// by Paul Merrell, 2013

GH.Prover = function(suggestArea, direct) {
	this.depth = 0;
	this.direct = direct;
	this.conclusions = [];
	this.suggestButtons_ = document.createElement('div');
	suggestArea.appendChild(this.suggestButtons_);
};

GH.Prover.prototype.update = function(theorems) {
	while(this.suggestButtons_.firstChild){
    	this.suggestButtons_.removeChild(this.suggestButtons_.firstChild);
	}

	this.conclusions = GH.Prover.getConclusions(theorems);
	
	if (this.conclusions.length >= 1) {
		var lastConclusion = this.conclusions[this.conclusions.length - 1];
		if (this.commuteStep(lastConclusion)) {
			this.addSuggestion('Commute', 'window.direct.prover.handleCommute()');
		}
	}
	
	if (this.conclusions.length >= 2) {
		var prevConclusion = this.conclusions[this.conclusions.length - 2];
		if (prevConclusion && this.isReplaceable(prevConclusion, lastConclusion)) {
			this.addSuggestion('Substitute', 'window.direct.prover.handleSubstitute()');
		}
		if (prevConclusion && this.maybeRemove(prevConclusion, lastConclusion)) {
			this.addSuggestion('Remove', 'window.direct.prover.handleRemove()');
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

// This is a bit of a hack.
GH.Prover.prototype.printBeforeLastStep = function(text) {
	var theorems = this.direct.update();
	var start = theorems[theorems.length - 1].begin;
	this.direct.text.splice(start, 0, text);
};

// Returns a list of the theorems from the stack. The list contains
// all the conclusions of theorems converted into s-expressions.
GH.Prover.prototype.getTheorems = function() {
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
	
// Convert from a number to an s-expression. Only the numbers 0 to 10 are defined
// in Ghilbert, so multi-digit numbers are formed by combining these digits according
// to the standard base-10 numbering system.
GH.Prover.prototype.numToSexp = function(num) {
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
		return '(* (' + value.toString() + ') ' + this.numToSexp(digit) + ')';
	} else {
		// If there are lower digits, add the upper and lower digit numbers.
		var lowerDigits = this.numToSexp(remainder);
		var upperDigits = this.numToSexp(upperDigit);
		return '(+ ' + upperDigits + ' ' + lowerDigits + ') ';
	}
};
	
// Convert an s-expression into a number.
// Simply performs all the multiplication and additions within the expression.
GH.Prover.prototype.sexpToNum = function(sexp) {
	if (sexp.operator_ == '*') {
		return this.sexpToNum(sexp.left()) * this.sexpToNum(sexp.right());
	} else if (sexp.operator_ == '+') {
		return this.sexpToNum(sexp.left()) + this.sexpToNum(sexp.right());
	} else {
		return parseInt(sexp.operator_);
	}
};
	
// Returns true if x is a power of ten.
GH.Prover.prototype.isPowerOfTen = function(x) {
	while (x % 10 == 0) {
		x /= 10;
	}
	return (x == 1);
};
	
// Convert a number to an s-expression and insert it into the stack.
GH.Prover.prototype.printNum = function(num) {
	this.println(this.numToSexp(num));
};

// TODO: Rename and describe function.
GH.Prover.prototype.findPosition = function(sexp) {
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
GH.Prover.prototype.findMatchingPosition = function(sexp, matcher) {
	var indices = this.findPosition(matcher);

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
	var name = generator.name(this, sexp);
	// TODO: Remove references to window.
	this.depth++;
	this.println('## <d>');
	this.depth++;
	if (this.direct.vg.syms.hasOwnProperty(name)) {
		// Uses the proof if it already exists in the repository.
		var hyps = generator.hyps(this, sexp);
		this.print(hyps, name);
	} else {
		// Generates a proof when the proof is not in the repository.
		generator.body(this, sexp);
	}
	this.depth--;
	this.println('## </d>');
	this.depth--;

	return this.addReplaceThm(sexp);
};

GH.Prover.prototype.symbolDefined = function(name) {
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

GH.Prover.prototype.addReplaceThm = function(sexp) {
	var position = this.findPosition(sexp);
	var name = '';
	// What happens when position.length is 1?
	if (position.length > 0) {
		var replacement = this.getLast();
		name = GH.Prover.replaceThmName(sexp, position);
		if (!this.symbolDefined(name)) {
			var replaceThm = this.createGeneric(position.slice(0), sexp, replacement, name);
			var position = 0;
			for (var i = 0; i < replaceThm.length; i++) {
				this.direct.text.splice(position, 0, replaceThm[i] + '\n');
				position += replaceThm[i].length + 1;
			}
		}
		this.depth++;
	}
	this.println(name);
	if (position.length > 0) {
		this.depth--;
	}

	var replaced = this.getLast();
	if (sexp.parent_) {
		return this.findMatchingPosition(replaced, sexp);
	} else {
		return replacement.right();
	}
};

GH.Prover.prototype.createGeneric = function(position, replacee, replacement, name) {
	var output = [];
	while (replacee.parent_ != null) {
		replacee = replacee.parent_;
	}
	var start = [];
	var end = [];
	var middle = [];
	var usedVariables = { wff: 0, nat: 0, bind: 0};
	this.genericCopies(start, end, middle, position.slice(0), replacee, replacement, usedVariables);

	var startString  = GH.sexp_to_string(start);
	var middleString = GH.sexp_to_string(middle);
	var endString    = GH.sexp_to_string(end);

	GH.Prover.removeStyling(start);
	GH.Prover.removeStyling(middle);
	GH.Prover.removeStyling(end);
	var startExp  = new GH.sExpression(start,  null, null);
	var middleExp = new GH.sExpression(middle, null, null);
	var endExp    = new GH.sExpression(end,    null, null);
	
	var spacedColumns = this.spaceColumns([startString, middleString, endString]);

	output.push('## <title> Substitution </title>');
	output.push('## <table>');
	output.push('##   '	+ spacedColumns[0]);
	output.push('##   '	+ spacedColumns[1]);
	output.push('##   '	+ spacedColumns[2]);
	output.push('## </table>');
	output.push('thm (' + name + ' () (');
	output.push('     replacee ' + startExp.toString());
	output.push('     substitution ' + middleExp.toString() + ') ');
	output.push('     ' + endExp.toString());
	output.push('  replacee');
	output.push('  substitution');

	this.depth++;
	for (var i = 0; i < position.length; i++) {
		startExp = startExp.operands_[position[i]];
	}
	this.replace(startExp, output);
	this.depth--;
	output.push(')');
	output.push('');
	return output;
};

GH.Prover.replaceThmName = function(sexp, position) {
	var temp = sexp;
	while (temp.parent_ != null) {
		temp = temp.parent_;
	}
	var result = '';
	for (var i = 0; i < position.length; i++) {
		var operator = temp.operator_;		
		var name = '';
 		       if (operator == '-.') {		name = 'not';
		} else if (operator == '->') {		name = 'imp';		
		} else if (operator == '<->') {		name = 'bi';
		} else if (operator == '\\/') {		name = 'or';
		} else if (operator == '/\\') {		name = 'an';
		} else if (operator == 'A.') {		name = 'al';
		} else if (operator == 'E.') {		name = 'ex';
		} else if (operator == '=') {		name = 'eq';
		} else if (operator == '<=') {		name = 'le';
		} else if (operator == '<') {		name = 'lt';
		} else if (operator == '+') {		name = 'add';
		} else if (operator == '*') {		name = 'mul';
		} else {
			alert('Operator ' + operator + ' is not named.');
		}
		result += name + position[i];
		temp = temp.operands_[position[i]];
	}
	return result;
};

GH.Prover.prototype.spaceColumns = function(strings) {
	var matches = [];
	for (var i = 0; i < strings.length; i++) {
		var re = / \[| \]/g;
		var indices = [];
		while ((match = re.exec(strings[i])) != null) {
			indices.push(match.index);
		}
		matches.push(indices);
	}
	for (var i = indices.length - 1; i >= 0; i--) {
		var maxWidth = 0;
		for (var j = 0; j < strings.length; j++) {
			var width = matches[j][i] - ((i > 0) ? matches[j][i - 1] : 0);
			maxWidth = Math.max(maxWidth, width);
		}
		for (var j = 0; j < strings.length; j++) {
			var width = matches[j][i] - ((i > 0) ? matches[j][i - 1] : 0);
			var delta = maxWidth - width;
			var insertion = '';
			for (var k = 0; k < delta; k++) {
				insertion += ' ';
			}
			strings[j] = strings[j].slice(0, matches[j][i]) + insertion + strings[j].slice(matches[j][i], strings[j].length);
		}
	}
	return strings;
};

GH.Prover.removeStyling = function(sexp) {
    if (typeof sexp == 'string') {
		sexp = sexp.replace(/ |\[|\]/g, '')
	}
	for (var i = 1; i < sexp.length; i++) {
		if (typeof sexp[i] == 'string') {
			sexp[i] = sexp[i].replace(/ |\[|\]/g, '')
		} else {
			GH.Prover.removeStyling(sexp[i]);
		}
	}
};

GH.Prover.prototype.genericCopies = function(start, end, middle, positions, replacee, replacement, usedVariables) {
	var operand = positions.splice(0, 1);
	var operator = replacee.operator_;
	start.push(operator);
	end.push(operator);
	var types = GH.Prover.getOperatorTypes(operator);
	for (var i = 0; i < types.length - 1; i++) {
		if (i != operand) {
			var variable = this.grabNextVariable(usedVariables, types[i]);
			start.push(variable);
			end.push(variable);
		} else {
			if (positions.length > 0) {
				start.push([]);
				end.push([]);
				this.genericCopies(start[i + 1], end[i + 1], middle, positions, replacee.operands_[i], replacement, usedVariables);
			} else {
				var operator = replacement.operator_;
				var types = GH.Prover.getOperatorTypes(operator);
				var leftVariable  = this.grabNextVariable(usedVariables, types[0]);
				var rightVariable = this.grabNextVariable(usedVariables, types[1]);
				
				middle.push(operator);
				middle.push(' [ ' + leftVariable + ' ] ')
				middle.push(' [ ' + rightVariable + ' ] ')
				start.push(' [ ' + leftVariable + ' ] ] ] ');
				end.push(' [ [ [ ' + rightVariable + ' ] ');
			}
		}
	}
};

GH.Prover.prototype.grabNextVariable = function(usedVariables, type) {
	if (GH.Prover.VARIABLE_NAMES[type].length <= usedVariables[type]) {
		alert('No more unused variable names.');
	}
	var result = GH.Prover.VARIABLE_NAMES[type][usedVariables[type]];
	usedVariables[type]++;
	return result;
};

GH.Prover.VARIABLE_NAMES = {
	wff: ['ph', 'ps', 'ch', 'th', 'ta'],
	nat: ['A', 'B', 'C', 'D', 'A\'', 'B\'', 'C\'', 'D\''], 
	bind: ['x', 'y', 'z', 'v', 'w\'', 'x\'', 'y\'', 'z\'', 'v\'', 'w\'']
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
				hyps = this.getUnorderedHyps(sexp.operands_[i], expectedForm.operands_[i], hyps);
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
GH.Prover.prototype.getHyps = function(sexp, expectedForm) {
	var hyps = this.getUnorderedHyps(sexp, expectedForm, {});
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
	this.insertText('thm (' + generator.name(this, sexp) + ' ' + generator.header(this, sexp) + ' ');
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


GH.Prover.REMOVE_OPERATIONS = [
	[ '->', ['impRemove1', 'impRemove2'], ['impNotRemove1', 'impNotRemove2']],
	['<->', [ 'biRemove1',  'biRemove2'], [ 'biNotRemove1',  'biNotRemove2']],
	['\\/', [ 'orRemove1',  'orRemove2'], [ 'orNotRemove1',  'orNotRemove2']], 
	['/\\',	[ 'anRemove1',  'anRemove2'], [ 'anNotRemove1',  'anNotRemove2']]
];

// TODO: Use shorthand operations.
// These could be used to remove part of an expression with no parent. These could be used
// instead of the remove operations except the hypotheses are in the wrong order.
GH.Prover.REMOVE_SHORTHAND_OPERATIONS = [
	[ '->', ['ax-mpRemove', null], [null, 'mtoRemove']],
	['<->', [ 'mpbiRemove', 'mpbirRemove'], [ 'mtbiRemove',  'mtbirRemove']]
];

GH.Prover.prototype.remove = function(removee, isNegated, output) {
	var parent = removee.parent_;
	var operandIndex = removee.siblingIndex_;
	if (!parent) {
		// The remover and the removee are identical.
		return false;
	}
		
	var operator = parent.operator_;
	
	var shorthandOperations = GH.Prover.REMOVE_SHORTHAND_OPERATIONS;
	if (!parent.parent_) {
		for (var i = 0; i < shorthandOperations.length; i++) {
			if (operator == shorthandOperations[i][0]) {
				var stepName = null;
				if (!isNegated) {
					stepName = shorthandOperations[i][1][operandIndex];
				} else {
					stepName = shorthandOperations[i][2][operandIndex];
				}
				if ((!stepName) || (!this.symbolDefined(stepName))) {
					return false;
				}
				this.makeString([], stepName, output);
				return true;
			}
		}
	}
	
	var removeOperations = GH.Prover.REMOVE_OPERATIONS;
	for (var i = 0; i < removeOperations.length; i++) {
		if (operator == removeOperations[i][0]) {
			var mandHyps = [];
			var stepName = null;
			//if (parent.parent_) {
			mandHyps.push(parent.operands_[1 - operandIndex]);
			if (!isNegated) {
				stepName = removeOperations[i][1][operandIndex];
			} else {
				stepName = removeOperations[i][2][operandIndex];
			}
			if ((!stepName) || (!this.symbolDefined(stepName))) {
				return false;
			}
			this.makeString(mandHyps, stepName, output);
		}
	}

	// Recursively replace the entire replacee follow the expression up to the root.
	var success;
	if (parent.parent_) {
		return this.replace(parent, output);
	} else {
		output.push('mpbi');
		return true;
	}
};

GH.Prover.prototype.removeBoolean = function(removee, output) {
	var myMatch = GH.Prover.findMatch(removee, new GH.sExpression('T'));	
	if (myMatch && myMatch.parent_) {
		output.push('tru');
		this.remove(myMatch, false, output);
	}
	myMatch = GH.Prover.findMatch(removee, new GH.sExpression('F'));	
	if (myMatch && myMatch.parent_) {
		output.push('notfal');
		this.remove(myMatch, true, output);
	}
};

// A set of theorems for replacing some part of an expression. One for each operator.
// Each operator has two groups of theorems. The first group is for when the expression
// has a parent. The second group is for when the expression does not. Within each group
// there is one theorem for each operand.
GH.Prover.REPLACE_OPERATIONS = [
	[ '-.', ['con4biir'], ['mtbi']],
	[ '->', ['imbi1i', 'imbi2i'], ['sylbi2', 'sylib']],
	['<->', ['bibi1i', 'bibi2i'], ['bitr3icom', 'bitri']],
	['\\/', ['orbi1i', 'orbi2i'], ['orbi1ii', 'orbi2ii']],
	['/\\',	['anbi1i', 'anbi2i'], ['anbi1ii', 'anbi2ii']],
	['A.',  [null,     'albii' ], [null,      'albiii' ]],
	['E.',  [null,     'exbii' ], [null,      'exbiii' ]],
	['=',   ['eqeq1i', 'eqeq2i'], ['eqtr5',   'eqtr'   ]],
	['<=',  ['leeq1i', 'leeq2i'], ['leeq1ii', 'leeq2ii']],
	['<',   ['lteq1i', 'lteq2i'], ['lteq1ii', 'lteq2ii']],
	['+',	['addeq1i','addeq2i'], [null, null]],
	['*',   ['muleq1i','muleq2i'], [null, null]]
];


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
 *
 * Returns true if the replacement was successful.
 */
GH.Prover.prototype.replace = function(replacee, output) {
	var parent = replacee.parent_;
	var operandIndex = replacee.siblingIndex_;
	if (!parent) {
		return true;
	}
		
	var operator = parent.operator_;
	var types = GH.Prover.getOperatorTypes(operator);
	if (types == null) {
		return false;
	}

	var replaceOperations = GH.Prover.REPLACE_OPERATIONS;
	for (var i = 0; i < replaceOperations.length; i++) {
		if (operator == replaceOperations[i][0]) {
			var mandHyps = [];
			var stepName = null;
			if (parent.parent_) {
				// Add all the operands that are not getting replaced.
				for (var j = 0; j < types.length - 1; j++) {
					if (j != operandIndex) {
						mandHyps.push(parent.operands_[j]);
					}
				}
				stepName = replaceOperations[i][1][operandIndex];
			} else {
				stepName = replaceOperations[i][2][operandIndex];
			}
			if ((!stepName) || (!this.symbolDefined(stepName))) {
				return false;
			}
			this.makeString(mandHyps, stepName, output)
		}
	}

	// Recursively replace the entire replacee follow the expression up to the root.
	if (parent.parent_) {
		return this.replace(parent, output);
	} else {
		return true;
	}
};

// Replace the s-expression replacee using the last statement on the proof stack.
/*GH.Prover.prototype.getReplaced = function(replacee) {
	var replacement = this.getLast();
	if (replacee.parent_) {
		var printOutput = [];
		var replaced = this.replace(replacee, printOutput);
		return this.findMatchingPosition(replaced, replacee);
	} else {
		return replacement.right();
	}
};*/

// Replace the s-expression replacee using the last statement on the proof stack.
GH.Prover.prototype.getReplaced = function(replacee) {
	var printOutput = [];
	this.createReplaceThm(replacee, printOutput);
	for (var i = 0; i < printOutput.length; i++) {
		this.println(printOutput[i]);
	}
	result = this.getLast();
	result = this.findMatchingPosition(result, replacee);
	return result;
};

// Replace the s-expression replacee using the last statement on the proof stack.
GH.Prover.prototype.createReplaceThm = function(replacee, output) {
	// TODO: Return output.

	var replacement = this.getLast();
	if (replacee.parent_) {
		this.replace(replacee, output);
		//var replaced = this.replace(replacee, output);
		//return this.findMatchingPosition(replaced, replacee);
	}/* else {
		return replacement.right();
	}*/
};

// A set of commutable operators and the theorem for commuting them.
// The first step is for when the expression has a parent.
// The second step is when the expression has no parent.
GH.Prover.COMMUTE_OPERATIONS = [
  ['<->', 'bicom', 'bicomi'],
  ['/\\', 'ancom', 'ancomi'],
  ['\\/', 'orcom', 'orcomi'],
  [ '=' , 'eqcom', 'eqcomi'],
  [ '+' , 'addcom', null],
  [ '*' , 'mulcom', null]
];

GH.Prover.prototype.commuteStep = function(sexp) {
	if (sexp.operands_.length != 2) {
		return null;
	}
	// Commuting is unnecessary if the left and right sides are equal.
	if (sexp.left().equals(sexp.right())) {
		return null;
	}

	var commuteOperations = GH.Prover.COMMUTE_OPERATIONS;
	for (var i = 0; i < commuteOperations.length; i++) {
		if (sexp.operator_ == commuteOperations[i][0]) {
			var stepName;
			if (sexp.parent) {
				stepName = commuteOperations[i][1];
			} else {
				stepName = commuteOperations[i][2];
			}
			return (this.symbolDefined(stepName)) ? stepName : null;
		}
	}
	return null;
};
  
// Commmute the operands of an s-expression.	
GH.Prover.prototype.commute = function(sexp) {
	var step = this.commuteStep(sexp);
	if (!step) {
		return sexp;
	}
	if (sexp.parent_) {
		this.print([sexp.left(), sexp.right()], step);
	} else {
		this.print([], step);
	}
	return this.getReplaced(sexp);
};

GH.Prover.prototype.handleCommute = function() {
	this.direct.text.moveCursorToEnd();
	this.insertText(' ');
	var lastConclusion = this.conclusions[this.conclusions.length - 1];
	this.commute(lastConclusion);
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
	replacee = this.addReplaceThm(myMatch);

	// TODO: Replace a value multiple times if it appears multiple times.
	/*while (myMatch) {
		replacee = this.addReplaceThm(myMatch);
		myMatch = GH.Prover.findMatch(replacee, replacement.left());
	}*/
};

GH.Prover.prototype.isReplaceable = function(replacee, replacement) {
	// Replacing does nothing if the left and right sides are equal.
	if ((replacement.operands_.length != 2) || (replacement.left().equals(replacement.right()))) {
		return false;
	}
	// Check that the operator is an equivalence operator.
	var operatorTypes = GH.Prover.getOperatorTypes(replacement.operator_);
	if ((!operatorTypes) || (replacement.operator_ != GH.Prover.EQUIVALENCE_OPERATOR[operatorTypes[0]])) {
		return false;
	}
	var myMatch = GH.Prover.findMatch(replacee, replacement.left());
	if (!myMatch) {
		return false;
	}
	var unusedOutput = [];
	return this.replace(myMatch, unusedOutput);
};


GH.Prover.prototype.handleRemove = function() {
	this.direct.text.moveCursorToEnd();
	this.insertText(' ');
	var removee = this.conclusions[this.conclusions.length - 2];
	var remover = this.conclusions[this.conclusions.length - 1];
	var output = this.maybeRemove(removee, remover);
	for (var i = 0; i < output.length; i++) {
		this.println(output[i]);
	}
	this.direct.update();
	
	output = [];
	removee = this.conclusions[this.conclusions.length - 1];
	this.removeBoolean(removee, output);
	for (var i = 0; i < output.length; i++) {
		this.println(output[i]);
	}
	this.direct.update();
	// TODO: Replace a wff multiple times if it appears multiple times.
};


GH.Prover.prototype.maybeRemove = function(removee, remover) {
	var output = [];
	var isNegated = false;
	var myMatch = GH.Prover.findMatch(removee, remover);
	if (myMatch && myMatch.parent_ && (myMatch.parent_.operator_ == '-.')) {
		output.push('notnoti');
		isNegated = true;
		myMatch = myMatch.parent_;
	}
	if ((!myMatch) && (remover.operator_ == '-.')) {
		isNegated = true;
		myMatch = GH.Prover.findMatch(removee, remover.child());
	}

	if (!myMatch) {
		return null;
	} else {
		var success = this.remove(myMatch, isNegated, output);
		if (success) {
			return output;
		} else {
			return null;
		}
	}
};

// Apply the associative property on an s-expression. This does the same thing as
// reposition(result, 'A (B C)', '(A B) C');
GH.Prover.prototype.associateLeft = function(sexp) {
	var operator = sexp.operator_;
	var mandHyps = [sexp.left(), sexp.right().left(), sexp.right().right()];
	if (operator == '+') {
		if (sexp.right().operator_ != '+') {
			alert('No rule available for associating the ' + operator + '  and ' + sexp.right().operator_ + ' operators.');
			return null;
		}
		this.print(mandHyps, 'addass');
		this.print([], 'eqcomi');
		return this.getReplaced(sexp);
	} else {
		alert('No rule available for associating the ' + operator + ' operator.');
		return null;
	}
};

// Apply the associative property on an s-expression. This does the same thing as
// reposition(result, '(A B) C', 'A (B C)');	
GH.Prover.prototype.associateRight = function(sexp) {
	var operator = sexp.operator_;
	var mandHyps = [sexp.left().left(), sexp.left().right(), sexp.right()];
	if (operator == '+') {
		if (sexp.left().operator_ != '+') {
			alert('No rule available for associating the ' + operator + '  and ' + sexp.left().operator_ + ' operators.');
			return null;
		}
		this.print(mandHyps, 'addass');
		return this.getReplaced(sexp);
	} else {
		alert('No rule available for associating the ' + operator + ' operator.');
		return null;
	}
};

// Replace a single-digit number with its predessor on the left.
// For example, 5 = 4 + 1.
GH.Prover.prototype.predecessorLeft = function(sexp) {
	var num = sexp.operator_;
	this.print([], 'df-' + num);
	return this.getReplaced(sexp);
};

// Replace a single-digit number with its predecessor on the right.
// For example, 5 = 1 + 4.
GH.Prover.prototype.predecessorRight = function(sexp) {
	var num = sexp.operator_;
	this.print([], 'df-' + num);
	var replacement = this.getLast();
	this.commute(replacement.right());
	return this.getReplaced(sexp);
};

// Replace a single-digit number on the left with its successor.
// For example, 4 + 1 = 5.
GH.Prover.prototype.successorLeft = function(sexp) {
	var num = sexp.left().operator_;
	this.print([], 'df-' + (parseInt(num) + 1));
	var replacement = this.getLast();
	this.commute(replacement);
	return this.getReplaced(sexp);
};

// Replace a single-digit number on the left with its successor.
// For example, 1 + 4 = 5.	
GH.Prover.prototype.successorRight = function(sexp) {
	var num = sexp.right().operator_;
	this.print([], 'df-' + (parseInt(num) + 1));
	var replacement = this.getLast();
	replacement = this.applyRight(this.commute, replacement);
	this.commute(replacement);
	return this.getReplaced(sexp, replacement);
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

// Use the additive identity to simplify expressions like 5 + 0 to 5.
GH.Prover.prototype.additiveIdentity = function(sexp) {
	if (sexp.operator_ == '+') {
		if (sexp.left().operator_ == '0') {
			this.print([sexp.right()], 'pa_ax3r');
			return this.getReplaced(sexp);
		} else if (sexp.right().operator_ == '0') {
			this.print([sexp.left()], 'pa_ax3r');
			this.commute(this.getLast().left());
			return this.getReplaced(sexp);
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
GH.Prover.addSingleDigits.name = function(prover, sexp) {
	var hyps = prover.getHyps(sexp, this.expectedForm);
	return hyps[0].operator_ + 'plus' + hyps[1].operator_;
};

// Returns the mandatory hypotheses for the theorem given an s-expression.
// addSingleDigits has no mandatory hypotheses.
GH.Prover.addSingleDigits.hyps = function(prover, sexp) {
	return [];
};

// Returns a header of the theorem contain the theorem hypotheses and the freeness
// constraints. Both are empty in this case.
GH.Prover.addSingleDigits.header = function(prover, sexp) {
	return '() ()';
};

// Generate a full theorem given two single digit numbers.
GH.Prover.addSingleDigits.makeTheorem = function(prover, leftNum, rightNum) {
	// Create an s-expression in the expected form with the left and right numbers.
	var leftHyp  = GH.sExpression.fromString('(' + leftNum  + ')');
	var rightHyp = GH.sExpression.fromString('(' + rightNum + ')');
	var sexp = this.prover.setHyps(this.expectedForm, [leftHyp, rightHyp]);
	prover.addTheorem(this, sexp);
};

// The body of the addSingleDigits proof generator. Takes an expression like 2 + 2
// and finds their sum: 2 + 2 = 4.
GH.Prover.addSingleDigits.body = function(prover, sexp) {
	var  leftNum = parseInt(sexp.left().operator_);
	var rightNum = parseInt(sexp.right().operator_);
	var result = sexp.copy();
	result = prover.additiveIdentity(result);

	// We increment the higher number and decrement the lower number until
	// we've reach 10 or until the lower number is zero.
	if (rightNum < leftNum) {
		while ((rightNum > 0) && (leftNum < 10)) {
			if (rightNum > 1) {
				result = prover.applyRight(prover.predecessorRight, result);
				result = prover.associateLeft(result);
				result = prover.applyLeft(prover.successorLeft, result);
			} else {
				result = prover.successorLeft(result);
			}
			rightNum--;
			leftNum++;
		}
	} else {
		while ((leftNum > 0) && (rightNum < 10)) {
			if (leftNum > 1) {
				result = prover.applyLeft(prover.predecessorLeft, result);
				result = prover.associateRight(result);
				result = prover.applyRight(prover.successorRight, result);
			} else {
				result = prover.successorRight(result);
			}
			rightNum++;
			leftNum--;
		}
		if ((rightNum == 10) && (leftNum > 0)) {
			result = prover.commute(result);
		}
	}
	return result;
};

// Replace a number x with 1 * x.
GH.Prover.prototype.multiplyByOneLeft = function(sexp) {
	if (((sexp.operator_ == '+') || (sexp.operator_ == '*')) && (sexp.left().operator_ == '1')) {
		return sexp;
	}
	this.print([sexp], 'mulid');
	this.print([], 'eqcomi');
	this.commute(this.getLast().right());
	return this.getReplaced(sexp);
};

// Adds two multi-digit numbers. This represents adding the 10's or 100's digit.
// Both numbers must have the same number of digits and only the highest digit can
// be non-zero. The numbers should be in long-form.
GH.Prover.prototype.addHigherDigits = function(sexp) {
	var result = sexp.copy(null);                                          // Example:
	                                                                       // 5 * 10 + 6 * 10
	result = this.replaceWith(this.undistributeLeft, result);   // (5 + 6) * 10
	result = this.replaceLeft(GH.Prover.addSingleDigits, result);     // (10 + 1) * 10
	
	// If the result is a two digit number. Distribute the carry.
	if (result.left().operator_ == '+') {              
		result = this.replaceWith(this.distributeLeft, result); // 10 * 10 +  1 * 10
	}

	//return result;
	return this.getReplaced(sexp);
};


// Distribute the right operand to the left like this: (a + b) * c = a * c + b * c.
GH.Prover.distributeLeft = {};

GH.Prover.distributeLeft.expectedForm = GH.sExpression.fromString('(* (+ A B) C)');

GH.Prover.distributeLeft.description = 'Distributive Prop.';

GH.Prover.distributeLeft.name = function(prover, sexp) {
	return 'distl';
};

// Returns the mandatory hypotheses using the expected form.
GH.Prover.distributeLeft.hyps = function(prover, sexp) {
	return prover.getHyps(sexp, this.expectedForm);
};
// We assume that 'distl' is in the repository, so there is no body or header for GH.Prover.distributeLeft.

// This reverses the distribution left operation:  a * c + b * c = (a + b) * c
GH.Prover.undistributeLeft = {};

GH.Prover.undistributeLeft.expectedForm = GH.sExpression.fromString('(+ (* A C) (* B C))');

GH.Prover.undistributeLeft.name = function(prover, sexp) {
	return 'undistl';
};

GH.Prover.undistributeLeft.description = 'Distributive Prop.';

GH.Prover.undistributeLeft.header = function(prover, sexp) {
	return '() ()';
};

GH.Prover.undistributeLeft.hyps = function(prover, sexp) {
	return prover.getHyps(sexp, this.expectedForm);
};

GH.Prover.undistributeLeft.body = function(prover, sexp) {
	var hyps = prover.getHyps(sexp, this.expectedForm);
	prover.print(hyps, 'distl');
	prover.print([], 'eqcomi');
	return prover.getReplaced(sexp);
};

GH.Prover.undistributeLeft.makeTheorem = function(prover) {
	prover.addTheorem(this, this.expectedForm);
};

// Computes the sum of two numbers. Both numbers are converted into a long form that is easier to compute
// with. The result is converted back into the short form.
GH.Prover.prototype.addTwoNumbers = function(sexp) {
	var result = sexp;
	result = this.applyLeft(this.numberLongForm, result);
	result = this.applyRight(this.numberLongForm, result);
	result = this.addTwoLongFormNumbers(result);
	return this.numberShortForm(result);
};

// Converts an s-expression representing a number in a long form. Digits with a 1 or 0 are expanded out.
// For example, 120 is normally represented as:   120 =     10 * 10 + 2 * 10. 
// In long-form it is represented as:             120 = 1 * 10 * 10 + 2 * 10 + 0.
GH.Prover.prototype.numberLongForm = function(sexp) {
	var num = this.sexpToNum(sexp);
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
				result = this.applyLeft(this.multiplyByOneLeft, result);
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
				this.print([result], 'pa_ax3')
				this.print([], 'eqcomi');
				result = this.getReplaced(result);
				if (i > 0) {
					this.print([this.numToSexp(Math.pow(10, i))], 'pa_ax5r')
					this.print([], 'eqcomi');
					result = this.getReplaced(result.right());
				} else {
					result = result.right();
					depth++;
				}
			} else {
				this.print([result], 'pa_ax3r')
				this.print([], 'eqcomi');
				result = this.getReplaced(result);
				if (i > 0) {
					this.print([this.numToSexp(Math.pow(10, i))], 'pa_ax5r')
					this.print([], 'eqcomi');
					result = this.getReplaced(result.left());
					result = result.parent_;
				}
				result = result.right();
				depth++;
			}
		}
	}
	if (changed) {
		return this.getReplaced(sexp);
	} else {
		return sexp;
	}
};

// Simplify multiplication in the following two ways:
//     1 * x = x
//     0 * x = 0
GH.Prover.prototype.simplifyTimes = function(sexp) {
	var result = sexp;
	if(result.operator_ == '*') {
		if (result.left().operator_ == '0') {
			this.print([result.right()], 'pa_ax5r')
			result = this.getReplaced(result);
		} else if (result.left().operator_ == '1') {
			this.print([result.right()], 'mulid');
			var mulid = this.getLast();
			this.applyLeft(this.commute, mulid);
			result = this.getReplaced(result);
		}
	}
	return result;
};

// Convert a number in long form back into the standard short form.
// Simplify multiplication and addition.
GH.Prover.prototype.numberShortForm = function(sexp) {
	if (sexp.operator_ == '+') {
		var result = sexp;
		result = this.applyLeft(this.numberShortForm, sexp);
		result = this.applyRight(this.numberShortForm, result);
		return this.additiveIdentity(result);
	} else {
		return this.simplifyTimes(sexp);
	}
};

// Returns the number of digits of a number. The number can be in long form or short form.
GH.Prover.prototype.getDigitNum = function(sexp) {
	if (sexp.operator_ == '+') {
		return this.getDigitNum(sexp.left());
	} else if (sexp.operator_ == '*') {
		return GH.numOfDigits(this.sexpToNum(sexp.right()));
	} else {
		return 1;
	}
};

// Computes the sum of two numbers in long form.
GH.Prover.prototype.addTwoLongFormNumbers = function(sexp) {
	var leftNum  = this.sexpToNum(sexp.left());
	var rightNum = this.sexpToNum(sexp.right());
	var leftDigits = this.getDigitNum(sexp.left());
	var rightDigits = this.getDigitNum(sexp.right());
	var maxDigits = Math.max(leftDigits, rightDigits);
		
	var digit = Math.pow(10, maxDigits - 1);
	var upperDigit = digit * 10;
	var lowerCarry = (((leftNum %      digit) + (rightNum %      digit)) / digit >= 1);
	var upperCarry = (((leftNum % upperDigit) + (rightNum % upperDigit)) / upperDigit >= 1);
	var lowerZero  = (((leftNum + rightNum) % upperDigit) / digit < 1);
				
	var result = sexp;
	if (leftDigits == 1 && rightDigits == 1) {
		result = this.replaceWith(GH.Prover.addSingleDigits, result);
	} else if (leftDigits != rightDigits) {
		if (leftDigits > rightDigits) {
			result = this.associateRight(result);
		} else {
			result = this.reposition(result, 'A (B C)', 'B (A C)');
		}
		result = this.applyRight(this.addTwoLongFormNumbers, result);
			
		// Handle a carry.
		if (lowerCarry) {
			result = this.associateLeft(result);
			//result = this.reposition(result, 'A (B C)', '(A B) C'); // Same as associateLeft
			result = this.applyLeft(this.addHigherDigits, result);
		}		
	} else if (leftDigits == rightDigits) {
		result = this.reposition(result, '(A B) (C D)', '(A C) (B D)'); // This is the same as add4.
		result = this.applyRight(this.addTwoLongFormNumbers, result);
	
		// Handle a carry.
		if (lowerCarry) {
			result = this.reposition(result, '(A B) (carry D)', '(A (B carry)) D');
			result = result.left().right();
			result = this.addHigherDigits(result);
			result = result.parent_.parent_;
		}
		result = this.applyLeft(this.addHigherDigits, result);
		if (upperCarry && !lowerZero) {
			result = this.associateRight(result);
		}
	}
	result = this.numberLongForm(result);
	return result;
};

// Takes an s-expression and a symbol tree and continues to run the associateRight function
// wherever it is possible for both the symbol tree and the s-expression.
GH.Prover.prototype.associateAllRight = function(expTree) {
	var sexp = expTree.sexp;
	var tree = expTree.tree;
	if (tree.left && tree.left.left) {
		var result = this.associateRight(sexp);
		tree.associateRight();
		return this.associateAllRight({sexp: result, tree: tree});
	} else if (tree.right) {
		var result = this.associateAllRight({sexp: sexp.right(), tree: tree.right});
		return {sexp: result.sexp.parent_, tree: tree};
	} else {
		return expTree;
	}
};

// Takes an s-expression and a symbol tree and continues to run the associateLeft function
// wherever it is possible for both the symbol tree and the s-expression.
GH.Prover.prototype.associateAllLeft = function(expTree) {
	var sexp = expTree.sexp;
	var tree = expTree.tree;
	if (tree.right && tree.right.right) {
		var result = this.associateLeft(sexp);
		tree.associateLeft();
		return this.associateAllLeft({sexp: result, tree: tree});
	} else if (tree.left) {
		var result = this.associateAllLeft({sexp: sexp.left(), tree: tree.left});
		return {sexp: result.sexp.parent_, tree: tree};
	} else {
		return expTree;
	}
};

// Repositions the terms in an s-expression. Uses commutation and association rules to 
// change the s-expression between any two positions. Assumes that s-expression has operators
// that commute and associate. oldPosition and newPosition are strings that are converted into
// symbol trees. 
GH.Prover.prototype.reposition = function(sexp, oldPosition, newPosition) {
	var oldTree = GH.symbolTree.fromString(oldPosition);
	var newTree = GH.symbolTree.fromString(newPosition);
	return this.repositionTree(sexp, oldTree, newTree);
};

// Repositions the terms in an s-expression. Uses commutation and association rules to 
// change the s-expression between two symbol trees. Assumes that s-expression has operators
// that commute and associate.

// First, associate all left, then reorder all the terms, and then use association rules to
// get into the new tree position.
GH.Prover.prototype.repositionTree = function(sexp, oldTree, newTree) {
	// TODO: Optimize by not modifying left or right if they were not changed.
	var leftAssociated = this.associateAllLeft({sexp: sexp, tree: oldTree});
//	var result = leftAssociated.
	var symbolOrder = GH.symbolTree.getSymbolOrder(oldTree.getSymbolList(), newTree.getSymbolList());
	var reordered = this.reorder(leftAssociated.sexp, symbolOrder);
	
	// leftAssociated.tree was set before the reordering, so it is not a perfect representation
	// of the state of the left, but for the reassociation step the order is irrelevant.
	return this.reassociate(reordered, leftAssociated.tree, newTree);
};
	
// Uses a bubble sort.
GH.Prover.prototype.reorder = function(sexp, order) {
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
					
				result = this.bubble(result, i, order.length);
			}
		}
	}
	return result;
};

// Swaps the order of two expressions, given the position of the
// expression to swap. The most basic operation in a bubble sort. 
GH.Prover.prototype.bubble = function(sexp, position, listLength) {
	var leftness = listLength - position - 2;
	for (var i = 0; i < leftness; i++) {
		sexp = sexp.left();
	}
	if (position == 0) {
		sexp = this.commute(sexp);
	} else {
		sexp = this.associateRight(sexp);
		sexp = this.applyRight(this.commute, sexp);
		sexp = this.associateLeft(sexp);
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
GH.Prover.prototype.reassociate = function(sexp, oldTree, newTree) {
	if (!oldTree.left) {
		return sexp;
	}
	
	var oldLeftness = oldTree.left.getSymbolList().length;
	var newLeftness = newTree.left.getSymbolList().length;
	while (oldLeftness < newLeftness) {
		sexp = this.associateLeft(sexp);
		oldTree.associateLeft();
		oldLeftness = oldTree.left.getSymbolList().length;
	}
	while (oldLeftness > newLeftness) {
		sexp = this.associateRight(sexp);
		oldTree.associateRight();
		oldLeftness = oldTree.left.getSymbolList().length;
	}
	if (oldLeftness != newLeftness) {
		alert('Reassociation failed.');
	}
	var result = sexp;
	result = this.reassociate(result.left(),  oldTree.left,  newTree.left);
	result = result.parent_;
	result = this.reassociate(result.right(), oldTree.right, newTree.right);
	result = result.parent_;
	
	return result;
};

GH.Prover.prototype.oneDigitNotZero = function(sexp) {
	var predecessor = parseInt(sexp.operator_) - 1;	
	this.print(['(' + predecessor + ')'], 'pa_ax1');
	var result = this.getLast().child().right();

	this.print(['(' + predecessor + ')'], 'a1suc');
	result = this.getReplaced(result, this.getLast())
	this.successorLeft(result);
};

GH.Prover.prototype.oneDigitInequality = function(leftNum, rightNum) {
	if (leftNum >= rightNum) {
		// Not written yet.
		return;
	}
	var diff = rightNum - leftNum;
	this.println('x (' + diff + ') tyex');
	this.println('x (' + diff + ') (' + leftNum + ') addeq2');
	
	var result = this.getLast().right().right();
	result = this.replaceWith(this.addSingleDigits, result);
	
	this.println('x 19.22i');
	this.println('ax-mp');

    this.println('(' + leftNum + ') (' + rightNum + ') x df-le');
    this.println('mpbir');  // Could also use replace.

    // TODO: Put this is a not equal function
		// TODO: Don't use a fake s-expression.
		var fakeSexp = {operator_: diff};
		this.oneDigitNotZero(fakeSexp);
		this.println('(0) (' + leftNum + ') (' + diff + ') addcan')
		this.println('mtbir');
	
		result = this.getLast().child();
		result = this.replaceRight(this.addSingleDigits, result);
		result = this.additiveIdentity(result.left());
		
	this.println('pm3.2i');
	this.println('(' + leftNum + ') (' + rightNum + ') df-lt');
	this.println('bicomi');
	this.println('mpbi');
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