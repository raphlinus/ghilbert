GH.replacer = function(prover) {
	this.prover = prover;
};

GH.replacer.prototype.addReplaceThm = function(sexp) {
	var position = GH.Prover.findPosition(sexp);
	var name = '';
	// What happens when position.length is 1?
	if (position.length > 0) {
		var replacement = this.prover.getLast();
		name = GH.replacer.replaceThmName(sexp, position);
		if (!this.prover.symbolDefined(name)) {
			var replaceThm = this.createGeneric(position.slice(0), sexp, replacement, name);
			this.prover.insertBeginning(replaceThm);
		}
		this.prover.depth++;
	}
	this.prover.println(name);
	if (position.length > 0) {
		this.prover.depth--;
	}

	// TODO: Check that this is working right.
	var replaced = this.prover.getLast();
	if (sexp.parent_) {
		return GH.Prover.findMatchingPosition(replaced, sexp);
	} else {
		if (GH.Prover.getType(sexp) == 'wff') {
			return replaced;
		} else {
			return replaced.right();
		}
	}
	// TODO: Don't generate a new replacement theorem for basic one-line replacements.
};



GH.replacer.prototype.createGeneric = function(position, replacee, replacement, name) {
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

	GH.replacer.removeStyling(start);
	GH.replacer.removeStyling(middle);
	GH.replacer.removeStyling(end);
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

	this.prover.depth++;
	for (var i = 0; i < position.length; i++) {
		startExp = startExp.operands_[position[i]];
	}
	this.replace(startExp, output);
	this.prover.depth--;
	output.push(')');
	output.push('');
	return output;
};

GH.replacer.replaceThmName = function(sexp, position) {
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

GH.replacer.prototype.spaceColumns = function(strings) {
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

GH.replacer.removeStyling = function(sexp) {
    if (typeof sexp == 'string') {
		sexp = sexp.replace(/ |\[|\]/g, '')
	}
	for (var i = 1; i < sexp.length; i++) {
		if (typeof sexp[i] == 'string') {
			sexp[i] = sexp[i].replace(/ |\[|\]/g, '')
		} else {
			GH.replacer.removeStyling(sexp[i]);
		}
	}
};

GH.replacer.prototype.genericCopies = function(start, end, middle, positions, replacee, replacement, usedVariables) {
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

GH.replacer.prototype.grabNextVariable = function(usedVariables, type) {
	if (GH.replacer.VARIABLE_NAMES[type].length <= usedVariables[type]) {
		alert('No more unused variable names.');
	}
	var result = GH.replacer.VARIABLE_NAMES[type][usedVariables[type]];
	usedVariables[type]++;
	return result;
};

GH.replacer.VARIABLE_NAMES = {
	wff: ['ph', 'ps', 'ch', 'th', 'ta'],
	nat: ['A', 'B', 'C', 'D', 'A\'', 'B\'', 'C\'', 'D\''], 
	bind: ['x', 'y', 'z', 'v', 'w\'', 'x\'', 'y\'', 'z\'', 'v\'', 'w\'']
};

// A set of theorems for replacing some part of an expression. One for each operator.
// Each operator has two groups of theorems. The first group is for when the expression
// has a parent. The second group is for when the expression does not. Within each group
// there is one theorem for each operand.
GH.replacer.REPLACE_OPERATIONS = [
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
GH.replacer.prototype.replace = function(replacee, output) {
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

	var replaceOperations = GH.replacer.REPLACE_OPERATIONS;
	for (var i = 0; i < replaceOperations.length; i++) {
		if (operator == replaceOperations[i][0]) {
			var mandHyps = [];
			var stepName = null;
			var operatorTypes = GH.Prover.getOperatorTypes(operator);
			if ((parent.parent_) || (GH.Prover.getType(parent) != 'wff')) {
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
			if ((!stepName) || (!this.prover.symbolDefined(stepName))) {
				return false;
			}
			this.prover.makeString(mandHyps, stepName, output)
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
GH.replacer.prototype.getReplaced = function(replacee) {
	var printOutput = [];
	this.createReplaceThm(replacee, printOutput);
	for (var i = 0; i < printOutput.length; i++) {
		this.prover.println(printOutput[i]);
	}
	result = this.prover.getLast();
	result = GH.Prover.findMatchingPosition(result, replacee);
	return result;
};

// Replace the s-expression replacee using the last statement on the proof stack.
GH.replacer.prototype.createReplaceThm = function(replacee, output) {
	// TODO: Return output.

	var replacement = this.prover.getLast();
	if (replacee.parent_) {
		this.replace(replacee, output);
		//var replaced = this.replace(replacee, output);
		//return GH.Prover.findMatchingPosition(replaced, replacee);
	}/* else {
		return replacement.right();
	}*/
};

GH.replacer.prototype.isReplaceable = function(replacee, replacement) {
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