GH.ProofGenerator.replacer = function(prover) {
	this.prover = prover;
};

GH.ProofGenerator.replacer.VARIABLE_NAMES = {
	wff: ['ph', 'ps', 'ch', 'th', 'ta', 'et', 'zi', 'si', 'ph\'', 'ps\'', 'ch\'', 'th\'', 'ta\''],
	nat: ['A', 'B', 'C', 'D', 'A\'', 'B\'', 'C\'', 'D\'', 'A0', 'A1', 'A2', 'A3'], 
	bind: ['x', 'y', 'z', 'v', 'w\'', 'x\'', 'y\'', 'z\'', 'v\'', 'w\'']
};

// A set of theorems for replacing some part of an expression. One for each operator.
// Each operator has two groups of theorems. The first group is for when the expression
// has a parent. The second group is for when the expression does not. Within each group
// there is one theorem for each operand.
GH.ProofGenerator.replacer.REPLACE_OPERATIONS = [
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
	['S',	['pa_ax2i'], [null]],
	['+',	['addeq1i','addeq2i'], [null, null]],
	['*',   ['muleq1i','muleq2i'], [null, null]]
];

GH.ProofGenerator.replacer.prototype.stepName = function(sexp) {
	// TODO: Reenable this without breaking anything.
	/*if ((GH.operatorUtil.getRootType(sexp) != 'wff') && (!sexp.parent)) {
		// An orphan non-wff must be an expression that is being evaluated directly from the stack
		// and not in a theorem. However, the second to last theorem if it exists will normally have the
		// expression we want to replace. Except sometimes it doesn't.
		var theorems = this.prover.getTheorems();
		if (theorems.length >= 2) {
			sexp = theorems[theorems.length - 2].right();
		}
	}*/
	
	var position = GH.Prover.findPosition(sexp);
	var temp = sexp;
	while (temp.parent != null) {
		temp = temp.parent;
	}
	if (position.length == 1) {
		// Do not generate a new replacement theorem for basic one-line replacements.
		var replaceOperations = GH.ProofGenerator.replacer.REPLACE_OPERATIONS;
		for (var i = 0; i < replaceOperations.length; i++) {
			if (sexp.parent.operator == replaceOperations[i][0]) {
				stepName = replaceOperations[i][2][sexp.siblingIndex];
				if (stepName) {
					return stepName;
				}
			}
		}
	}

	var result = position.length ? 'replace' : '';
	for (var i = 0; i < position.length; i++) {
		var name = GH.operatorUtil.getName(temp.operator);
		result += name + position[i];
		temp = temp.operands[position[i]];
	}
	return result;
};

GH.ProofGenerator.replacer.prototype.hyps = function(sexp) {
	return [];
};

GH.ProofGenerator.replacer.prototype.canAddTheorem = function(sexp) {
	var position = GH.Prover.findPosition(sexp);
	if ((GH.operatorUtil.getRootType(sexp) != 'wff') || (position.length == 0)) {
		// addThorem is not currently working with non-wffs, but there's no reason it
		// couldn't work. Use inline for now.
		return false;
	} else {
		return true;
	}
};

GH.ProofGenerator.replacer.prototype.addTheorem = function(sexp, replacement) {
	var position = GH.Prover.findPosition(sexp);
	var name = this.stepName(sexp);
	var replaceThm = this.createGeneric(position.slice(0), sexp, replacement, name);
	// this.prover.insertBeginning(replaceThm);
	for (var i = 0; i < replaceThm.length; i++) {
		this.prover.println(replaceThm[i]);
	} 
};

GH.ProofGenerator.replacer.prototype.createGeneric = function(position, replacee, replacement, name) {
	var output = [];
	while (replacee.parent != null) {
		replacee = replacee.parent;
	}
	var start = [];
	var end = [];
	var middle = [];
	var usedVariables = { wff: 0, nat: 0, bind: 0};
	this.genericCopies(start, end, middle, position.slice(0), replacee, replacement, usedVariables);

	var startString  = GH.sexp_to_string(start);
	var middleString = GH.sexp_to_string(middle);
	var endString    = GH.sexp_to_string(end);

	GH.ProofGenerator.replacer.removeStyling(start);
	GH.ProofGenerator.replacer.removeStyling(middle);
	GH.ProofGenerator.replacer.removeStyling(end);
	var startExp  = GH.sExpression.fromRaw(start);
	var middleExp = GH.sExpression.fromRaw(middle);
	var endExp    = GH.sExpression.fromRaw(end);
	
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
		startExp = startExp.operands[position[i]];
	}
	this.replace(startExp, output);
	this.prover.depth--;
	output.push(')');
	return output;
};

GH.ProofGenerator.replacer.prototype.spaceColumns = function(strings) {
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

GH.ProofGenerator.replacer.removeStyling = function(sexp) {
    if (typeof sexp == 'string') {
		sexp = sexp.replace(/ |\[|\]/g, '')
	}
	for (var i = 1; i < sexp.length; i++) {
		if (typeof sexp[i] == 'string') {
			sexp[i] = sexp[i].replace(/ |\[|\]/g, '')
		} else {
			GH.ProofGenerator.replacer.removeStyling(sexp[i]);
		}
	}
};

GH.ProofGenerator.replacer.prototype.genericCopies = function(start, end, middle, positions, replacee, replacement, usedVariables) {
	var operand = positions.splice(0, 1);
	var operator = replacee.operator;
	start.push(operator);
	end.push(operator);
	var types = GH.operatorUtil.getOperatorTypes(operator);
	for (var i = 0; i < types.length - 1; i++) {
		if (i != operand) {
			var variable = this.grabNextVariable(usedVariables, types[i]);
			start.push(variable);
			end.push(variable);
		} else {
			if (positions.length > 0) {
				start.push([]);
				end.push([]);
				this.genericCopies(start[i + 1], end[i + 1], middle, positions, replacee.operands[i], replacement, usedVariables);
			} else {
				var operator = replacement.operator;
				var replacerTypes = GH.operatorUtil.getOperatorTypes(operator);
				var leftVariable  = this.grabNextVariable(usedVariables, replacerTypes[0]);
				var rightVariable = this.grabNextVariable(usedVariables, replacerTypes[1]);
				
				middle.push(operator);
				middle.push(' [ ' + leftVariable + ' ] ')
				middle.push(' [ ' + rightVariable + ' ] ')
				start.push(' [ ' + leftVariable + ' ] ] ] ');
				end.push(' [ [ [ ' + rightVariable + ' ] ');
			}
		}
	}
};

GH.ProofGenerator.replacer.prototype.grabNextVariable = function(usedVariables, type) {
	if (GH.ProofGenerator.replacer.VARIABLE_NAMES[type].length <= usedVariables[type]) {
		alert('No more unused variable names.');
	}
	var result = GH.ProofGenerator.replacer.VARIABLE_NAMES[type][usedVariables[type]];
	usedVariables[type]++;
	return result;
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
 *
 * Returns true if the replacement was successful.
 */
GH.ProofGenerator.replacer.prototype.replace = function(replacee, output) {
	var parent = replacee.parent;
	var operandIndex = replacee.siblingIndex;
	if (!parent) {
		return true;
	}
		
	var operator = parent.operator;
	var types = GH.operatorUtil.getOperatorTypes(operator);
	if (types == null) {
		return false;
	}

	var replaceOperations = GH.ProofGenerator.replacer.REPLACE_OPERATIONS;
	for (var i = 0; i < replaceOperations.length; i++) {
		if (operator == replaceOperations[i][0]) {
			var mandHyps = [];
			var stepName = null;
			var operatorTypes = GH.operatorUtil.getOperatorTypes(operator);
			if ((parent.parent) || (GH.operatorUtil.getType(parent) != 'wff')) {
				// Add all the operands that are not getting replaced.
				for (var j = 0; j < types.length - 1; j++) {
					if (j != operandIndex) {
						mandHyps.push(parent.operands[j]);
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
	if (parent.parent) {
		return this.replace(parent, output);
	} else {
		return true;
	}
};

// Replace the s-expression replacee using the last statement on the proof stack.
GH.ProofGenerator.replacer.prototype.inline = function(replacee) {
	var printOutput = [];
	this.replace(replacee, printOutput);
	for (var i = 0; i < printOutput.length; i++) {
		this.prover.println(printOutput[i]);
	}
	result = this.prover.getLast();
	result = GH.Prover.findMatchingPosition(result, replacee);
	// replacee.joinEq(result.copy());
	return true;
};

GH.ProofGenerator.replacer.prototype.isApplicable = function(replacee, replacement) {
	// Replacing does nothing if the left and right sides are equal.
	if ((replacement.operands.length != 2) || (replacement.left().equals(replacement.right()))) {
		return false;
	}
	// Check that the operator is an equivalence operator.
	if (!GH.operatorUtil.isEquivalenceOperator(replacement.operator)) {
		return false;
	}
	var myMatch = GH.Prover.findMatch(replacee, replacement.left());
	if (!myMatch) {
		return false;
	}
	var unusedOutput = [];
	return this.replace(myMatch, unusedOutput);
};