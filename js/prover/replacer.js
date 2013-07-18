GH.ProofGenerator.replacer = function(prover) {
	this.prover = prover;
};

GH.ProofGenerator.replacer.VARIABLE_NAMES = {
	wff: ['ph', 'ps', 'ch', 'th', 'ta', 'et', 'zi', 'si', 'ph\'', 'ps\'', 'ch\'', 'th\'', 'ta\''],
	nat: ['A', 'B', 'C', 'D', 'A\'', 'B\'', 'C\'', 'D\'', 'A0', 'A1', 'A2', 'A3'], 
	bind: ['x', 'y', 'z', 'v', 'w\'', 'x\'', 'y\'', 'z\'', 'v\'', 'w\''],
	set: ['S', 'T', 'U', 'V', 'S0', 'S1', 'S2', 'S3', 'S4', 'S5', 'S6', 'S7', 'S8', 'S9']
};

// A set of theorems for replacing some part of an expression.
// The first operator is the equivalence operator that is needed in the second hypothesis statement.
// Then there are a list of operators that this equivalence can be applied to. These operators are
// in the first hypothesis statement. For each of those, there is the name of the operator, the step
// name when it is applied to each operand, then the resulting equivalence operator, then there is
// an optional operator if the operator in the first hypothesis statement changed.
GH.ProofGenerator.replacer.REPLACE_OPERATIONS = [
['<->',
   [[ '-.', ['con4biir'], '<->'],
	[ '->', ['imbi1i', 'imbi2i'], '<->'],
	['<->', ['bibi1i', 'bibi2i'], '<->'],
	['\\/', ['orbi1i', 'orbi2i'], '<->'],
	['/\\',	['anbi1i', 'anbi2i'], '<->'],
	['A.',  [null,     'albii' ], '<->'],
	['E.',  [null,     'exbii' ], '<->'],
	['{|}', [null,     'abeq2i'], '=_']]],
['->',
   [[ '->', [null,     'imim2i'], '->'],
	['\\/', ['orim1i', 'orim2i'], '->'],
	['/\\',	['anim1i', 'anim2i'], '->'],
	['E.',  [null,     '19.22i'], '->']]],
['=',
   [['=',   ['eqeq1i', 'eqeq2i'], '<->'],
	['<=',  ['leeq1i', 'leeq2i'], '<->'],
	['<',   ['lteq1i', 'lteq2i'], '<->'],
	['|',   ['divideseq1i', 'divideseq2i'], '<->'],
	['prime', ['primeeqi'], '<->'],
	['S',	['pa_ax2i'], '='],
	['+',	['addeq1i','addeq2i'], '='],
	['*',   ['muleq1i','muleq2i'], '='],
	['e.',  ['eleq1i', null], '<->']]],
['<',
   [['<',   [null, 'ltTrlt'], '->', '<'],
	['<=',  [null, 'ltTrle'], '->', '<'],
	['=',	[null, 'ltTreq'], '->', '<']]],
['<=',
   [['<',   [null, 'leTrlt'], '->', '<'],
	['<=',  [null, 'leTrle'], '->', '<='],
	['=',	[null, 'leTreq'], '->', '<=']]],
['=_',
   [['=_',  ['seqseq1i', 'seqseq2i'], '<->'],
	['e.',  [null, 'eleq2i'], '<->'],
	['u.',  ['uneq1i', 'uneq2i'], '=_'],
	['i^i', ['ineq1i', 'ineq2i'], '=_']]],
];

GH.ProofGenerator.replacer.SHORTHAND_OPERATIONS = {
    BiReplaceNot0: 'mtbi',
	BiReplaceImp0: 'sylbi2',
	BiReplaceImp1: 'sylib',
	BiReplaceBi0: 'bitr3icom',
	BiReplaceBi1: 'bitri',
	BiReplaceOr0: 'orbi1ii',
	BiReplaceOr1: 'orbi2ii',
	BiReplaceAn0: 'anbi1ii',
	BiReplaceAn1: 'anbi2ii',
	BiReplaceAl1: 'albiii',
	BiReplaceEx1: 'exbiii',
    ImpReplaceImp1: 'syl'
};

GH.ProofGenerator.replacer.prototype.stepName = function(sexp, replacement) {
	var position = GH.Prover.findPosition(sexp);
	var temp = sexp;
	while (temp.parent != null) {
		temp = temp.parent;
	}

	var replacementOperator = replacement ? replacement.operator : this.prover.getLast().operator;
	var prefix = GH.operatorUtil.getName(replacementOperator);
	var result = position.length ? prefix + 'Replace' : '';
	for (var i = 0; i < position.length; i++) {
		var name = GH.operatorUtil.getName(temp.operator);
		result += name + position[i];
		temp = temp.operands[position[i]];
	}
	var shorthand = GH.ProofGenerator.replacer.SHORTHAND_OPERATIONS[result];
	if (shorthand) {
		return shorthand;
	} else {
		return result;
	}
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
	var name = this.stepName(sexp, replacement);
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
	var usedVariables = { wff: 0, nat: 0, bind: 0, set: 0};
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
	this.replace(startExp, middleExp.operator, output);
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
	if (positions.length == 0) {
		var replaceOperation = GH.ProofGenerator.replacer.getReplaceOperation(replacee.operator, replacement.operator);
		if (replaceOperation.length > 3) {
			end.push(replaceOperation[3]);
		} else {
			end.push(operator);
		}
	} else {
		end.push(operator);
	}
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

GH.ProofGenerator.replacer.getReplaceOperation = function(replaceeOperator, replacementOperator) {
	var replacementOperations = GH.ProofGenerator.replacer.REPLACE_OPERATIONS;
	var resultOperator = null;
	for (var j = 0; j < replacementOperations.length; j++) {	
		if (replacementOperator == replacementOperations[j][0]) {
			var replaceOperations = replacementOperations[j][1];
			for (var i = 0; i < replaceOperations.length; i++) {
				if (replaceeOperator == replaceOperations[i][0]) {
					return replaceOperations[i];
				}
			}
		}
	}
	return null;
};

GH.ProofGenerator.replacer.prototype.addStep = function(mandHyps, stepName, output) {
	if ((!stepName) || (!this.prover.symbolDefined(stepName))) {
		return false;
	}
	this.prover.makeString(mandHyps, stepName, output);
	return true;
}

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
GH.ProofGenerator.replacer.prototype.replace = function(replacee, replacementOperator, output) {
	var parent = replacee.parent;
	var operandIndex = replacee.siblingIndex;
	if (!parent) {
		if (GH.operatorUtil.getType(replacee) == 'wff') {
			stepName = 'null';
			if (replacementOperator == '->') {
				stepName = 'ax-mp';
			} else if (replacementOperator == '<->') {
				stepName = 'mpbi';
			}
			return this.addStep([], stepName, output);
		} else {
			return true;
		}
	}
		
	var replaceeOperator = parent.operator;
	var types = GH.operatorUtil.getOperatorTypes(replaceeOperator);
	if (types == null) {
		return false;
	}

	var resultOperator = null;
	var replaceOperation = GH.ProofGenerator.replacer.getReplaceOperation(replaceeOperator, replacementOperator);
	if (replaceOperation != null) {
		var mandHyps = [];
		var stepName = null;
		var operatorTypes = GH.operatorUtil.getOperatorTypes(replaceeOperator);
		// Add all the operands that are not getting replaced.
		for (var j = 0; j < types.length - 1; j++) {
			if (j != operandIndex) {
				mandHyps.push(parent.operands[j]);
			}
		}
		stepName = replaceOperation[1][operandIndex];
		var success = this.addStep(mandHyps, stepName, output);
		resultOperator = replaceOperation[2];
		if (!success) {
			return false;
		}
	} else {
		return false;
	}

	// Recursively replace the entire replacee follow the expression up to the root.
	return this.replace(parent, resultOperator, output);
};

// Replace the s-expression replacee using the last statement on the proof stack.
GH.ProofGenerator.replacer.prototype.inline = function(replacee) {
	var printOutput = [];
	var replacement = this.prover.getLast();
	this.replace(replacee, replacement.operator, printOutput);
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
	var myMatch = GH.Prover.findMatch(replacee, replacement.left());
	if (!myMatch) {
		return false;
	}
	var unusedOutput = [];
	return this.replace(myMatch, replacement.operator, unusedOutput);
};