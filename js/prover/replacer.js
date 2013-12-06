GH.ProofGenerator.replacer = function(prover) {
	this.prover = prover;
	this.equalizer = new GH.ProofGenerator.equalizer(prover);
};

// A set of theorems for replacing some part of an expression.
// The first operator is the equivalence operator that is needed in the second hypothesis statement.
// Then there are a list of operators that this equivalence can be applied to. These operators are
// in the first hypothesis statement. For each of those, there is the name of the operator, the step
// name when it is applied to each operand, then the resulting equivalence operator, then there is
// an optional operator if the operator in the first hypothesis statement changed.
GH.ProofGenerator.replacer.REPLACE_OPERATIONS = [
['<->',
   [[null,  ['mpbi'], null],
    [ '-.', ['con4biir'], '<->'],
	[ '->', ['imbi1i', 'imbi2i'], '<->'],
	['<->', ['bibi1i', 'bibi2i'], '<->'],
	['\\/', ['orbi1i', 'orbi2i'], '<->'],
	['/\\',	['anbi1i', 'anbi2i'], '<->'],
	['A.',  [null,     'albii' ], '<->'],
	['E.',  [null,     'exbii' ], '<->'],
	['[/]', [null,     'sbcbii'], '<->'],
	['rwff',[null,     'rwffbii'], '<->'],   
	]],
['->',
   [[null,  ['ax-mp'], null],
    ['<->', ['biim1i', 'biim2i'], '->'],  // This doesn't work quite right see ImpReplaceBi1.
	[ '->', [null,     'imim2i'], '->'],
	['\\/', ['orim1i', 'orim2i'], '->'],
	['/\\',	['anim1i', 'anim2i'], '->'],
	['A.',  [null,     '19.20i'], '->'],
	['E.',  [null,     '19.22i'], '->']   ]],
['=',
   [['=',   ['eqeq1i', 'eqeq2i', 'eqeq1', 'eqeq2'], '<->'],
	['<=',  ['leeq1i', 'leeq2i', 'leeq1', 'leeq2'], '<->'],
	['<',   ['lteq1i', 'lteq2i', 'lteq1', 'lteq2'], '<->'],
	['>=',  ['geeq1i', 'geeq2i', 'geeq1', 'geeq2'], '<->'],
	['>',   ['gteq1i', 'gteq2i', 'gteq1', 'gteq2'], '<->'],
	['|',   ['divideseq1i', 'divideseq2i', 'divideseq1', 'divideseq2'], '<->'],
	['prime', ['primeeqi', 'primeeq'], '<->'],
	['S',	['pa_ax2i', 'pa_ax2'], '='],
	['+',	['addeq1i','addeq2i', 'addeq1', 'addeq2'], '='],
	['*',   ['muleq1i','muleq2i', 'muleq1', 'muleq2'], '='],
	['exp', ['expeq1i','expeq2i',     null, null    ], '='],
	['{...}', ['intervaleq1i',  'intervaleq2i'], '=_'],
	['{}',  ['sneqi'], '=_'],
	['e.',  ['eleq1i',  null,   'ax-eleq1', null    ], '<->']   ]],
['<',
   [['<',   [null, 'ltTrlt'], '->', '<'],
	['<=',  [null, 'ltTrle'], '->', '<'],
	['=',	[null, 'ltTreq'], '->', '<']]],
['<=',
   [['<',   [null, 'leTrlt'], '->', '<'],
	['<=',  [null, 'leTrle'], '->', '<='],
	['=',	[null, 'leTreq'], '->', '<=']]],
['>=',
   [['>',   [null, 'geTrge'], '->', '>='],
	['>=',  [null, 'geTrgt'], '->', '>'],
	['=',	[null, 'geTreq'], '->', '>=']]],
['>',
   [['>=',  [null, 'gtTrge'], '->', '>'],
	['>',   [null, 'gtTrgt'], '->', '>'],
	['=',	[null, 'gtTreq'], '->', '>']]],
['=_',
   [['=_',  ['seqseq1i', 'seqseq2i'], '<->'],
    ['C_',  ['sseq1i',   'sseq2i'], '<->'],
	// Missing C.
	['e.',  [null,       'eleq2i'], '<->'],
	['min', ['mineqi' ], '='],
	['u.',  ['uneq1i',   'uneq2i'], '=_'],
	['i^i', ['ineq1i',   'ineq2i'], '=_']]],
['=z',
   [['=_',  ['zeqzeq1i', 'zeqzeq2i'], '<->']]],
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

GH.ProofGenerator.replacer.NEGATED_OPERATIONS = [
	['>',  '<='],
	['>=', '<' ]
];

GH.ProofGenerator.replacer.getOperator = function(sexp) {
	if (!sexp) {
		return null;
	}
	if (sexp.parent && sexp.parent.operator == '-.') {
		var operations = GH.ProofGenerator.replacer.NEGATED_OPERATIONS;
		for (var i = 0; i < operations.length; i++) {
			if (sexp.operator == operations[i][1]) {
				return operations[i][0];
			}
		}
	}
	return sexp.operator;
};

GH.ProofGenerator.replacer.isNegated = function(sexp) {
	if (sexp.operator == '-.') {
		var operations = GH.ProofGenerator.replacer.NEGATED_OPERATIONS;
		for (var i = 0; i < operations.length; i++) {
			if (sexp.child().operator == operations[i][1]) {
				return true;
			}
		}
	}
	return false;
};

// Turn negated operator into positive operators.
GH.ProofGenerator.replacer.makePositive = function(operator) {
	var operations = GH.ProofGenerator.replacer.NEGATED_OPERATIONS;
	for (var i = 0; i < operations.length; i++) {
		if (operator == operations[i][0]) {
			return operations[i][1];
		}
	}
	return operator;
};

GH.ProofGenerator.replacer.prototype.action = function(sexp, replacement) {
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
		return new GH.action(shorthand, []);
	} else {
		return new GH.action(result, []);
	}
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
	var name = this.action(sexp, replacement).name;
	this.createGeneric(position.slice(0), sexp, replacement, name);
	// this.prover.insertBeginning(replaceThm);
};

GH.ProofGenerator.replacer.prototype.createGeneric = function(position, replacee, replacement, name) {
	while (replacee.parent != null) {
		replacee = replacee.parent;
	}
	var start = [];
	var end = [];
	var middle = [];
	var varGenerator = new GH.Prover.variableGenerator();
	this.genericCopies(start, end, middle, position.slice(0), replacee, replacement, varGenerator);

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

	this.prover.println('## <title> Substitution </title>');
	this.prover.println('## <table>');
	this.prover.println('##   '	+ spacedColumns[0]);
	this.prover.println('##   '	+ spacedColumns[1]);
	this.prover.println('##   '	+ spacedColumns[2]);
	this.prover.println('## </table>');
	this.prover.println('thm (' + name + ' () (');
	this.prover.println('     replacee ' + startExp.toString());
	this.prover.println('     substitution ' + middleExp.toString() + ') ');
	this.prover.println('     ' + endExp.toString());
	this.prover.println('  replacee substitution');

	this.prover.depth++;
	startExp.isProven = true;
	for (var i = 0; i < position.length; i++) {
		startExp = startExp.operands[position[i]];
	}
	var midExp = GH.ProofGenerator.replacer.isNegated(middleExp) ? middleExp.child() : middleExp;
	var replacementOp = GH.ProofGenerator.replacer.getOperator(midExp);
	this.replace(startExp, replacementOp);
	this.prover.depth--;
	this.prover.println(')');
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

GH.ProofGenerator.replacer.prototype.genericCopies = function(start, end, middle, positions, replacee, replacement, varGenerator) {
	var operand = positions.splice(0, 1);
	var operator = replacee.operator;
	start.push(operator);
	if (positions.length == 0) {
		var replaceeOp    = GH.ProofGenerator.replacer.getOperator(replacee);
		var replacementQuery = GH.ProofGenerator.replacer.isNegated(replacement) ? replacement.child() : replacement;
		var replacementOp = GH.ProofGenerator.replacer.getOperator(replacementQuery);
		var replaceOperation = this.getReplaceOperation(replaceeOp, replacementOp, operand[0]);
		if (!replaceOperation) {
			alert('No replace operation for ' + replaceeOp + ' and ' + replacementOp);
			return;
		}
		if (replaceOperation.hasOwnProperty('innerOperator')) {
			end.push(GH.ProofGenerator.replacer.makePositive(replaceOperation.innerOperator));
		} else {
			end.push(operator);
		}
	} else {
		// The -> is broken.
		/*if (operator == '<->' && replacement.operator == '->') {
			end.push(replacement.operator);  
		} else {
			end.push(operator);
		}*/
		end.push(operator);
	}
	var types = this.prover.getOperatorTypes(operator);
	for (var i = 0; i < types.length - 1; i++) {
		if (i != operand) {
			var variable = varGenerator.generate(types[i]);
			start.push(variable);
			end.push(variable);
		} else {
			if (positions.length > 0) {
				start.push([]);
				end.push([]);
				this.genericCopies(start[i + 1], end[i + 1], middle, positions, replacee.operands[i], replacement, varGenerator);
			} else {
				var operator = replacement.operator;
				if (GH.ProofGenerator.replacer.isNegated(replacement)) {
					middle.push(operator);
					middle.push([]);
					middle = middle[1];
					operator = replacement.child().operator;
				}
				var replacerTypes = this.prover.getOperatorTypes(operator);
				var leftVariable  = varGenerator.generate(replacerTypes[0]);
				var rightVariable = varGenerator.generate(replacerTypes[1]);
				
				middle.push(operator);
				middle.push(' [ ' + leftVariable + ' ] ')
				middle.push(' [ ' + rightVariable + ' ] ')
				start.push(' [ ' + leftVariable + ' ] ] ] ');
				end.push(' [ [ [ ' + rightVariable + ' ] ');
			}
		}
	}
};

GH.ProofGenerator.replacer.getTableOperation = function(replaceeOperator, replacementOperator) {
	var replacementOperations = GH.ProofGenerator.replacer.REPLACE_OPERATIONS;
	for (var j = 0; j < replacementOperations.length; j++) {	
		if (replacementOperator == replacementOperations[j][0]) {
			var replaceOperations = replacementOperations[j][1];
			for (var i = 0; i < replaceOperations.length; i++) {
				if (replaceeOperator == replaceOperations[i][0]) {
					if (replaceOperations[i].length > 3) {
						window.console.log('Switching operators in replace is currently broken.');
					}
					return replaceOperations[i];
				}
			}
		}
	}
	return null;
};


GH.ProofGenerator.replacer.prototype.getReplaceOperation = function(replaceeOperator, replacementOperator, index) {
	var tableOperation = GH.ProofGenerator.replacer.getTableOperation(replaceeOperator, replacementOperator);
	if (tableOperation) {
		var result = {name: tableOperation[1][index], resultOperator: tableOperation[2]};
		if (tableOperation.length > 3) {
			result['innerOperator'] = tableOperation[3]
		}
		return result;
	}

	// TODO: Replace the table with this.
	if (GH.operatorUtil.EQUIVALENCE_OPERATORS.indexOf(replacementOperator) > -1) {
		var name = this.equalizer.actionName(replaceeOperator, index) + 'i';
		if (!this.prover.symbolDefined(name)) {
			// alert(name + ' is not defined.');
			return null;
		} else {
			var types = this.prover.getOperatorTypes(replaceeOperator);
			var resultOperator = GH.operatorUtil.getEquivalenceOperator(types[types.length - 1]);
			return {name: name, resultOperator: resultOperator};
		}
	}
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
GH.ProofGenerator.replacer.prototype.replace = function(replacee, replacementOperator) {
	var sexp = replacee.parent;		
	var replaceeOperator = GH.ProofGenerator.replacer.getOperator(sexp);
	if ((replaceeOperator == null) && !replacee.isProven) {
		return true;
	}
	var index = sexp ? replacee.siblingIndex : 0;
	var replaceOperation = this.getReplaceOperation(replaceeOperator, replacementOperator, index);
	var actionName = replaceOperation ? replaceOperation.name : null;
	if (actionName && this.prover.symbolDefined(actionName)) {
		// Add all the operands that are not getting replaced.
		var mandHyps = [];
		for (var j = 0; sexp && (j < sexp.operands.length); j++) {
			if (j != replacee.siblingIndex) {
				mandHyps.push(sexp.operands[j]);
			}
		}
		this.prover.print(mandHyps, actionName);

		if (sexp) {
			if (sexp.parent && GH.ProofGenerator.replacer.isNegated(sexp.parent)) {
				sexp = sexp.parent;
			}
			this.prover.replace(sexp);
		} else {
			return true;
		}
	} else {
		return false;
	}
};

// Replace the s-expression replacee using the last statement on the proof stack.
GH.ProofGenerator.replacer.prototype.inline = function(replacee) {
	var replacement = this.prover.getLast();
	this.replace(replacee, replacement.operator);
	result = this.prover.getLast();
	result = GH.Prover.findMatchingPosition(result, replacee);
	// replacee.joinEq(result.copy());
	return true;
};

GH.ProofGenerator.replacer.prototype.isApplicable = function(replacee, replacement) {
	// Replacing does nothing if the left and right sides are equal.
	if (GH.ProofGenerator.replacer.isNegated(replacement) == '-.') {
		replacement = replacement.child();
	}
	if ((replacement.operands.length != 2) || (replacement.left().equals(replacement.right()))) {
		return false;
	}
	var myMatch = GH.Prover.findMatch(replacee, replacement.left());
	if (!myMatch) {
		return false;
	}
	var replacementOp = GH.ProofGenerator.replacer.getOperator(replacement);
	return this.isApplicableTraverse(myMatch, replacementOp);
};


GH.ProofGenerator.replacer.prototype.isApplicableTraverse = function(replacee, replacementOperator) {
	var sexp = replacee.parent;		
	var replaceeOperator = GH.ProofGenerator.replacer.getOperator(sexp);
	var index = sexp ? replacee.siblingIndex : 0;
	var replaceOperation = this.getReplaceOperation(replaceeOperator, replacementOperator, index);
	var actionName = replaceOperation ? replaceOperation.name : null;
	if (actionName && this.prover.symbolDefined(actionName)) {
		if (sexp) {
			if (sexp.parent && GH.ProofGenerator.replacer.isNegated(sexp.parent)) {
				sexp = sexp.parent;
			}
			return this.isApplicableTraverse(sexp, replaceOperation.resultOperator);
		} else {
			return true;
		}
	} else {
		return false;
	}
};