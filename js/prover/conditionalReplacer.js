// Adds a condition and expresses how an expression would change if the condition was met.
// For example, it can transform      x + 3 < 7
//                    into (x = 2) -> x + 3 < 7 <-> 2 + 3 < 7 
//                      or (3 = y) -> x + 3 < 7 <-> x + y < 7
GH.ProofGenerator.conditionalReplacer = function(prover) {
	this.prover = prover;
	this.equalizer = new GH.ProofGenerator.equalizer(prover);
};

GH.ProofGenerator.conditionalReplacer.DEDUCTION_OPERATIONS = [
    [ '-.', ['notbid']],
	[ '->', ['imbi1d', 'imbi2d', 'imbi12d']],
	['<->', ['bibi1d', 'bibi2d', 'bibi12d']],
	['\\/', ['orbi1d', 'orbi2d', 'orbi12d']],
	['/\\',	['anbi1d', 'anbi2d', 'anbi12d']],
	['E.',  [null,     'exbid']],
    ['=',   ['eqeq1d', 'eqeq2d', 'eqeq12d']],
	['<=',  ['leeq1d', 'leeq2d', 'leeq12d']],
	['<',   ['lteq1d', 'lteq2d', 'lteq12d']],
	// ['>=',  ['geeq1d', 'geeq2d', 'geeq12d']],    // Not yet added.
	// ['>',   ['gteq1d', 'gteq2d', 'gteq12d']],    // Not yet added.
	['S',	['suceqd']],
	['+',	['addeq1d', 'addeq2d', 'addeq12d']],
	['*',   ['muleq1d', 'muleq2d', 'muleq12d']],     // muleq2d is missing.
	['[/]', [null, null, 'sbcbid']],                 // terms missing.
];

GH.ProofGenerator.conditionalReplacer.INITIAL_OPERATIONS = [
    ['=',   ['eqeq1', 'eqeq2']],
	['<=',  ['leeq1', 'leeq2']],
	['<',   ['lteq1', 'lteq2']],
	// ['>=',  ['geeq1', 'geeq2']],    // Not yet added.
	// ['>',   ['gteq1', 'gteq2']],    // Not yet added.
	['e.',  ['ax-eleq1', 'eleq2']],
	['S',	['suceq']],
	['+',	['addeq1', 'addeq2']],
	['*',   ['muleq1', 'muleq2']],
	['[/]', ['dfsbcq', null, null]],
	['|', ['divideseq1', 'divideseq2']],
	['recursep', ['recursepeq1', 'recursepeq2', 'recursepeq3', 'recursepeq4']],
];

GH.ProofGenerator.conditionalReplacer.prototype.action = function(sexp) {
	return new GH.action('undefined', []);
};

GH.ProofGenerator.conditionalReplacer.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.conditionalReplacer.returnTypes = {
	FAILURE: 0,
	NO_CHANGE: 1,
	MATCH: 2,
	REPLACED: 3,
};

GH.ProofGenerator.conditionalReplacer.prototype.inline = function(sexp, condition) {
	var result = this.replace(sexp, condition);
	return (result == GH.ProofGenerator.conditionalReplacer.returnTypes.REPLACED);
	/*{
		this.prover.reverseLastSteps();
		this.prover.remove();
		return true;
	} else {
		return false;
	}*/
};

GH.ProofGenerator.conditionalReplacer.prototype.printOperation = function(operations, suffix, operator, args, index) {
	var returnTypes = GH.ProofGenerator.conditionalReplacer.returnTypes;
	for (var i = 0; i < operations.length; i++) {
		if (operations[i][0] == operator) {
			var operation = operations[i][1][index];
			if (!operation) {
				return returnTypes.FAILURE;
			} else {
				this.prover.print(args, operation);
				return returnTypes.REPLACED;
			}
		}
	}

	// TODO: Use this to completely replace the table.
	var name = this.equalizer.actionName(operator, index) + suffix;
	if (!this.prover.symbolDefined(name)) {
		alert(name + ' is not defined.');
		return returnTypes.FAILURE;
	} else {
		this.prover.print(args, name);
		return returnTypes.REPLACED;
	}
};

GH.ProofGenerator.conditionalReplacer.addMissingOperands = function(sexp, presence) {
	var args = [];
	for (var i = 0; i < sexp.operands.length; i++) {
		if (Math.floor(presence / Math.pow(2, i)) % 2 == 0) {
			args.push(sexp.operands[i]);
		}
	}
	return args;
};

GH.ProofGenerator.conditionalReplacer.prototype.replace = function(sexp, condition) {
	var returnTypes = GH.ProofGenerator.conditionalReplacer.returnTypes;
	var replacedIndex = 0;
	for (var i = 0; i < sexp.operands.length; i++) {
		var result = this.replace(sexp.operands[i], condition);
		if (result == returnTypes.MATCH) {
			var args = [condition.left(), condition.right()];
			args = args.concat(GH.ProofGenerator.conditionalReplacer.addMissingOperands(sexp, Math.pow(2, i)));
			return this.printOperation(
				GH.ProofGenerator.conditionalReplacer.INITIAL_OPERATIONS, '',
				sexp.operator, args, i);
		} else if (result == returnTypes.REPLACED) {
			replacedIndex += Math.pow(2, i);
		} else if (result == returnTypes.FAILURE) {
			return result;
		}
	}
	if (replacedIndex > 0) {
		var args = GH.ProofGenerator.conditionalReplacer.addMissingOperands(sexp, replacedIndex);
		return this.printOperation(
  		    GH.ProofGenerator.conditionalReplacer.DEDUCTION_OPERATIONS, 'd',
			sexp.operator, args, replacedIndex - 1);
	} else {
		if (sexp.equals(condition.left())) {
			return returnTypes.MATCH;
		} else {
			return returnTypes.NO_CHANGE;
		}
	}
};

GH.ProofGenerator.conditionalReplacer.prototype.canAddTheorem = function(sexp) {
	return false;
};