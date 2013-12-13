// Adds a condition and expresses how an expression would change if the condition was met.
// For example, it can transform      x + 3 < 7
//                    into (x = 2) -> x + 3 < 7 <-> 2 + 3 < 7 
//                      or (3 = y) -> x + 3 < 7 <-> x + y < 7
GH.ProofGenerator.conditionalReplacer = function(prover) {
	this.prover = prover;
	this.equalizer = new GH.ProofGenerator.equalizer(prover);
};

// These tables are used for theorems with non-standard names.
GH.ProofGenerator.conditionalReplacer.DEDUCTION_OPERATIONS = [
	['E.',  [null,     'exbid']],
	['[/]', [null, null, 'sbcbid']],
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
	REPLACED: 2,
};

GH.ProofGenerator.conditionalReplacer.prototype.inline = function(sexp, condition) {
	var result = this.replace(sexp, condition);
	return (result == GH.ProofGenerator.conditionalReplacer.returnTypes.REPLACED);
};

GH.ProofGenerator.conditionalReplacer.prototype.printOperation = function(operator, args, indices) {
	var operations = GH.ProofGenerator.conditionalReplacer.DEDUCTION_OPERATIONS;
	var returnTypes = GH.ProofGenerator.conditionalReplacer.returnTypes;
	if (indices.length == 1) {
		for (var i = 0; i < operations.length; i++) {
			if (operations[i][0] == operator) {
				var operation = operations[i][1][indices[0]];
				if (!operation) {
					return returnTypes.FAILURE;
				} else {
					this.prover.print(args, operation);
					return returnTypes.REPLACED;
				}
			}
		}
	}

	var name = this.equalizer.actionName(operator, indices) + 'd';
	if (!this.prover.symbolDefined(name)) {
		alert(name + ' is not defined.');
		return returnTypes.FAILURE;
	} else {
		this.prover.print(args, name);
		return returnTypes.REPLACED;
	}
};

GH.ProofGenerator.conditionalReplacer.addMissingOperands = function(sexp, replacedIndices) {
	var args = [];
	for (var i = 0; i < sexp.operands.length; i++) {
		if (replacedIndices.indexOf(i) == -1) {
			args.push(sexp.operands[i]);
		}
	}
	return args;
};

GH.ProofGenerator.conditionalReplacer.prototype.replace = function(sexp, condition) {
	var returnTypes = GH.ProofGenerator.conditionalReplacer.returnTypes;
	var replacedIndices = [];
	for (var i = 0; i < sexp.operands.length; i++) {
		var result = this.replace(sexp.operands[i], condition);
		if (result == returnTypes.REPLACED) {
			replacedIndices.push(i);
		} else if (result == returnTypes.FAILURE) {
			return result;
		}
	}
	if (replacedIndices.length > 0) {
		var args = GH.ProofGenerator.conditionalReplacer.addMissingOperands(sexp, replacedIndices);
		return this.printOperation(sexp.operator, args, replacedIndices);
	} else {
		if (sexp.equals(condition.left())) {
			this.prover.print([condition], 'id');
			return returnTypes.REPLACED;
		} else {
			return returnTypes.NO_CHANGE;
		}
	}
};

GH.ProofGenerator.conditionalReplacer.prototype.canAddTheorem = function(sexp) {
	return false;
};