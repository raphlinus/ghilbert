GH.ProofGenerator.operationExchanger = function(prover) {
  this.prover = prover;
};

// Each term goes: original operator, new operator, originally negated, Ghilbert step.
GH.ProofGenerator.operationExchanger.OPERATIONS = [
  ['<',  '=',  false, 'ltneq'],
  ['<',  '<=', false, 'ltle'],
  ['<=', '=',  true,  'gtneq'],
  ['<=', '<',  true,  'gtge'],
  ['=',  '<=', false, 'eqle'],
  ['=',  '<',  false, 'eqge'],

  ['C.', '=_', false, 'pssNeq'],
  ['C.', 'C_', false, 'pssSs'],
  // ['C_', '=_',  true,  'nssNeq'],  // Could easily be proved, but haven't been.
  ['C_', 'C.', true,  'nssNpss'],
  // ['=_',  'C_', false, 'seqSs'],
  ['=_',  'C.', false, 'seqNpss'],
];

GH.ProofGenerator.operationExchanger.prototype.isApplicable = function(sexp) {
	return (this.getExchange(sexp).length > 0) && (sexp.isProven);
};

GH.ProofGenerator.operationExchanger.prototype.getExchange = function(sexp) {
	var result = [];
	var OPERATIONS = GH.ProofGenerator.operationExchanger.OPERATIONS;
	for (var i = 0; i < OPERATIONS.length; i++) {
		var operation = OPERATIONS[i];
		if (this.prover.symbolDefined(operation[3])) {
			if (operation[2]) {
				// Check that the operator is negated.
				if ((sexp.operator == '-.') && (sexp.child().operator == operation[0])) {
					result.push(operation[1]);
				}
			} else if (sexp.operator == operation[0]) {
				result.push(operation[1]);
			}
		}
	}
	return result;
};

GH.ProofGenerator.operationExchanger.prototype.addSuggestion = function(sexp) {
	var exchangers = this.getExchange(sexp);
	for (var i = 0; i < exchangers.length; i++) {
		var clickHandler = 'window.direct.prover.handleClick(\'exchange\', \''+ exchangers[i] + '\')';
		this.prover.addSuggestion(exchangers[i], clickHandler, true);
	}
};

GH.ProofGenerator.operationExchanger.prototype.action = function(sexp, newOperation) {
	var OPERATIONS = GH.ProofGenerator.operationExchanger.OPERATIONS;
	for (var i = 0; i < OPERATIONS.length; i++) {
		var operation = OPERATIONS[i];
		var operator = sexp.operator == '-.' ? sexp.child().operator : sexp.operator;
		if ((operator == operation[0]) && (newOperation == operation[1])) {
			var args;
			if (operation[2]) {
				args = [sexp.child().left(), sexp.child().right()];
			} else {
				args = [sexp.left(), sexp.right()];
			}
			return new GH.action(operation[3], args);
		}
	}
	return new GH.action('undefined', []);
};

GH.ProofGenerator.operationExchanger.prototype.inline = function(sexp) {
	return false;
}

GH.ProofGenerator.operationExchanger.prototype.canAddTheorem = function(sexp) {
	return false;
}

GH.ProofGenerator.operationExchanger.prototype.addTheorem = function(sexp) {
	return false;
}