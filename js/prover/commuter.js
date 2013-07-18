GH.ProofGenerator.commuter = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator A B)');
};

// A set of commutable operators and the theorem for commuting them.
// The first step is for when the expression has a parent.
// The second step is when the expression has no parent.
GH.ProofGenerator.commuter.OPERATIONS = [
  ['<->', 'bicom',  'bicomi'],
  ['/\\', 'ancom',  'ancomi'],
  ['\\/', 'orcom',  'orcomi'],
  [ '=' , 'eqcom',  null],
  [ '<' , 'ltcom',  null],
  ['<=' , 'lecom',  null],
  [ '+' , 'addcom', null],
  [ '*' , 'mulcom', null],
  ['=_' , 'seqcom', 'seqcomi'],
  ['u.' , 'uncom',  null],
  ['i^i', 'incom',  null],
];

GH.ProofGenerator.commuter.NEGATED_OPERATIONS = ['<', '<='];

GH.ProofGenerator.commuter.prototype.isNegated = function(sexp) {
	if (sexp.operator == '-.') {
		if (GH.ProofGenerator.commuter.NEGATED_OPERATIONS.indexOf(sexp.child().operator) >= 0) {
			return true;
		} else {
			return false;
		}
	}
};

GH.ProofGenerator.commuter.prototype.stepName = function(sexp) {
	if (this.isNegated(sexp)) {
		return 'not' + this.stepName(sexp.child());
	}

	var commuteOperations = GH.ProofGenerator.commuter.OPERATIONS;
	for (var i = 0; i < commuteOperations.length; i++) {
		if (sexp.operator == commuteOperations[i][0]) {
			if (true) { // !sexp.isProven) {     // TODO: Resolve these problems.
				return commuteOperations[i][1];
			} else {
				return commuteOperations[i][2];
			}
		}
	}
	return null;
};

GH.ProofGenerator.commuter.prototype.isApplicable = function(sexp) {
	if (this.isNegated(sexp)) {
		return true;
	}
	if (this.isNegated(sexp)) {
		return true;
	}
	if (sexp.operands.length != 2) {
		return false;
	}
	// Commuting is unnecessary if the left and right sides are equal.
	if (sexp.left().equals(sexp.right())) {
		return false;
	}

	var stepName = this.stepName(sexp);
	return this.prover.symbolDefined(stepName);
};

GH.ProofGenerator.commuter.prototype.hyps = function(sexp) {
	if (true) { // !sexp.isProven) {     // TODO: Resolve these problems.
		return this.prover.getHyps(sexp, this.expectedForm);
	} else {
		return [];
	}
};

GH.ProofGenerator.commuter.prototype.inline = function(sexp) {
	if (!this.isNegated(sexp)) {
		return false;
	}
	var result = this.prover.commute(sexp.child()).parent;
	if (sexp.parent) {
		this.prover.print([result.child().child()], 'notnotbi');
	} else {
		this.prover.print([], 'notnotri');
	}
	return true;
};
GH.ProofGenerator.commuter.prototype.canAddTheorem = function(sexp) {	return false; };