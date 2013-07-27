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

GH.ProofGenerator.commuter.prototype.action = function(sexp) {
	if (this.isNegated(sexp)) {
		var action = this.action(sexp.child());
		action.name = 'not' + positiveAction.name;
		return action;
	}

	//var hyps = !sexp.isProven ? this.prover.getHyps(sexp, this.expectedForm) : []; // TODO: Resolve these problems.
	var hyps = this.prover.getHyps(sexp, this.expectedForm);
	var commuteOperations = GH.ProofGenerator.commuter.OPERATIONS;
	for (var i = 0; i < commuteOperations.length; i++) {
		if (sexp.operator == commuteOperations[i][0]) {
			if (true) { // !sexp.isProven) {     // TODO: Resolve these problems.
				return new GH.action(commuteOperations[i][1], hyps);
			} else {
				return new GH.action(commuteOperations[i][2], hyps);
			}
		}
	}
	return new GH.action(null, []);
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

	var action = this.action(sexp);
	return this.prover.symbolDefined(action.name);
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