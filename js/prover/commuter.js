GH.ProofGenerator.commuter = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator A B)');
};

// A set of commutable operators and the theorem for commuting them.
// The first step is for when the expression has a parent.
// The second step is when the expression has no parent.
GH.ProofGenerator.commuter.OPERATIONS = [
  ['<->', 'bicom', 'bicomi'],
  ['/\\', 'ancom', 'ancomi'],
  ['\\/', 'orcom', 'orcomi'],
  [ '=' , 'eqcom', 'eqcomi'],
  [ '<' , 'ltcom', 'ltcomi'],
  ['<=' , 'lecom', 'lecomi'],
  [ '+' , 'addcom', null],
  [ '*' , 'mulcom', null]
];

GH.ProofGenerator.commuter.prototype.stepName = function(sexp) {
	var commuteOperations = GH.ProofGenerator.commuter.OPERATIONS;
	for (var i = 0; i < commuteOperations.length; i++) {
		if (sexp.operator == commuteOperations[i][0]) {
			if (!sexp.isProven) {
				return commuteOperations[i][1];
			} else {
				return commuteOperations[i][2];
			}
		}
	}
	return null;
};

GH.ProofGenerator.commuter.prototype.isApplicable = function(sexp) {
	// TODO: Maybe use expected form here.
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
	if (!sexp.isProven) {
		return this.prover.getHyps(sexp, this.expectedForm);
	} else {
		return [];
	}
};

GH.ProofGenerator.commuter.prototype.inline = function(sexp) {	   		return false; };
GH.ProofGenerator.commuter.prototype.canAddTheorem = function(sexp) {	return false; };