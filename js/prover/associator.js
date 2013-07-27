// Apply the associative property on an s-expression. This does the same thing as
// reposition(result, '(A B) C', 'A (B C)');	
GH.ProofGenerator.associatorRight = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator (operator A B) C)');
};

// A set of operators and the theorem for associating them.
// The first step is for when the expression is part of another expression or is unproven.
// The second step is when the expression is proven.
GH.ProofGenerator.associatorRight.OPERATIONS = [
  ['<->', 'biass', 'biassi'],
  ['/\\', 'anass', 'anassi'],
  ['\\/', 'orass', 'orassi'],
  [ '+' , 'addass', 'addass'],
  [ '*' , 'mulass', 'mulass'],
  ['u.' , 'unass', 'unass'],
  ['i^i', 'inass', 'inass'],
];

GH.ProofGenerator.associatorRight.getActionName = function (sexp) {
	var associateOperations = GH.ProofGenerator.associatorRight.OPERATIONS;
	for (var i = 0; i < associateOperations.length; i++) {
		if (sexp.operator == associateOperations[i][0]) {
			if (!sexp.isProven) {
				return associateOperations[i][1];
			} else {
				return associateOperations[i][2];
			}
		}
	}
	return null;
};

GH.ProofGenerator.associatorRight.prototype.action = function(sexp) {
	var hyps = (!sexp.isProven) ? this.prover.getHyps(sexp, this.expectedForm) : [];
	var name = GH.ProofGenerator.associatorRight.getActionName(sexp);
	return new GH.action(name, hyps);
};

GH.ProofGenerator.associatorRight.prototype.isApplicable = function(sexp) {
	if (this.prover.getHyps(sexp, this.expectedForm) == null) {
		return false;
	}
	if (sexp.operator.toString() != sexp.left().operator.toString()) {
		return false;
	}
	var action = this.action(sexp);
	return this.prover.symbolDefined(action.name);
};
GH.ProofGenerator.associatorRight.prototype.inline = function(sexp) {      return false;  };
GH.ProofGenerator.associatorRight.prototype.canAddTheorem = function(sexp) {  return false;  };




// Apply the associative property on an s-expression. This does the same thing as
// reposition(result, 'A (B C)', '(A B) C');
GH.ProofGenerator.associatorLeft = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator A (operator B C))');
};

GH.ProofGenerator.associatorLeft.OPERATIONS = [
  ['<->', 'biassl', 'biassli'],
  ['/\\', 'anassl', 'anassli'],
  ['\\/', 'orassl', 'orassli'],
  [ '+' , 'addassl', 'addassl'],
  [ '*' , 'mulassl', 'mulassl'],
  ['u.' , 'unassl', 'unassl'],
  ['i^i', 'inassl', 'inassl'],
];

GH.ProofGenerator.associatorLeft.prototype.action = function(sexp) {
	var hyps = (!sexp.isProven) ? this.prover.getHyps(sexp, this.expectedForm) : [];
	var associateOperations = GH.ProofGenerator.associatorLeft.OPERATIONS;
	for (var i = 0; i < associateOperations.length; i++) {
		if (sexp.operator == associateOperations[i][0]) {
			if (!sexp.isProven) {
				return new GH.action(associateOperations[i][1], hyps);
			} else {
				return new GH.action(associateOperations[i][2], hyps);
			}
		}
	}
	return null;
};

GH.ProofGenerator.associatorLeft.prototype.isApplicable = function(sexp) {
	if (this.prover.getHyps(sexp, this.expectedForm) == null) {
		return false;
	}
	if (sexp.operator.toString() != sexp.right().operator.toString()) {
		return false;
	}
	return (this.action(sexp).name != null);
};

GH.ProofGenerator.associatorLeft.prototype.inline = function(sexp) {
	var hyps = (!sexp.isProven) ? this.prover.getHyps(sexp, this.expectedForm) : [];
	var name = GH.ProofGenerator.associatorRight.getActionName(sexp);
	this.prover.print(hyps, name);
	var result = this.prover.getLast();
	this.prover.commute(result);
	return true;
};

GH.ProofGenerator.associatorLeft.prototype.canAddTheorem = function(sexp) {  return false;  };