// Apply the associative property on an s-expression. This does the same thing as
// reposition(result, '(A B) C', 'A (B C)');	
GH.ProofGenerator.associatorRight = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator (operator A B) C)');
};

// A set of operators and the theorem for associating them.
// The first step is for when the expression has a parent.
// The second step is when the expression has no parent.
GH.ProofGenerator.associatorRight.OPERATIONS = [
  ['<->', 'biass', 'biassi'],
  ['/\\', 'anass', 'anassi'],
  ['\\/', 'orass', 'orassi'],
  [ '+' , 'addass', 'addass'],
  [ '*' , 'mulass', 'mulass']
];

GH.ProofGenerator.associatorRight.getStepName = function(sexp) {
	var associateOperations = GH.ProofGenerator.associatorRight.OPERATIONS;
	for (var i = 0; i < associateOperations.length; i++) {
		if (sexp.operator_ == associateOperations[i][0]) {
			if (sexp.parent_) {
				return associateOperations[i][1];
			} else {
				return associateOperations[i][2];
			}
		}
	}
	return null;
};

GH.ProofGenerator.associatorRight.prototype.stepName = function(sexp) {
	return GH.ProofGenerator.associatorRight.getStepName(sexp);
};

GH.ProofGenerator.associatorRight.prototype.isApplicable = function(sexp) {
	if (this.prover.getHyps(sexp, this.expectedForm) == null) {
		return false;
	}
	if (sexp.operator_.toString() != sexp.left().operator_.toString()) {
		return false;
	}
	var stepName = this.stepName(sexp);
	return this.prover.symbolDefined(stepName);
};

GH.ProofGenerator.associatorRight.prototype.hyps = function(sexp) {
	if ((sexp.parent_) || (GH.operatorUtil.getType(sexp) != 'wff')) {
		return this.prover.getHyps(sexp, this.expectedForm);
	} else {
		return [];
	}
};

GH.ProofGenerator.associatorRight.prototype.inline = function(sexp) {      return false;  };
GH.ProofGenerator.associatorRight.prototype.addTheorem = function(sexp) {  return false;  };




// Apply the associative property on an s-expression. This does the same thing as
// reposition(result, 'A (B C)', '(A B) C');
GH.ProofGenerator.associatorLeft = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator A (operator B C))');
};

GH.ProofGenerator.associatorLeft.prototype.stepName = function(sexp) {
	var name = GH.ProofGenerator.associatorRight.getStepName(sexp);
	if (name != null) {
		return name + 'Left';
	} else {
		return null;
	}
};

GH.ProofGenerator.associatorLeft.prototype.isApplicable = function(sexp) {
	if (this.prover.getHyps(sexp, this.expectedForm) == null) {
		return false;
	}
	if (sexp.operator_.toString() != sexp.right().operator_.toString()) {
		return false;
	}
	var stepName = GH.ProofGenerator.associatorRight.getStepName(sexp);
	return this.prover.symbolDefined(stepName);
};

GH.ProofGenerator.associatorLeft.prototype.hyps = function(sexp) {
	if ((sexp.parent_) || (GH.operatorUtil.getType(sexp) != 'wff')) {
		return this.prover.getHyps(sexp, this.expectedForm);
	} else {
		return [];
	}
};

GH.ProofGenerator.associatorLeft.prototype.inline = function(sexp) {
	var stepName = GH.ProofGenerator.associatorRight.getStepName(sexp);
	this.prover.print(this.hyps(sexp), stepName);
	var result = this.prover.getLast();
	this.prover.commute(result);
	return true;
};

GH.ProofGenerator.associatorLeft.prototype.addTheorem = function(sexp) {  return false;  };