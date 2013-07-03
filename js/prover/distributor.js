// Distribute the right operand to the left like this: (a + b) * c = a * c + b * c.
GH.ProofGenerator.distributorLeft = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator (operator A B) C)');
};

GH.ProofGenerator.distributorLeft.prototype.isApplicable = function(sexp) {
	// TODO: Check that the step name is defined.
	return ((this.hyps(sexp) != null) && (this.stepName(sexp) != null));
};

GH.ProofGenerator.distributorLeft.prototype.stepName = function(sexp) {
	// TODO: Add ianor and ioran.
	var distributerOperator = sexp.operator_;
	var distributedOperator = sexp.left().operator_;
	if ((distributerOperator == '*') && (distributedOperator == '+')) {
		return 'distl';
	} else {
		return null;
	}
};

// Returns the mandatory hypotheses using the expected form.
GH.ProofGenerator.distributorLeft.prototype.hyps = function(sexp) {
	return this.prover.getHyps(sexp, this.expectedForm);
};

GH.ProofGenerator.distributorLeft.prototype.inline = function(sexp) {      return false;  };
GH.ProofGenerator.distributorLeft.prototype.addTheorem = function(sexp) {  return false;  };





// Distribute the left operand to the right like this: a * (b + c) = a * b + a * c.
GH.ProofGenerator.distributorRight = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator A (operator B C))');
};

GH.ProofGenerator.distributorRight.prototype.isApplicable = function(sexp) {
	return ((this.hyps(sexp) != null) && (this.stepName(sexp) != null));
};

GH.ProofGenerator.distributorRight.prototype.stepName = function(sexp) {
	var distributerOperator = sexp.operator_;
	var distributedOperator = sexp.right().operator_;
	if ((distributerOperator == '*') && (distributedOperator == '+')) {
		return 'distl';
	} else {
		return null;
	}
};

// Returns the mandatory hypotheses using the expected form.
GH.ProofGenerator.distributorRight.prototype.hyps = function(sexp) {
	return this.prover.getHyps(sexp, this.expectedForm);
};

GH.ProofGenerator.distributorRight.prototype.inline = function(sexp) {      return false;  };
GH.ProofGenerator.distributorRight.prototype.addTheorem = function(sexp) {  return false;  };




// Undistribute to the left like this: a * c + b * c = (a + b) * c.
GH.ProofGenerator.undistributorLeft = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator (operator A B) (operator C B))');
};

GH.ProofGenerator.undistributorLeft.prototype.isApplicable = function(sexp) {
	if (this.hyps(sexp) == null) {
		return false;
	}
	if (sexp.left().operator_.toString() != sexp.right().operator_.toString()) {
		return false;
	}
	return (this.stepName(sexp) != null);
};

GH.ProofGenerator.undistributorLeft.prototype.stepName = function(sexp) {
	var distributerOperator = sexp.left().operator_;
	var distributedOperator = sexp.operator_;
	if ((distributerOperator == '*') && (distributedOperator == '+')) {
		return 'undistl';
	} else {
		return null;
	}
};

// Returns the mandatory hypotheses using the expected form.
GH.ProofGenerator.undistributorLeft.prototype.hyps = function(sexp) {
	return this.prover.getHyps(sexp, this.expectedForm);
};

GH.ProofGenerator.undistributorLeft.prototype.inline = function(sexp) {
	this.prover.print(this.hyps(sexp), 'distl');
	var result = this.prover.getLast();
	this.prover.commute(result);
	return true;
};

GH.ProofGenerator.undistributorLeft.prototype.addTheorem = function(sexp) {         return false;  };






// Undistribute to the right like this: a * b + a * c = a * (b + c).
GH.ProofGenerator.undistributorRight = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator (operator A B) (operator A C))');
};

GH.ProofGenerator.undistributorRight.prototype.isApplicable = function(sexp) {
	if (this.hyps(sexp) == null) {
		return false;
	}
	if (sexp.left().operator_.toString() != sexp.right().operator_.toString()) {
		return false;
	}
	return (this.stepName(sexp) != null);
};

GH.ProofGenerator.undistributorRight.prototype.stepName = function(sexp) {
	var distributerOperator = sexp.left().operator_;
	var distributedOperator = sexp.operator_;
	if ((distributerOperator == '*') && (distributedOperator == '+')) {
		return 'undistr';
	} else {
		return null;
	}
};

// Returns the mandatory hypotheses using the expected form.
GH.ProofGenerator.undistributorRight.prototype.hyps = function(sexp) {
	return this.prover.getHyps(sexp, this.expectedForm);
};

GH.ProofGenerator.undistributorRight.prototype.inline = function(sexp) {
	this.prover.print(this.hyps(sexp), 'distr');
	var result = this.prover.getLast();
	this.prover.commute(result);
	return true;
};

GH.ProofGenerator.undistributorRight.prototype.addTheorem = function(sexp) {   return false;  };