// Distribute the right operand to the left like this: (a + b) * c = a * c + b * c.
GH.ProofGenerator.distributorLeft = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator (operator A B) C)');
};

GH.ProofGenerator.distributorLeft.OPERATIONS = [
	[ '*',   '+',  'distl'],
	['\\/', '/\\', 'ordir'],
	['/\\', '\\/', 'andir'],
	['u.',  'i^i', 'undir'],
	['i^i', 'u.',  'indir'],
	// orordi could be included, but not terribly useful and probably distracting.
];

GH.ProofGenerator.distributorLeft.prototype.isApplicable = function(sexp) {
	return ((this.prover.getHyps(sexp, this.expectedForm) != null) && (this.action(sexp).name != null));
};

GH.ProofGenerator.distributorLeft.prototype.action = function(sexp) {
	// TODO: Add ianor and ioran.
	var name = GH.ProofGenerator.distributorLeft.getOperation(
	    GH.ProofGenerator.distributorLeft.OPERATIONS,
	    sexp.operator,
        sexp.left().operator);
	var hyps = this.prover.getHyps(sexp, this.expectedForm);
	return new GH.action(name, hyps);
};

GH.ProofGenerator.distributorLeft.prototype.inline = function(sexp) {         return false;  };
GH.ProofGenerator.distributorLeft.prototype.canAddTheorem = function(sexp) {  return false;  };

GH.ProofGenerator.distributorLeft.getOperation = function(operations, distributerOperator, distributedOperator) {
	for (var i = 0; i < operations.length; i++) {
		var operation = operations[i];
		if ((distributerOperator == operation[0]) && (distributedOperator == operation[1])) {
			return operation[2];
		}		
	}
	return null;
};



// Distribute the left operand to the right like this: a * (b + c) = a * b + a * c.
GH.ProofGenerator.distributorRight = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator A (operator B C))');
};

GH.ProofGenerator.distributorRight.OPERATIONS = [
	[ '*',   '+',  'distr'],
	['\\/', '/\\', 'ordi'],
	['/\\', '\\/', 'andi'],
	['e.',  'u.',  'elun'],
	['e.',  'i^i', 'elin'],
	['u.',  'i^i', 'undi'],
	['i^i', 'u.',  'indi'],
];

GH.ProofGenerator.distributorRight.prototype.isApplicable = function(sexp) {
	return ((this.prover.getHyps(sexp, this.expectedForm) != null) && (this.action(sexp).name != null));
};

GH.ProofGenerator.distributorRight.prototype.action = function(sexp) {
	var name = GH.ProofGenerator.distributorLeft.getOperation(
	    GH.ProofGenerator.distributorRight.OPERATIONS,
	    sexp.operator,
        sexp.right().operator);
	var hyps = this.prover.getHyps(sexp, this.expectedForm);
	return new GH.action(name, hyps);
};

GH.ProofGenerator.distributorRight.prototype.inline = function(sexp) {         return false;  };
GH.ProofGenerator.distributorRight.prototype.canAddTheorem = function(sexp) {  return false;  };




// Undistribute to the left like this: a * c + b * c = (a + b) * c.
GH.ProofGenerator.undistributorLeft = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator (operator A C) (operator B C))');
};

GH.ProofGenerator.undistributorLeft.prototype.isApplicable = function(sexp) {
	if (this.prover.getHyps(sexp, this.expectedForm) == null) {
		return false;
	}
	if (sexp.left().operator.toString() != sexp.right().operator.toString()) {
		return false;
	}
	return (this.action(sexp).name != null);
};

GH.ProofGenerator.undistributorLeft.prototype.action = function(sexp) {
	var forwardName = GH.ProofGenerator.distributorLeft.getOperation(
	    GH.ProofGenerator.distributorLeft.OPERATIONS,
        sexp.left().operator,
	    sexp.operator);
	var hyps = this.prover.getHyps(sexp, this.expectedForm);
	if (forwardName != null) {
		return new GH.action('undo' + forwardName, hyps);  // TODO: Get undistr to work.
	} else {
		return new GH.action(null, hyps);
	}
};

GH.ProofGenerator.undistributorLeft.prototype.inline = function(sexp) {
	var forwardName = GH.ProofGenerator.distributorLeft.getOperation(
	    GH.ProofGenerator.distributorLeft.OPERATIONS,
        sexp.left().operator,
	    sexp.operator);
	var hyps = this.prover.getHyps(sexp, this.expectedForm);
	this.prover.print(hyps, forwardName);
	var result = this.prover.getLast();
	this.prover.commute(result);
	return true;
};

GH.ProofGenerator.undistributorLeft.prototype.canAddTheorem = function(sexp) {         return false;  };






// Undistribute to the right like this: a * b + a * c = a * (b + c).
GH.ProofGenerator.undistributorRight = function(prover) {
  this.prover = prover;
  this.expectedForm = GH.sExpression.fromString('(operator (operator A B) (operator A C))');
};

GH.ProofGenerator.undistributorRight.OPERATIONS = [
	[ '*',   '+',  'distr'],
	['\\/', '/\\', 'ordi'],
	['/\\', '\\/', 'andi'],
	['e.',  '\\/', 'elun'],
	['e.',  '/\\', 'elin'],
	['u.',  'i^i', 'undi'],
	['i^i', 'u.',  'indi'],
];

GH.ProofGenerator.undistributorRight.prototype.isApplicable = function(sexp) {
	if (this.prover.getHyps(sexp, this.expectedForm) == null) {
		return false;
	}
	if (sexp.left().operator.toString() != sexp.right().operator.toString()) {
		return false;
	}
	return (this.action(sexp).name != null);
};

GH.ProofGenerator.undistributorRight.prototype.action = function(sexp) {
	var forwardName = GH.ProofGenerator.distributorLeft.getOperation(
	    GH.ProofGenerator.undistributorRight.OPERATIONS,
        sexp.left().operator,
	    sexp.operator);
	var hyps = this.prover.getHyps(sexp, this.expectedForm);
	if (forwardName != null) {
		return new GH.action('undo' + forwardName, hyps);
	} else {
		return new GH.action(null, hyps);
	}
};

GH.ProofGenerator.undistributorRight.prototype.inline = function(sexp) {
	var forwardName = GH.ProofGenerator.distributorLeft.getOperation(
	    GH.ProofGenerator.undistributorRight.OPERATIONS,
	    sexp.left().operator,
        sexp.operator);
	var action = this.action(sexp);
	this.prover.print(action.hyps, forwardName);
	var result = this.prover.getLast();
	this.prover.commute(result);
	return true;
};

GH.ProofGenerator.undistributorRight.prototype.canAddTheorem = function(sexp) {   return false;  };