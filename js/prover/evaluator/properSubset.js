GH.ProofGenerator.evaluatorProperSubset = function(prover) {
  this.prover = prover;
  this.operators = ['C.'];
};

GH.ProofGenerator.evaluatorProperSubset.prototype.action = function(sexp) {
	return new GH.action('undefined', []);
};

GH.ProofGenerator.evaluatorProperSubset.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorProperSubset.prototype.inline = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	if (this.calculate(sexp)) {
		var subset   = this.prover.create('C_', [sexp.left(), sexp.right()]);
		var equality = this.prover.create('=_', [sexp.left(), sexp.right()]);
		
		sexp = this.prover.openExp(sexp, 'Subset');
		this.prover.evaluate(subset);
		sexp = this.prover.closeExp(sexp);

		sexp = this.prover.openExp(sexp, 'Not equal');
		this.prover.evaluate(equality);
		sexp = this.prover.closeExp(sexp);

		this.prover.print([], 'dfpssi');
		return this.prover.getLast();
	} else if (GH.setUtil.getMissingElement(leftSet, rightSet)) {
		var subset   = this.prover.create('C_', [sexp.left(), sexp.right()]);
		this.prover.evaluate(subset);
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '⊄');
	} else {
		var equality = this.prover.create('=_', [sexp.left(), sexp.right()]);
		this.prover.evaluate(equality);
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '⊄');
	}
	return null;
};

GH.ProofGenerator.evaluatorProperSubset.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorProperSubset.prototype.calculate = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	leftSet = GH.setUtil.removeArrayDuplicates(leftSet.sort());
	rightSet = GH.setUtil.removeArrayDuplicates(rightSet.sort());
	return !GH.setUtil.equals(leftSet, rightSet) && (GH.setUtil.getMissingElement(leftSet, rightSet) == null);
};