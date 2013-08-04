GH.ProofGenerator.evaluatorSubset = function(prover) {
  this.prover = prover;
  this.operators = ['C_'];
};

GH.ProofGenerator.evaluatorSubset.prototype.action = function(sexp) {
	return new GH.action('undefined', []);
};

GH.ProofGenerator.evaluatorSubset.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorSubset.prototype.inline = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());

	var rightMissing = GH.setUtil.getMissingElement(leftSet, rightSet);
	if (rightMissing) {
		var inLeft   = GH.operatorUtil.create('e.', [rightMissing, sexp.left()]);
		var outRight = GH.operatorUtil.create('e.', [rightMissing, sexp.right()]);
		sexp = this.prover.openExp(sexp, 'Inside Left Set');
		this.prover.evaluate(inLeft);
		sexp = this.prover.closeExp(sexp);
		sexp = this.prover.openExp(sexp, 'Outside Right Set');
		this.prover.evaluate(outRight);
		sexp = this.prover.closeExp(sexp);
		this.prover.print([], 'notSs');
		return this.prover.getLast();
	} else {
		var diff = GH.setUtil.setDifference(rightSet, leftSet);
		var setDiff = GH.setUtil.createSet(diff);
		this.prover.print([sexp.left(), setDiff], 'ssUnion');
		var result = this.prover.getLast();
		this.prover.evaluate(result.right());
		return this.prover.getLast();
	}
	return null;
};

GH.ProofGenerator.evaluatorSubset.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorSubset.prototype.calculate = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	return (GH.setUtil.getMissingElement(leftSet, rightSet) == null);
	
};