GH.ProofGenerator.evaluatorSetEquality = function(prover) {
  this.prover = prover;
  this.operators = ['=_'];
};

GH.ProofGenerator.evaluatorSetEquality.prototype.variableAction = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	if (GH.setUtil.equals(leftSet, rightSet) || sexp.left().equals(sexp.right())) {
		return new GH.action('seqid', [sexp.left()]);
	}
};

GH.ProofGenerator.evaluatorSetEquality.prototype.action = function(sexp) {
	return new GH.action('undefined', []);
};

GH.ProofGenerator.evaluatorSetEquality.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorSetEquality.prototype.inline = function(sexp) {
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

		this.prover.print([], 'notSeq');
		return this.prover.getLast();
	}
	var leftMissing = GH.setUtil.getMissingElement(rightSet, leftSet);
	if (leftMissing) {
		var outLeft = GH.operatorUtil.create('e.', [leftMissing, sexp.left()]);
		var inRight = GH.operatorUtil.create('e.', [leftMissing, sexp.right()]);

		sexp = this.prover.openExp(sexp, 'Outside Right Set');
		this.prover.evaluate(outLeft);
		sexp = this.prover.closeExp(sexp);

		sexp = this.prover.openExp(sexp, 'Inside Left Set');
		this.prover.evaluate(inRight);
		sexp = this.prover.closeExp(sexp);

		this.prover.print([], 'notSeq2');
		return this.prover.getLast();
	}
	alert('Problems with set equality is true.');
	return false;
};

GH.ProofGenerator.evaluatorSetEquality.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorSetEquality.prototype.calculate = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	leftSet = GH.setUtil.removeArrayDuplicates(leftSet.sort());
	rightSet = GH.setUtil.removeArrayDuplicates(rightSet.sort());
	return GH.setUtil.equals(leftSet, rightSet);
};