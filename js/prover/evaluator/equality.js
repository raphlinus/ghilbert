// Evaluates equality and inequality expressions like 2 = 3 and 2 < 3.
GH.ProofGenerator.evaluatorEquality = function(prover) {
  this.prover = prover;
  this.operators = ['='];
};

GH.ProofGenerator.evaluatorEquality.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (leftNum == rightNum) {
		return new GH.action('eqid', [sexp.left()]);
	}
	return new GH.action(leftNum + 'equals' + rightNum, []);
};

GH.ProofGenerator.evaluatorEquality.prototype.isApplicable = function(sexp) {
	// This is a hack to just make sure we're at least in the right file.
	return this.prover.symbolDefined('eqid');
};

GH.ProofGenerator.evaluatorEquality.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorEquality.prototype.inline = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	var operator = sexp.operator;
	var inequality;

	if (leftNum == rightNum) {
		return false;
	} else if (leftNum == 0) {
		return this.rightNumNotZero(rightNum);
	} else if (rightNum == 0) {
		return this.leftNumNotZero(sexp);
		
	} else if (leftNum < rightNum) {
		this.prover.evaluate(GH.operatorUtil.create('<', [sexp.left(), sexp.right()]));
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '=');
	} else {
		this.prover.evaluate(GH.operatorUtil.create('<=', [sexp.left(), sexp.right()]));
		var result = this.prover.getLast();
		return this.prover.operationExchange(result, '=');
	}
	return null;
};

GH.ProofGenerator.evaluatorEquality.prototype.rightNumNotZero = function(num) {
	var predecessor = num - 1;
	var sexp = GH.numUtil.createNum(predecessor);
	this.prover.print([sexp], 'pa_ax1plus');
	var result = this.prover.getLast();
	return this.prover.evaluate(result.child().right()).parent.parent;
};

GH.ProofGenerator.evaluatorEquality.prototype.leftNumNotZero = function(sexp) {
	sexp = this.prover.openExp(sexp, 'Number is Not Zero');
	var commuted = GH.operatorUtil.create('=', [sexp.right(), sexp.left()]);
	sexp = this.prover.evaluate(commuted);
	sexp = this.prover.commute(sexp.child());
	return this.prover.closeExp(sexp);
};

GH.ProofGenerator.evaluatorEquality.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return leftNum == rightNum;
};