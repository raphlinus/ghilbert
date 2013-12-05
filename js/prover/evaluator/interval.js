GH.ProofGenerator.evaluatorInterval = function(prover) {
  this.prover = prover;
  this.operators = ['{...}'];
};

GH.ProofGenerator.evaluatorInterval.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (leftNum == rightNum) {
		return new GH.action('intervalSn', [sexp.left()]);
	}
	return new GH.action(leftNum + 'interval' + rightNum, []);
};

GH.ProofGenerator.evaluatorInterval.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorInterval.prototype.inline = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (leftNum < rightNum) {
		var decremented;
		if ((rightNum - 1) % 10 != 0) {
			decremented = this.prover.unevaluate(this.prover.create('+', [rightNum - 1, 1]), sexp.right());
		} else {
			// 11 is already in the form 10 + 1.
			decremented = sexp.right().copy();
		}
		this.prover.evaluate(this.prover.create('<=', [leftNum, rightNum - 1]));
		this.prover.print([], 'intervalAttach');
		var result = this.prover.getLast();
		this.prover.commute(result);
		result = this.prover.replace(decremented);
		result = this.prover.evaluate(result.right().child());
		result = this.prover.evaluate(result.parent.parent.left());
		result = this.prover.evaluate(result.parent);
		return true;
	}
};

GH.ProofGenerator.evaluatorInterval.prototype.canAddTheorem = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorInterval.prototype.theoremName = function(sexp) {	
	return 'Interval of Natural Numbers';
};

GH.ProofGenerator.evaluatorInterval.prototype.calculate = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	var result = [];
	for (var i = leftNum; i <= rightNum; i++) {
		result.push(i);
	}
	return result;
};