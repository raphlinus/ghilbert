GH.ProofGenerator.evaluatorHalfMinus = function(prover) {
  this.prover = prover;
  this.operators = ['.-'];
};

GH.ProofGenerator.evaluatorHalfMinus.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return new GH.action(leftNum + 'halfminus' + rightNum, []);
};

GH.ProofGenerator.evaluatorHalfMinus.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorHalfMinus.prototype.inline = function(sexp) {
	var difference = this.calculate(sexp);
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (difference > 0) {
		this.prover.evaluate(this.prover.create('+', [rightNum, difference]));
		this.prover.commute(this.prover.getLast());
		this.prover.print([], 'addhalfminusi');
	} else {
		this.prover.evaluate(this.prover.create('<=', [leftNum, rightNum]));
		this.prover.print([], 'halfminus-negi');
	}
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorHalfMinus.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorHalfMinus.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	var difference = leftNum - rightNum;
	return (difference > 0) ? difference : 0;
};