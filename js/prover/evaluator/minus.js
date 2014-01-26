GH.ProofGenerator.evaluatorMinus= function(prover) {
  this.prover = prover;
  this.operators = ['-'];
};

GH.ProofGenerator.evaluatorMinus.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return new GH.action(leftNum + 'minus' + rightNum, []);
};

GH.ProofGenerator.evaluatorMinus.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorMinus.prototype.inline = function(sexp) {
	var difference = this.calculate(sexp);
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (rightNum < 0) {
		this.prover.print([sexp.left(), sexp.right().child()], 'minusneg');
		result = this.prover.getLast();
		this.prover.evaluate(result.right());
	} else if (leftNum < 0) {
		this.prover.print([sexp.left().child(), sexp.right()], 'negminus3');
		result = this.prover.getLast();
		this.prover.evaluate(result.right());
	} else if (difference >= 0) {
		this.prover.evaluate(this.prover.create('+', [difference, rightNum]));
		this.prover.print([], 'minusValuei');
	} else {
		this.prover.print([sexp.left(), sexp.right()], 'negminus');
		var result = this.prover.getLast();
		this.prover.replace(sexp);
		result = this.prover.getLast();
		this.prover.evaluate(result.right());
	}
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorMinus.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorMinus.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return leftNum - rightNum;
};