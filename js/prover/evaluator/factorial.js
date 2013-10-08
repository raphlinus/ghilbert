GH.ProofGenerator.evaluatorFactorial = function(prover) {
  this.prover = prover;
  this.operators = ['!'];
};

GH.ProofGenerator.evaluatorFactorial.prototype.action = function(sexp) {
	var num = GH.numUtil.decimalNumberSexp(sexp.child());
	return new GH.action('factorial' + num, []);
};

GH.ProofGenerator.evaluatorFactorial.prototype.theoremName = function(sexp) {	
	return 'Factorial';
};

GH.ProofGenerator.evaluatorFactorial.prototype.isApplicable = function(sexp) {
	return true;
};

// 0! should already be in the repository.
GH.ProofGenerator.evaluatorFactorial.prototype.inline = function(sexp) {
	var num = GH.numUtil.decimalNumberSexp(sexp.child());
	var predecessor = GH.numUtil.createNum(num - 1);
	
	var result = this.prover.openExp(sexp, 'Evaluate Factorial');
	this.prover.print([predecessor], 'factorialrecurse');
	result = this.prover.getLast();
	result = this.prover.evaluate(result.left().child()).parent.parent;
	result = this.prover.evaluate(result.right().right());
	result = this.prover.closeExp(result);
	this.prover.openExp(result, 'Evaluate Factorial');
	result = this.prover.evaluate(result.left()).parent;
	result = this.prover.evaluate(result);
	return this.prover.closeExp(result);
};

GH.ProofGenerator.evaluatorFactorial.prototype.canAddTheorem = function(sexp) {
	var num = this.prover.calculate(sexp.child());
	return (num < 10);
};

GH.ProofGenerator.evaluatorFactorial.prototype.calculate = function(sexp) {
	var num = this.prover.calculate(sexp.child());
	var result = 1;
	for (var i = 1; i <= num; i++) {
		result *= i;
	}
	return result;
};
