GH.ProofGenerator.evaluatorFibonacci = function(prover) {
  this.prover = prover;
  this.operators = ['fibonacci'];
};

GH.ProofGenerator.evaluatorFibonacci.prototype.action = function(sexp) {
	var num = GH.numUtil.decimalNumberSexp(sexp.child());
	return new GH.action('fibonacci' + num, []);
};

GH.ProofGenerator.evaluatorFibonacci.prototype.theoremName = function(sexp) {	
	return 'Fibonacci';
};

GH.ProofGenerator.evaluatorFibonacci.prototype.isApplicable = function(sexp) {
	return true;
};

// F_0 and F_1 should already be in the repository.
GH.ProofGenerator.evaluatorFibonacci.prototype.inline = function(sexp) {
	var num = GH.numUtil.decimalNumberSexp(sexp.child());
	var predecessor = GH.numUtil.createNum(num - 2);
	
	var result = this.prover.openExp(sexp, 'Add Indices');
	this.prover.print([predecessor], 'df-fibRecurse');
	result = this.prover.getLast();
	result = this.prover.evaluate(result.left().child()).parent.parent;
	result = this.prover.evaluate(result.right().right().child()).parent.parent.parent;
	result = this.prover.closeExp(result);
	result = this.prover.openExp(result, 'Insert Previous Numbers');
	result = this.prover.evaluate(result.left()).parent;
	result = this.prover.evaluate(result.right()).parent;
	result = this.prover.closeExp(result);
	result = this.prover.openExp(result, 'Sum Fibonacci Numbers');
	result = this.prover.evaluate(result);
	return this.prover.closeExp(result);
};

GH.ProofGenerator.evaluatorFibonacci.prototype.canAddTheorem = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorFibonacci.prototype.calculate = function(sexp) {
	var num = this.prover.calculate(sexp.child());
	var result0 = 0;
	var result1 = 1;
	for (var i = 0; i < num; i++) {
		var result2 = result0 + result1;
		result0 = result1;
		result1 = result2;
	}
	return result0;
};
