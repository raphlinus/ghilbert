GH.ProofGenerator.evaluatorModulo = function(prover) {
  this.prover = prover;
  this.operators = ['mod'];
};

GH.ProofGenerator.evaluatorModulo.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return new GH.action(leftNum + 'mod' + rightNum, []);
};

GH.ProofGenerator.evaluatorModulo.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorModulo.prototype.inline = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (rightNum == 0) {
		return false;
	}
	var A = leftNum;
	var B = rightNum;
	var C = leftNum % rightNum;
	var y = (A - C) / B;
	this.prover.evaluate(this.prover.create('<', [C, B]));
	var expanded = this.prover.create('+', [this.prover.create('*', [B, y]), C]);  // B * y + C
	this.prover.evaluate(expanded);
	this.prover.print([], 'modvali');
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorModulo.prototype.canAddTheorem = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return (rightNum >= 2) && (rightNum <= 5) && (leftNum <= 10);
};

GH.ProofGenerator.evaluatorModulo.prototype.theoremName = function(sexp) {	
	return 'One-digit Modulo';
};

GH.ProofGenerator.evaluatorModulo.prototype.calculate = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return leftNum % rightNum;
};