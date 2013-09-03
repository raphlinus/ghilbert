GH.ProofGenerator.evaluatorDiv = function(prover) {
  this.prover = prover;
  this.operators = ['div'];
};

GH.ProofGenerator.evaluatorDiv.prototype.action = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return new GH.action(leftNum + 'div' + rightNum, []);
};

GH.ProofGenerator.evaluatorDiv.prototype.isApplicable = function(sexp) {
	var rightNum = this.prover.calculate(sexp.right());
	return (rightNum != 0);
};

GH.ProofGenerator.evaluatorDiv.prototype.inline = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	
	var A = leftNum;
	var B = rightNum;
	var C = Math.floor(leftNum / rightNum);
	this.prover.evaluate(GH.operatorUtil.create('<=', [B, 0]));  // B > 0
	var BC = GH.operatorUtil.create('*', [B, C]);
	var AmodB = GH.operatorUtil.create('mod', [A, B]);
	var expanded = GH.operatorUtil.create('+', [BC, AmodB]);  // B * C + A mod B
	this.prover.evaluate(expanded);
	this.prover.print([], 'divval');
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorDiv.prototype.canAddTheorem = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return ((leftNum % rightNum == 0) && (leftNum < 50) && (rightNum > 1) && (leftNum / rightNum >= 2));
};

GH.ProofGenerator.evaluatorDiv.prototype.theoremName = function(sexp) {	
	return 'Whole Number Division';
};

GH.ProofGenerator.evaluatorDiv.prototype.calculate = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	return Math.floor(leftNum / rightNum);
};