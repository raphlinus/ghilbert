GH.ProofGenerator.evaluatorSubstitution = function(prover) {
  this.prover = prover;
  this.operators = ['[/]'];
};

GH.ProofGenerator.evaluatorSubstitution.prototype.variableAction = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorSubstitution.prototype.action = function(sexp) {
	return new GH.action('undefined-apply', []);
};

GH.ProofGenerator.evaluatorSubstitution.prototype.isApplicable = function(sexp) {
	// The expression must depend on the binding variable or there is nothing to do.
	return GH.ProofGenerator.evaluatorApply.dependsOn(sexp.operands[2], sexp.operands[1]);
};

GH.ProofGenerator.evaluatorSubstitution.prototype.inline = function(sexp) {
	var condition = this.prover.create('=', [sexp.operands[1], sexp.operands[0]]);
	this.prover.condition(sexp.operands[2], condition);
	this.prover.print([], 'sbcie');
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorSubstitution.prototype.isOperandReducable = function(index) {
	return false;
};

GH.ProofGenerator.evaluatorSubstitution.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorSubstitution.prototype.calculate = function(sexp) {
	alert('EvaluateSubstitution.calculate not defined.');
};