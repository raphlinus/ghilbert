// Performs multiple replacement simultaneously
GH.ProofGenerator.multiReplacer = function(prover) {
  this.prover = prover;
};

/*GH.ProofGenerator.multiReplacer.changeExp = function(condition, replacee) {
	if (replacee.equals(condition.left())) {
		return condition.right();
	}
	for (var i = 0; i < replacee.operands; i++) {
		replacee.operands[i] = GH.ProofGenerator.multiReplacer.changeExp(condition, replacee.operands[i]);
	}
	return replacee;
};*/

GH.ProofGenerator.multiReplacer.prototype.replace = function(replacee, replacer) {
	var condition = replacer.parent;
	this.prover.println([], '');
	if (replacer.siblingIndex == 1) {
		condition = this.prover.commute(condition);		
	}
	this.prover.condition(replacee, condition);
	this.prover.replace(condition);
	this.prover.reverseLastSteps();
	this.prover.remove();


	/*var result = GH.ProofGenerator.multiReplacer.changeExp(condition, replacee);
	this.prover.println([result], 'biRemove1');
	this.prover.println([condition], 'imbi2i');*/
};

GH.ProofGenerator.multiReplacer.prototype.isApplicable = function(sexp) {
	return true;
};


/*
GH.ProofGenerator.multiReplacer.prototype.action = function(sexp) {
	return new GH.action('undefined', []);
};

GH.ProofGenerator.multiReplacer.prototype.inline = function(sexp) {
};

GH.ProofGenerator.multiReplacer.prototype.canAddTheorem = function(sexp) {
	return false;
};*/