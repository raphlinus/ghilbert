GH.ProofGenerator.evaluatorElementOf = function(prover) {
  this.prover = prover;
  this.operators = ['e.'];
};

GH.ProofGenerator.evaluatorElementOf.prototype.stepName = function(sexp) {
	if ((sexp.right().operator == '{}') && (this.calculate(sexp))) {
		return 'snid';
	}
	if (sexp.right().operator == '{/}') {
		return 'noel';
	}
	return 'elementOf';
};

GH.ProofGenerator.evaluatorElementOf.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorElementOf.prototype.hyps = function(sexp) {
	if ((sexp.right().operator == '{}') && (this.calculate(sexp))) {
		return [sexp.left()];
	}
	if (sexp.right().operator == '{/}') {
		return [sexp.left()];
	}
	return [];
};

GH.ProofGenerator.evaluatorElementOf.prototype.inline = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	var index = rightSet.indexOf(leftNum);

	if (index >= 0) {
		this.insideSet(sexp, leftNum, rightSet, index);
	} else {
		if (sexp.right().operator == '{}') {
			this.notInSingleton(sexp);
		} else {
			this.notInsideSet(sexp, leftNum, rightSet);
		}
	}
	
	return true;
};

GH.ProofGenerator.evaluatorElementOf.prototype.notInSingleton = function(sexp) {
	this.prover.print([sexp.left(), sexp.right().child()], 'elsnc');
	var result = this.prover.getLast();
	this.prover.evaluate(result.right());
	return this.prover.remove();
};

GH.ProofGenerator.evaluatorElementOf.prototype.insideSet = function(sexp, leftNum, rightSet, index) {
	var singleton = GH.sExpression.createOperator('{}', [sexp.left()]);
	var inSingleton = GH.sExpression.createOperator('e.', [sexp.left(), singleton]);
	var result = this.prover.evaluate(inSingleton);
	var precedingSet = rightSet.slice(0, index)
	var succeedingSet = rightSet.slice(index + 1, rightSet.length)
	if (succeedingSet.length > 0) {
		succeedingSet = GH.setUtil.createSet(succeedingSet);
		this.prover.print([succeedingSet], 'unionAttach1');
	}
	if (precedingSet.length > 0) {
		precedingSet = GH.setUtil.createSet(precedingSet);
		this.prover.print([precedingSet], 'unionAttach2');
	}
	result = this.prover.getLast();
	this.prover.evaluate(result.right());
};

GH.ProofGenerator.evaluatorElementOf.prototype.notInsideSet = function(sexp, leftNum, rightSet) {
	// TODO: Reorganize this so the inequalities are shown all at once and it's not recursive.
	var inLeftPart = GH.sExpression.createOperator('e.', [sexp.left(), sexp.right().left()]);
	this.prover.evaluate(inLeftPart);
	var inRightPart = GH.sExpression.createOperator('e.', [sexp.left(), sexp.right().right()]);
	this.prover.evaluate(inRightPart);
	this.prover.print([], 'notInUnion');
};

GH.ProofGenerator.evaluatorElementOf.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorElementOf.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	return (rightSet.indexOf(leftNum) >= 0);
};



// Singleton
GH.ProofGenerator.evaluatorSingleton = function(prover) {
  this.prover = prover;
  this.operators = ['{}'];
};

GH.ProofGenerator.evaluatorSingleton.prototype.isApplicable = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorSingleton.prototype.calculate = function(sexp) {
	var num = this.prover.calculate(sexp.child());
	return [num];
};