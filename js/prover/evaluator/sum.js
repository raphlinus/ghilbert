GH.ProofGenerator.evaluatorSum = function(prover) {
  this.prover = prover;
  this.operators = ['sum'];
};

GH.ProofGenerator.evaluatorSum.prototype.variableAction = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorSum.prototype.action = function(sexp) {
	return new GH.action('undefined-sum', []);
};

GH.ProofGenerator.evaluatorSum.prototype.isOperandReducable = function(index) {
	return (index != 2);
};

GH.ProofGenerator.evaluatorSum.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorSum.prototype.inline = function(sexp) {
	var lowerLimit = this.prover.calculate(sexp.operands[0]);
	var upperLimit = this.prover.calculate(sexp.operands[1]);

	sexp = this.prover.openExp(sexp, 'Expand the sum');
	for (var i = upperLimit; i >= lowerLimit; i--) {
		sexp = this.detachLast(sexp, lowerLimit, i);
		if (i > lowerLimit) {
			sexp = sexp.left();
		}
	}
	sexp = this.prover.closeExp(sexp);

	sexp = this.prover.openExp(sexp, 'Evaluate each term');
	for (var i = upperLimit; i > lowerLimit ; i--) {
		sexp = sexp.left();
	}
	for (var i = lowerLimit; i <= upperLimit; i++) {
		sexp = this.prover.evaluate(sexp);
		if (i == lowerLimit) {
			sexp = sexp.parent.right();
		} else if (i < upperLimit) {
			sexp = sexp.parent.parent.right();
		}
	}
	sexp = this.prover.closeExp(sexp);

	sexp = this.prover.openExp(sexp, 'Sum the total');
	sexp = this.prover.evaluate(sexp);
	return this.prover.closeExp(sexp);;
};

GH.ProofGenerator.evaluatorSum.prototype.detachLast = function(sexp, lowerLimit, upperLimit) {
	sexp = this.prover.openExp(sexp, 'Detach number from sum');
	if (lowerLimit == upperLimit) {
		this.prover.print([sexp.operands[0], sexp.operands[2]], 'sum1');
		sexp = this.prover.evaluate(this.prover.getLast().right());
	} else if (lowerLimit < upperLimit) {
		this.prover.evaluate(this.prover.create('<', [lowerLimit, upperLimit]));
		this.prover.print([sexp.operands[2]], 'sumdetachi');
		this.prover.evaluate(this.prover.getLast().right().right());
		var sum = this.prover.getLast().right().left()
		sexp = this.prover.evaluate(sum.operands[1]);
	}
	return this.prover.closeExp(sexp);
};

GH.ProofGenerator.evaluatorSum.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorSum.prototype.calculate = function(sexp) {
	alert('EvaluateSum.calculate not defined.');
};