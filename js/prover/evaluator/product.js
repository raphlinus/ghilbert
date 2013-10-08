GH.ProofGenerator.evaluatorProduct = function(prover) {
  this.prover = prover;
  this.operators = ['product'];
};

GH.ProofGenerator.evaluatorProduct.prototype.variableAction = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorProduct.prototype.action = function(sexp) {
	return new GH.action('undefined-product', []);
};

GH.ProofGenerator.evaluatorProduct.prototype.isOperandReducable = function(index) {
	return (index != 2);
};

GH.ProofGenerator.evaluatorProduct.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorProduct.prototype.inline = function(sexp) {
	var lowerLimit = this.prover.calculate(sexp.operands[0]);
	var upperLimit = this.prover.calculate(sexp.operands[1]);

	sexp = this.prover.openExp(sexp, 'Expand the product');
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

	sexp = this.prover.openExp(sexp, 'Multiply all terms');
	sexp = this.prover.evaluate(sexp);
	return this.prover.closeExp(sexp);;
};

GH.ProofGenerator.evaluatorProduct.prototype.detachLast = function(sexp, lowerLimit, upperLimit) {
	sexp = this.prover.openExp(sexp, 'Detach number from product');
	if (lowerLimit == upperLimit) {
		this.prover.print([sexp.operands[0], sexp.operands[2]], 'product1');
		sexp = this.prover.evaluate(this.prover.getLast().right());
	} else if (lowerLimit < upperLimit) {
		this.prover.evaluate(this.prover.create('<', [lowerLimit, upperLimit]));
		this.prover.print([sexp.operands[2]], 'productdetachi');
		this.prover.evaluate(this.prover.getLast().right().right());
		var product = this.prover.getLast().right().left()
		sexp = this.prover.evaluate(product.operands[1]);
	}
	return this.prover.closeExp(sexp);
};

GH.ProofGenerator.evaluatorProduct.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorProduct.prototype.calculate = function(sexp) {
	alert('EvaluateProduct.calculate not defined.');
};