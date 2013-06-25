GH.ProofGenerator.evaluatorMultiply = function(prover) {
  this.prover = prover;
};

GH.ProofGenerator.evaluatorMultiply.prototype.stepName = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());

	if (leftNum == 0) {
		return 'pa_ax5r';
	}
	if (rightNum == 0) {
		return 'pa_ax5'
	}
	if (leftNum == 1) {
		return 'mulidr'
	}
	if (rightNum == 1) {
		return 'mulid'
	}

	return leftNum + 'times' + rightNum;
};

GH.ProofGenerator.evaluatorMultiply.prototype.isApplicable = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());
	if (isNaN(leftNum) || isNaN(rightNum)) {
		return false
	}
	// If the full expression already is a decimal number, there is nothing to evaluate.
	if (!isNaN(GH.numUtil.decimalNumberSexp(sexp))) {
		// If the whole 
		return false;
	}
	return true;
};

GH.ProofGenerator.evaluatorMultiply.prototype.hyps = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());

	if ((leftNum == 0) || (leftNum == 1)) {
		return [sexp.right()];
	}
	if ((rightNum == 0) || (rightNum == 1)) {
		return [sexp.left()];
	}
	return [];
};

GH.ProofGenerator.evaluatorMultiply.prototype.addTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorMultiply.prototype.inline = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());

	
	if ((leftNum == 0) || (leftNum == 1) || (rightNum == 0) || (rightNum == 1)) {
		return false;
	}
	return true;
};