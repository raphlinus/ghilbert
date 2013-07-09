// Evaluates equality and inequality expressions like 2 = 3 and 2 < 3.
GH.ProofGenerator.evaluatorEquality = function(prover) {
  this.prover = prover;
};

GH.ProofGenerator.evaluatorEquality.prototype.stepName = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());

	if (leftNum == rightNum) {
		return 'eqid';
	}

	var operatorName;

    if (sexp.operator == '=') {
		operatorName = 'equals';
	} else if (sexp.operator == '<') {
		operatorName = 'less';
	} else if (sexp.operator == '<=') {
		operatorName = 'lessEq';
	}

	return leftNum + 'times' + rightNum;
};

GH.ProofGenerator.evaluatorEquality.prototype.isApplicable = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());
	if (isNaN(leftNum) || isNaN(rightNum)) {
		return false;
	}
	// This is a hack to just make sure we're at least in the right file.
	return this.prover.symbolDefined('eqid');
};

GH.ProofGenerator.evaluatorEquality.prototype.hyps = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());

	if (leftNum == rightNum) {
		return [sexp.left()];
	}

	return [];
};

GH.ProofGenerator.evaluatorEquality.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorEquality.prototype.inline = function(sexp) {
	var leftNum  = GH.numUtil.sexpToNum(sexp.left());
	var rightNum = GH.numUtil.sexpToNum(sexp.right());
	var operator = sexp.operator;

	if (leftNum == rightNum) {
		return false;
	} else if (leftNum == 0) {
		if (operator == '=') {
			this.rightNumNotZero(rightNum);
		} else if (operator == '<=') {
			this.prover.print([sexp.right()], '0le')
		} else if (operator == '<') {
			this.zeroLessThanNum(sexp.right());
		}
		// this.rightNumNotZero(rightNum);
	} else if (rightNum == 0) {
		if (operator == '=') {
			this.leftNumNotZero(leftNum);
		} else if (operator == '<=') {
			this.prover.print([sexp.left()], 'ge0');
		} else if (operator == '<') {
			this.numMoreThanZero(sexp.left());
		}
		//this.leftNumNotZero(leftNum);
	} else if (leftNum < rightNum) {
		this.handleRightGreater(leftNum, rightNum, operator);
	} else {
		this.handleLeftGreater(leftNum, rightNum, operator);
	}
	return true;
};

GH.ProofGenerator.evaluatorEquality.prototype.rightNumNotZero = function(num) {
	var predecessor = num - 1;
	var sexp = GH.numUtil.numToSexp(predecessor);
	this.prover.print([sexp], 'pa_ax1');
	var result = this.prover.getLast();
	return this.prover.evaluate(result.child().right()).parent.parent;
};

GH.ProofGenerator.evaluatorEquality.prototype.leftNumNotZero = function(num) {
	sexp = this.rightNumNotZero(num);
	return this.prover.commute(sexp.child());
};

GH.ProofGenerator.evaluatorEquality.prototype.zeroLessThanNum = function(sexp) {
	var axlttri2Func = function(sexp) {
		this.prover.println('(0) ' + sexp.toString() + ' axlttri2');
	}
	this.prover.applyHidden(axlttri2Func, sexp, this);
	this.rightNumNotZero(GH.numUtil.sexpToNum(sexp));
	this.prover.print([sexp], '0le');
	this.prover.println('pm3.2i');
	this.prover.getLast(); // To update the prover.
	this.prover.remove();
};

GH.ProofGenerator.evaluatorEquality.prototype.numMoreThanZero = function(sexp) {
	var axgrtriFunc = function(sexp) {
		this.prover.println(sexp.toString() + ' (0) axgrtri');
	}
	this.prover.applyHidden(axgrtriFunc, sexp, this);
	this.leftNumNotZero(GH.numUtil.sexpToNum(sexp));	
	this.prover.print([sexp], 'ge0')
	this.prover.println('pm3.2i');
	this.prover.getLast(); // TODO: Check if this is still necessary. To update the prover.
	this.prover.remove();
};

GH.ProofGenerator.evaluatorEquality.prototype.handleRightGreater = function(leftNum, rightNum, operator) {
	var diff = rightNum - leftNum;
	var sexp = GH.numUtil.numToSexp(diff);

	// TODO: Refactor by creating an expression like 0 < diff and then evaluate it.
	if (operator == '=') {
		this.rightNumNotZero(diff);
	} else if (operator == '<=') {
		this.prover.print([sexp], '0le')
	} else if (operator == '<') {
		this.zeroLessThanNum(sexp);
	}

	sexp = GH.numUtil.numToSexp(leftNum);
	
	if (operator == '=') {
		this.prover.print([sexp], 'addneq2i');
	} else if (operator == '<=') {
		this.prover.print([sexp], 'leadd2i');
	} else if (operator == '<') {
		this.prover.print([sexp], 'ltadd2i');
	}

	result = this.prover.getLast();
	if (operator == '=') {
		result = result.child();
	}
	result = this.prover.replaceLeft(this.prover.evaluator, result);
	result = this.prover.replaceRight(this.prover.evaluator, result);
};


GH.ProofGenerator.evaluatorEquality.prototype.handleLeftGreater = function(leftNum, rightNum, operator) {
	var diff = leftNum - rightNum;
	var sexp = GH.numUtil.numToSexp(diff);

	if (operator == '=') {
		this.leftNumNotZero(diff);
	} else if (operator == '<') {
		this.prover.print([sexp], 'ge0');
	} else if (operator == '<=') {
		this.numMoreThanZero(sexp);
	}

	sexp = GH.numUtil.numToSexp(rightNum);
	
	if (operator == '=') {
		this.prover.print([sexp], 'addneq2i');
	} else if (operator == '<') {
		this.prover.print([sexp], 'geadd2i');
	} else if (operator == '<=') {
		this.prover.print([sexp], 'gtadd2i');
	}

	result = this.prover.getLast().child();
	result = this.prover.replaceRight(this.prover.evaluator, result);
	result = this.prover.replaceLeft(this.prover.evaluator, result);
};