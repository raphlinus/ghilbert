// Evaluates equality and inequality expressions like 2 = 3 and 2 < 3.
GH.ProofGenerator.evaluatorEquality = function(prover) {
  this.prover = prover;
  this.operators = ['=', '<', '<='];
};

GH.ProofGenerator.evaluatorEquality.prototype.stepName = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());

	// TODO: Prove things like 3 <= 3.
	// TODO: Prove things like 1 + 5 = 2 * 3 here.
	if (leftNum == rightNum) {
		return 'eqid';
	}
	var operatorName;

    if (sexp.operator == '=') {
		operatorName = 'equals';
	} else if (sexp.operator == '<') {
		if (leftNum < rightNum) {
			operatorName = 'less';
		} else {
			operatorName = 'greaterEq';
		}
	} else if (sexp.operator == '<=') {
		if (leftNum < rightNum) {
			operatorName = 'lessEq';
		} else {
			operatorName = 'greater';
		}
	}

	return leftNum + operatorName + rightNum;
};

GH.ProofGenerator.evaluatorEquality.prototype.isApplicable = function(sexp) {
	// This is a hack to just make sure we're at least in the right file.
	return this.prover.symbolDefined('eqid');
};

GH.ProofGenerator.evaluatorEquality.prototype.hyps = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());

	if (leftNum == rightNum) {
		return [sexp.left()];
	}

	return [];
};

GH.ProofGenerator.evaluatorEquality.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorEquality.prototype.inline = function(sexp) {
	var leftNum  = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	var operator = sexp.operator;
	var inequality;

	if (leftNum == rightNum) {
		return false;
	} else if (leftNum == 0) {
		if (operator == '=') {
			inequality = this.rightNumNotZero(rightNum);
		} else if (operator == '<=') {
			inequality = this.prover.print([sexp.right()], '0le')
		} else if (operator == '<') {
			inequality = this.zeroLessThanNum(sexp.right());
		}
		// this.rightNumNotZero(rightNum);
	} else if (rightNum == 0) {
		if (operator == '=') {
			inequality = this.leftNumNotZero(leftNum);
		} else if (operator == '<=') {
			inequality = this.prover.print([sexp.left()], 'ge0');
		} else if (operator == '<') {
			inequality = this.numMoreThanZero(sexp.left());
		}
		//this.leftNumNotZero(leftNum);
	} else if (leftNum < rightNum) {
		inequality = this.handleRightGreater(leftNum, rightNum, operator);
	} else {
		inequality = this.handleLeftGreater(leftNum, rightNum, operator);
	}
	return inequality;
};

GH.ProofGenerator.evaluatorEquality.prototype.rightNumNotZero = function(num) {
	var predecessor = num - 1;
	var sexp = GH.numUtil.createNum(predecessor);
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
	this.rightNumNotZero(this.prover.calculate(sexp));
	this.prover.print([sexp], '0le');
	this.prover.println('pm3.2i');
	this.prover.getLast(); // To update the prover.
	return this.prover.remove();
};

GH.ProofGenerator.evaluatorEquality.prototype.numMoreThanZero = function(sexp) {
	var axgrtriFunc = function(sexp) {
		this.prover.println(sexp.toString() + ' (0) axgrtri');
	}
	this.prover.applyHidden(axgrtriFunc, sexp, this);
	this.leftNumNotZero(this.prover.calculate(sexp));	
	this.prover.print([sexp], 'ge0')
	this.prover.println('pm3.2i');
	this.prover.getLast(); // TODO: Check if this is still necessary. To update the prover.
	return this.prover.remove();
};

GH.ProofGenerator.evaluatorEquality.prototype.handleRightGreater = function(leftNum, rightNum, operator) {
	var diff = rightNum - leftNum;
	var sexp = GH.numUtil.createNum(diff);

	// TODO: Refactor by creating an expression like 0 < diff and then evaluate it.
	if (operator == '=') {
		this.rightNumNotZero(diff);
	} else if (operator == '<=') {
		this.prover.print([sexp], '0le')
	} else if (operator == '<') {
		this.zeroLessThanNum(sexp);
	}

	sexp = GH.numUtil.createNum(leftNum);
	
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
	return result;
};


GH.ProofGenerator.evaluatorEquality.prototype.handleLeftGreater = function(leftNum, rightNum, operator) {
	var diff = leftNum - rightNum;
	var sexp = GH.numUtil.createNum(diff);

	if (operator == '=') {
		this.leftNumNotZero(diff);
	} else if (operator == '<') {
		this.prover.print([sexp], 'ge0');
	} else if (operator == '<=') {
		this.numMoreThanZero(sexp);
	}

	sexp = GH.numUtil.createNum(rightNum);
	
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
	return result;
};

GH.ProofGenerator.evaluatorEquality.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightNum = this.prover.calculate(sexp.right());
	if (operator == '=') {
		return leftNum == rightNum;
	} else if (operator == '<') {
		return leftNum < rightNum;
	} else if (operator == '<=') {
		return leftNum <= rightNum;
	}
	return null;
};