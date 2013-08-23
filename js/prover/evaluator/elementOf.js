GH.ProofGenerator.evaluatorElementOf = function(prover) {
  this.prover = prover;
  this.operators = ['e.'];
  this.repeator = new GH.ProofGenerator.repeatedElementOf(prover);
};

GH.ProofGenerator.evaluatorElementOf.prototype.variableAction = function(sexp) {
	if ((sexp.right().operator == '{}') &&
	        ((this.calculate(sexp)) || (sexp.right().child().equals(sexp.left())))) {
		return new GH.action('snid', [sexp.left()]);
	}
	
	if (sexp.right().operator == '{/}') {
		return new GH.action('noel', [sexp.left()]);
	}
	return null;
};

GH.ProofGenerator.evaluatorElementOf.prototype.action = function(sexp) {
	return new GH.action('elementOf', []);
};

GH.ProofGenerator.evaluatorElementOf.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorElementOf.prototype.inline = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	var index = rightSet.indexOf(leftNum);

	if (index >= 0) {
		return this.insideSet(sexp, leftNum, rightSet, index);
	} else {
		return this.notInsideSet(sexp, leftNum);
	}
	
	return null;
};

GH.ProofGenerator.evaluatorElementOf.prototype.insideSet = function(sexp, leftNum, rightSet, index) {
	var singleton = GH.sExpression.createOperator('{}', [sexp.left()]);
	var inSingleton = GH.sExpression.createOperator('e.', [sexp.left(), singleton]);
	this.prover.openExp(sexp, 'Element is in Singleton');
	var result = this.prover.evaluate(inSingleton);
	this.prover.closeExp(sexp);
	var precedingSet = rightSet.slice(0, index)
	var succeedingSet = rightSet.slice(index + 1, rightSet.length)
	if (succeedingSet.length > 0) {
		this.prover.openExp(sexp, 'Element is part of a Larger Set');
		succeedingSet = GH.setUtil.createSet(succeedingSet);
		this.prover.print([succeedingSet], 'unionAttach1');
		this.prover.closeExp(sexp);
	}
	if (precedingSet.length > 0) {
		this.prover.openExp(sexp, 'Element is part of a Larger Set');
		precedingSet = GH.setUtil.createSet(precedingSet);
		this.prover.print([precedingSet], 'unionAttach2');
		this.prover.closeExp(sexp);
	}
	result = this.prover.getLast();
	this.prover.openExp(sexp, 'Reorder elements');
	this.prover.evaluate(result.right());
	return this.prover.closeExp(sexp);
};

/* GH.ProofGenerator.evaluatorElementOf.prototype.notInSingleton = function(sexp) {
	this.prover.print([sexp.left(), sexp.right().child()], 'elsnc');
	var result = this.prover.getLast();
	this.prover.evaluate(result.right());
	return this.prover.remove();
};

GH.ProofGenerator.evaluatorElementOf.prototype.notInsideSet = function(sexp, leftNum, rightSet) {
	// TODO: Reorganize this so the inequalities are shown all at once and it's not recursive.
	var inequality = GH.operatorUtil.create('=', [leftNum, sexp.right().left().child()]);
	this.prover.evaluate(inequality);
	var inRightPart = GH.operatorUtil.create('e.', [leftNum, sexp.right().right()]);
	this.prover.evaluate(inRightPart);
	this.prover.print([], 'notInSingletonUnion');
	return this.prover.getLast();
};*/

GH.ProofGenerator.evaluatorElementOf.prototype.notInsideSet = function(sexp, leftNum) {
	var temp = sexp.right();
	while (temp.operator == 'u.') {
		var inequality = GH.operatorUtil.create('=', [leftNum, temp.left().child()]);
		this.prover.evaluate(inequality);
		temp = temp.right();
	}
	var inequality = GH.operatorUtil.create('=', [leftNum, temp.child()]);
	this.prover.evaluate(inequality);
	this.prover.apply(this.repeator, sexp);
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorElementOf.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorElementOf.prototype.calculate = function(sexp) {
	var leftNum = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	return rightSet && (rightSet.indexOf(leftNum) >= 0);
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


// This generates theorems used by evaluateElementOf.
GH.ProofGenerator.repeatedElementOf = function(prover) {
	this.prover = prover;
};

GH.ProofGenerator.repeatedElementOf.prototype.action = function(sexp) {
	var set = this.prover.calculate(sexp.right());
	var name;
	if (set.length == 1) {
		name = 'notInSingleton';
	} else {
		name = 'notIn' + set.length + 'set'
	}
	return new GH.action(name, []);
};

GH.ProofGenerator.repeatedElementOf.prototype.canAddTheorem = function(sexp) {
	return this.prover.symbolDefined('notInSingleton') && this.prover.symbolDefined('notInSingletonUnion');
};

GH.ProofGenerator.repeatedElementOf.prototype.addTheorem = function(sexp) {
	var set = this.prover.calculate(sexp.right());
	sexp = sexp.copy();
	this.prover.println('## <title> Element Not Inside ' + set.length + '-Set </title>');

	// Find name.
	var name = this.action(sexp).name;

	// Find hypotheses.
	var varGenerator = new GH.Prover.variableGenerator();
	var primaryVar = varGenerator.generate('nat');
	var hyps = '';
	var hypVariables = [];
	for (var i = 0; i < set.length; i++) {
		hypVariables.push(varGenerator.generate('nat'));
		hyps += 'hyp' + i + ' (-. (= ' + primaryVar + ' ' + hypVariables[i] + ')) ';
	}
	
	// Find conclusion.
	var temp = sexp;
	var count = 0;
	temp.replaceOperand(new GH.sExpression(primaryVar, 0, 0, true), 0);
	temp = temp.right();
	while (temp.operator == 'u.') {
		temp.left().replaceOperand(new GH.sExpression(hypVariables[count], 0, 0, true), 0);
		count++;
		temp = temp.right();
	}
	temp.parent.right().replaceOperand(new GH.sExpression(hypVariables[count], 0, 0, true), 0);
	var conclusion = '(-. ' + sexp.toString() + ')';

	this.prover.println('thm (' + name + ' () (' + hyps + ') ' + conclusion);
	this.prover.depth++;
	for (var i = 0; i < set.length; i++) {
		this.prover.println('hyp' + i);
	}
	for (var i = 0; i < set.length; i++) {
		if (i == 0) {
			this.prover.println('notInSingleton');
		} else {
			this.prover.println('notInSingletonUnion');
		}
	}
	this.prover.depth--;
	this.prover.println(')');
};
