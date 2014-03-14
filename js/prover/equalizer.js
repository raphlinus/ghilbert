GH.ProofGenerator.equalizer = function(prover) {
  this.prover = prover;
};

GH.ProofGenerator.equalizer.prototype.action = function(sexp, indices) {
	var name = this.actionName(sexp.parent.operator, indices);
	return new GH.action(name, []);
};

GH.ProofGenerator.equalizer.prototype.actionName = function(operator, indices) {
	var suffix = '';
	var types = this.prover.getOperatorTypes(operator);
	if (types.length > 2) {
		for (var i = 0; i < indices.length; i++) {
			suffix = suffix + (indices[i] + 1);
		}
	}

	var base = GH.operatorUtil.getThmName(operator, true);
	// It probably would make more sense to use the output type rather than the type of the first indices, but
	// the name isn't super important.
	var replacementType = this.prover.getOperatorTypes(operator)[indices[0]];
	var equivalence = GH.operatorUtil.getThmName(GH.operatorUtil.getEquivalenceOperator(replacementType), false);
	return base + equivalence + suffix;
};

GH.ProofGenerator.equalizer.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.equalizer.prototype.findConclusion = function(sexp, indices, variables) {
	if (indices.length == 1) {
		return this.findConclusionSingle(sexp, indices);
	} else {
		return this.findConclusionMultiple(sexp.parent, indices, variables);
	}
};

GH.ProofGenerator.equalizer.prototype.findConclusionSingle = function(sexp, indices) {
	// This is basically the same as findConclusionMultiple, just the variable names are switched around.
	// TODO: Combine duplicate code with inline.
	var operator = sexp.parent.operator;
	var dfName = 'df-' + GH.operatorUtil.getThmName(operator, false);
	var dfSymbol = this.prover.getSymbol(dfName);
	var definition = dfSymbol[3];
	definition = GH.sExpression.fromRaw(definition);
	var operandIndex = sexp.siblingIndex;

	var types = this.prover.getOperatorTypes(operator);
	var resultOperator = GH.operatorUtil.getEquivalenceOperator(types[types.length - 1]);
	var replacementType = types[operandIndex];
	var replacement = GH.Prover.variableGenerator.generateUnused(definition.left(), replacementType);
	replacement = GH.sExpression.createVariable(replacement);

	var replaceVar = definition.left().operands[operandIndex].copy();
	var replacementOperator = GH.operatorUtil.getEquivalenceOperator(types[operandIndex]);
	var condition = this.prover.create(replacementOperator, [replaceVar, replacement]);

	var copy1  = definition.left().copy();
	var copy2 = definition.left().copy();
	copy2.operands[operandIndex] = replacement;
	var replaceExp = this.prover.create(resultOperator, [copy1, copy2]);
	return this.prover.create('->', [condition, replaceExp]);
};

// Inline should never be called.
GH.ProofGenerator.equalizer.prototype.inline = function(sexp) {};

GH.ProofGenerator.equalizer.prototype.equalizeSingle = function(sexp) {
	var operator = sexp.parent.operator;
	var dfName = 'df-' + GH.operatorUtil.getThmName(operator, false);
	var dfSymbol = this.prover.getSymbol(dfName);
	var definition = dfSymbol[3];
	definition = GH.sExpression.fromRaw(definition);
	var operandIndex = sexp.siblingIndex;

	var replacementType = this.prover.getOperatorTypes(operator)[operandIndex];
	var replacement = GH.Prover.variableGenerator.generateUnused(definition.left(), replacementType);
	replacement = GH.sExpression.createVariable(replacement);

	var replaceVar = definition.left().operands[operandIndex].copy();
	var replacee = definition.right().copy();

	var replacementOperator = GH.operatorUtil.getEquivalenceOperator(replacementType);
	var condition = this.prover.create(replacementOperator, [replaceVar, replacement]);
	this.prover.condition(replacee, condition);
	var conditional = this.prover.getLast()

	var definitionArgs = dfSymbol[4];
	var originalArgs = [];
	var replacedArgs = [];
	for (var i = 0; i < definitionArgs.length; i++) {
		var arg = GH.sExpression.createVariable(definitionArgs[i][2]);
		originalArgs.push(arg);
		if (arg.operator == replaceVar.operator) {
			replacedArgs.push(replacement);
		} else {
			replacedArgs.push(arg);
		}
	}
	this.prover.print(originalArgs, dfName);
	var result = this.prover.getLast();
	this.prover.commute(result);
		
	conditional = this.prover.replace(conditional.right().left()).parent.parent;

	this.prover.print(replacedArgs, dfName);
	result = this.prover.getLast();
	this.prover.commute(result);
	this.prover.replace(conditional.right().right());
	return true;
};

GH.ProofGenerator.equalizer.prototype.getVariables = function(sexp, indices) {
	var varGenerator = new GH.Prover.variableGenerator();
	var operatorTypes = this.prover.getOperatorTypes(sexp.operator);
	var oldVariables = [];
	var newVariables = [];
	for (var i = 0; i < sexp.operands.length; i++) {
		var oldVar = varGenerator.generate(operatorTypes[i]);
		oldVariables.push(oldVar);
		if (indices.indexOf(i) != -1) {		
			newVariables.push(varGenerator.generate(operatorTypes[i]));
		} else {
			newVariables.push(oldVar);
		}
	}
	return {oldV: oldVariables, newV: newVariables};
};

GH.ProofGenerator.equalizer.prototype.equalizeMultiple = function(sexp, indices, variables) {
	for (var i = 0; i < indices.length; i++) {
		var index = indices[i];
		var args = [];
		args.push(variables.oldV[index]);
		args.push(variables.newV[index]);
		for (var j = 0; j < sexp.operands.length; j++) {
			if (j < index) {
				args.push(variables.newV[j]);
			} else if (j > index) {
				args.push(variables.oldV[j]);
			}
		}
		this.prover.print(args, this.actionName(sexp.operator, [index]));
	}
	for (var i = 0; i < indices.length - 1; i++) {
		this.prover.print([], 'anim12i');
		this.prover.transitive(this.prover.getLast().right());
	}
};

GH.ProofGenerator.equalizer.prototype.findConclusionMultiple = function(sexp, indices, variables) {
	var leftSide = null;
	var operatorTypes = this.prover.getOperatorTypes(sexp.operator);
	for (var i = indices.length - 1; i >= 0; i--) {
		var index = indices[i];
		var equivalenceOperator = GH.operatorUtil.getEquivalenceOperator(operatorTypes[index]);
		var equivalence = this.prover.create(equivalenceOperator, [variables.oldV[index], variables.newV[index]]);
		if (leftSide == null) {
			leftSide = equivalence;
		} else {
			leftSide = this.prover.create('/\\', [equivalence, leftSide]);
		}
	}
	var equivalenceOperator = GH.operatorUtil.getEquivalenceOperator(operatorTypes[operatorTypes.length - 1]);
	var oldArgs = [];
	var newArgs = [];
	for (var i = 0; i < sexp.operands.length; i++) {
		oldArgs.push(variables.oldV[i]);
		newArgs.push(variables.newV[i]);
	}
	var rightOld = this.prover.create(sexp.operator, oldArgs);
	var rightNew = this.prover.create(sexp.operator, newArgs);
	var rightSide = this.prover.create(equivalenceOperator, [rightOld, rightNew]);
	return this.prover.create('->', [leftSide, rightSide]).toString();
};

GH.ProofGenerator.equalizer.prototype.canAddTheorem = function(sexp) {
	return true;
};

GH.ProofGenerator.equalizer.prototype.addTheorem = function(sexp, unused, indices) {
	var variables = this.getVariables(sexp.parent, indices);
	this.prover.println('## <title> Equivalence for ' + sexp.parent.operator + ' </title> ##');
	this.prover.println('thm (' + this.action(sexp, indices).name + ' () () ' + this.findConclusion(sexp, indices, variables));
	this.prover.depth++;
	if (indices.length == 1) {
		this.equalizeSingle(sexp);
	} else {
		this.equalizeMultiple(sexp.parent, indices, variables);
	}
	this.prover.depth--;
	this.prover.println(')');
};
