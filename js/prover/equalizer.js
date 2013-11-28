GH.ProofGenerator.equalizer = function(prover) {
  this.prover = prover;
};

GH.ProofGenerator.equalizer.UNIQUE_NAMES = {
	eleq1: 'ax-eleq1',
	iotaeq: 'ax-iotaeq'
};

GH.ProofGenerator.equalizer.prototype.action = function(sexp) {
	var name = this.actionName(sexp.parent.operator, sexp.siblingIndex);
	return new GH.action(name, []);
};

GH.ProofGenerator.equalizer.prototype.actionName = function(operator, index) {
	var suffix = '';
	var types = this.prover.getOperatorTypes(operator);
	if (types.length > 2) {
		suffix = index + 1;
	}

	var base = GH.operatorUtil.getThmName(operator);
	var replacementType = this.prover.getOperatorTypes(operator)[index];
	var equivalence = GH.operatorUtil.getThmName(GH.operatorUtil.getEquivalenceOperator(replacementType));
	return base + equivalence + suffix;
};

GH.ProofGenerator.equalizer.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.equalizer.prototype.findConclusion = function(sexp) {
	// TODO: Combine duplicate code with inline.
	var operator = sexp.parent.operator;
	var dfName = 'df-' + GH.operatorUtil.getThmName(operator);
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

GH.ProofGenerator.equalizer.prototype.inline = function(sexp) {
	var operator = sexp.parent.operator;
	var dfName = 'df-' + GH.operatorUtil.getThmName(operator);
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

GH.ProofGenerator.equalizer.prototype.canAddTheorem = function(sexp) {
	return true;
};

GH.ProofGenerator.equalizer.prototype.addTheorem = function(sexp) {
	this.prover.println('## <title> Equivalence for ' + GH.operatorUtil.getUnicode(sexp.parent.operator) + ' </title> ##');
	this.prover.println('thm (' + this.action(sexp).name + ' () () ' + this.findConclusion(sexp));
	this.prover.depth++;
	this.inline(sexp);
	this.prover.depth--;
	this.prover.println(')');
};
