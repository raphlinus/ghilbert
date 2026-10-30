GH.ProofGenerator.evaluatorUnion = function(prover) {
  this.prover = prover;
  this.operators = ['u.'];
};

GH.ProofGenerator.evaluatorUnion.prototype.variableAction = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	if (rightSet && (rightSet.length == 0)) {
		return new GH.action('unid', [sexp.left()]);
	} else if (leftSet && (leftSet.length == 0)) {
		return new GH.action('unidr', [sexp.right()]);
	} else if (GH.setUtil.equals(leftSet, rightSet) || sexp.left().equals(sexp.right())) {
		return new GH.action('unidm', [sexp.left()]);
	}
	return null;
};

GH.ProofGenerator.evaluatorUnion.prototype.action = function(sexp) {
	return new GH.action('undefinedUnion', []);
};

GH.ProofGenerator.evaluatorUnion.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorUnion.prototype.canAddTheorem = function (sexp) {
	return false;
};

GH.ProofGenerator.evaluatorUnion.prototype.inline = function (sexp) {
	sexp = sexp.copy();

	// First, combine and sort the two sets.
	var symbolList = [];
	var originalTree = this.createSymbolTree(sexp, symbolList);
	symbolList.sort(function(a, b) {
		return a[0] - b[0];
	});
	var sortedTree = this.createSortedTree(symbolList);
	sexp = this.prover.openExp(sexp, 'Place in numeric order');
	sexp = this.prover.repositioner.repositionTree(sexp, originalTree, sortedTree);
	sexp = this.prover.closeExp(sexp);
	
	// Second, remove duplicates.
	sexp = this.prover.openExp(sexp, 'Remove Duplicates');
	sexp = this.removeDuplicates(result);
	return this.prover.closeExp(sexp);
};

GH.ProofGenerator.evaluatorUnion.prototype.createSymbolTree = function(sexp, symbolList) {
	if (sexp.operator == 'u.') {
		var leftTree = this.createSymbolTree(sexp.left(), symbolList);
		var rightTree = this.createSymbolTree(sexp.right(), symbolList);
		return new GH.symbolTree(null, leftTree, rightTree);
	} else {
		var num = this.prover.calculate(sexp.child());
		var symbol = String.fromCharCode(65 + symbolList.length);
		symbolList.push([num, symbol]);
		return new GH.symbolTree(symbol, null, null);
	}
};

GH.ProofGenerator.evaluatorUnion.prototype.createSortedTree = function(sortedList) {
	if (sortedList.length > 1) {
		var lastItem = sortedList.pop();
		return new GH.symbolTree(
		    null,
			this.createSortedTree(sortedList),
			new GH.symbolTree(lastItem[1], null, null));
	} else {
		return new GH.symbolTree(sortedList[0][1], null, null);
	}
};

GH.ProofGenerator.evaluatorUnion.prototype.removeDuplicates = function(sexp) {
	while (sexp.operator == 'u.') {
		if (sexp.left().operator == 'u.') {
			if (this.prover.calculate(sexp.right().child()) == this.prover.calculate(sexp.left().right().child())) {
				sexp = this.prover.associateRight(sexp);
				sexp = this.prover.evaluate(sexp.right(), 'Union is Idempotent').parent;
			}
		} else {
			if (this.prover.calculate(sexp.left().child()) == this.prover.calculate(sexp.right().child())) {
				sexp = this.prover.evaluate(sexp, 'Union is Idempotent').parent;
			}
		}
		sexp = sexp.left();
	}
	return sexp;
};

GH.ProofGenerator.evaluatorUnion.prototype.calculate = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	var sortedSet = leftSet.concat(rightSet).sort();
	return GH.setUtil.removeArrayDuplicates(sortedSet);
};