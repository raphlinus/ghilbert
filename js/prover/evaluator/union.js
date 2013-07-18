GH.ProofGenerator.evaluatorUnion = function(prover) {
  this.prover = prover;
  this.operators = ['u.'];
};

GH.ProofGenerator.evaluatorUnion.prototype.stepName = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	if (rightSet.length == 0) {
		return 'unid';
	} else if (leftSet.length == 0) {
		return 'unidr';
	} else if (GH.ProofGenerator.evaluatorUnion.equalSets(leftSet, rightSet)) {
		return 'unidm';
	}
};

GH.ProofGenerator.evaluatorUnion.prototype.hyps = function(sexp) {
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	if (rightSet.length == 0) {
		return [sexp.left()];
	} else if (leftSet.length == 0) {
		return [sexp.right()];
	} else if (GH.ProofGenerator.evaluatorUnion.equalSets(leftSet, rightSet)) {
		return [sexp.left()];
	}
	return [];
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
	var result = this.prover.repositioner.repositionTree(sexp, originalTree, sortedTree);
	
	// Second, remove duplicates.
	this.removeDuplicates(result);
	return true;
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
		var firstItem = sortedList.shift();
		return new GH.symbolTree(
		    null,
			new GH.symbolTree(firstItem[1], null, null),
			this.createSortedTree(sortedList));
	} else {
		return new GH.symbolTree(sortedList[0][1], null, null);
	}
};

GH.ProofGenerator.evaluatorUnion.prototype.removeDuplicates = function(sexp) {
	while (sexp.operator == 'u.') {
		if (sexp.right().operator == 'u.') {
			if (this.prover.calculate(sexp.left().child()) == this.prover.calculate(sexp.right().left().child())) {
				sexp = this.prover.associateLeft(sexp);
				sexp = this.prover.evaluate(sexp.left()).parent;
			}
		} else {
			if (this.prover.calculate(sexp.left().child()) == this.prover.calculate(sexp.right().child())) {
				sexp = this.prover.evaluate(sexp).parent;
			}
		}
		sexp = sexp.right();
	}
	return sexp;
};

GH.ProofGenerator.evaluatorUnion.prototype.calculate = function(sexp) {
	// TODO: Sort during the concatenation.
	var leftSet = this.prover.calculate(sexp.left());
	var rightSet = this.prover.calculate(sexp.right());
	var sortedSet = leftSet.concat(rightSet).sort();
	return GH.ProofGenerator.evaluatorUnion.removeArrayDuplicates(sortedSet);
};

GH.ProofGenerator.evaluatorUnion.removeArrayDuplicates = function(inputArray) {
	var outputArray = [];
	for (var  i = 0; i < inputArray.length; i++) {
		if ((i == 0) || (inputArray[i] != inputArray[i - 1])) {
			outputArray.push(inputArray[i]);
		}
	}
	return outputArray;
};

// TODO: Maybe calculate this using evaluatorSetEquality.
GH.ProofGenerator.evaluatorUnion.equalSets = function(leftSet, rightSet) {
	if (leftSet.length != rightSet.length) {
		return false;
	}
	for (var i = 0; i < leftSet.length; i++) {
		if (leftSet[i] != rightSet[i]) {
			return false;
		}
	}
	return true;
};