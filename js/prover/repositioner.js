GH.repositioner = function(prover) {
	this.prover = prover;
};

// Repositions the terms in an s-expression. Uses commutation and association rules to 
// change the s-expression between any two positions. Assumes that s-expression has operators
// that commute and associate. oldPosition and newPosition are strings that are converted into
// symbol trees. 
GH.repositioner.prototype.reposition = function(sexp, oldPosition, newPosition) {
	var oldTree = GH.symbolTree.fromString(oldPosition);
	var newTree = GH.symbolTree.fromString(newPosition);
	return this.repositionTree(sexp, oldTree, newTree);
};

// Takes an s-expression and a symbol tree and continues to run the associateRight function
// wherever it is possible for both the symbol tree and the s-expression.
GH.repositioner.prototype.associateAllRight = function(expTree) {
	var sexp = expTree.sexp;
	var tree = expTree.tree;
	if (tree.left && tree.left.left) {
		var result = this.prover.associateRight(sexp);
		tree.associateRight();
		return this.associateAllRight({sexp: result, tree: tree});
	} else if (tree.right) {
		var result = this.associateAllRight({sexp: sexp.right(), tree: tree.right});
		return {sexp: result.sexp.parent, tree: tree};
	} else {
		return expTree;
	}
};

// Takes an s-expression and a symbol tree and continues to run the associateLeft function
// wherever it is possible for both the symbol tree and the s-expression.
GH.repositioner.prototype.associateAllLeft = function(expTree) {
	var sexp = expTree.sexp;
	var tree = expTree.tree;
	var result;
	if (tree.right && tree.right.right) {
		result = this.prover.associateLeft(sexp);
		tree.associateLeft();
		result = this.associateAllLeft({sexp: result, tree: tree});
	} else if (tree.left) {
		var result = this.associateAllLeft({sexp: sexp.left(), tree: tree.left});
		result = {sexp: result.sexp.parent, tree: tree};
	} else {
		result = expTree;
	}
	return result;
};

// Repositions the terms in an s-expression. Uses commutation and association rules to 
// change the s-expression between two symbol trees. Assumes that s-expression has operators
// that commute and associate.

// First, associate all left, then reorder all the terms, and then use association rules to
// get into the new tree position.
GH.repositioner.prototype.repositionTree = function(sexp, oldTree, newTree) {
	// TODO: Optimize by not modifying left or right if they were not changed.
	sexp = this.prover.openExp(sexp, 'Rearrange Terms');
	sexp = this.prover.openExp(sexp, 'Associate All Left');
	var leftAssociated = this.associateAllLeft({sexp: sexp, tree: oldTree});
	leftAssociated.sexp = this.prover.closeExp(leftAssociated.sexp);

	leftAssociated.sexp = this.prover.openExp(leftAssociated.sexp, 'Reorder Terms');
	var symbolOrder = GH.symbolTree.getSymbolOrder(oldTree.getSymbolList(), newTree.getSymbolList());
	var reordered = this.reorder(leftAssociated.sexp, symbolOrder);
	reordered.sexp = this.prover.closeExp(reordered.sexp);
	
	// leftAssociated.tree was set before the reordering, so it is not a perfect representation
	// of the state of the left, but for the reassociation step the order is irrelevant.
	reordered.sexp = this.prover.openExp(reordered.sexp, 'Change Associations');
	var result = this.reassociate(reordered, leftAssociated.tree, newTree);
	result = this.prover.closeExp(result);
	result = this.prover.closeExp(result);
	return result;
};
	
// Uses a bubble sort.
GH.repositioner.prototype.reorder = function(sexp, order) {
	var inorder = false;
	var result = sexp;
	while (!inorder) {
		inorder = true;
		for (var i = 0; i < order.length - 1; i++) {
			if (order[i] > order[i + 1]) {
				var temp = order[i];
				order[i] = order[i + 1];
				order[i + 1] = temp;
				inorder = false;
					
				result = this.bubble(result, i, order.length);
			}
		}
	}
	return result;
};

// Swaps the order of two expressions, given the position of the
// expression to swap. The most basic operation in a bubble sort. 
GH.repositioner.prototype.bubble = function(sexp, position, listLength) {
	var leftness = listLength - position - 2;
	for (var i = 0; i < leftness; i++) {
		sexp = sexp.left();
	}
	if (position == 0) {
		sexp = this.prover.commute(sexp);
	} else {
		sexp = this.prover.associateRight(sexp);
		sexp = this.prover.applyRight(this.prover.commute, sexp);
		sexp = this.prover.associateLeft(sexp);
	}
	for (var i = 0; i < leftness; i++) {
		sexp = sexp.parent;
	}
	return sexp;
};

// Given an s-expression an a symbol tree representing the old order of
// operations and a symbol tree representing the new order of operations
// switches the order of operations until the tree have the same structure.
// The order of the operands does not change.
GH.repositioner.prototype.reassociate = function(sexp, oldTree, newTree) {
	if (!oldTree.left) {
		return sexp;
	}
	
	var oldLeftness = oldTree.left.getSymbolList().length;
	var newLeftness = newTree.left.getSymbolList().length;
	while (oldLeftness < newLeftness) {
		sexp = this.prover.associateLeft(sexp);
		oldTree.associateLeft();
		oldLeftness = oldTree.left.getSymbolList().length;
	}
	while (oldLeftness > newLeftness) {
		sexp = this.prover.associateRight(sexp);
		oldTree.associateRight();
		oldLeftness = oldTree.left.getSymbolList().length;
	}
	if (oldLeftness != newLeftness) {
		alert('Reassociation failed.');
	}
	var result = sexp;
	result = this.reassociate(result.left(),  oldTree.left,  newTree.left);
	result = result.parent;
	result = this.reassociate(result.right(), oldTree.right, newTree.right);
	result = result.parent;
	
	return result;
};