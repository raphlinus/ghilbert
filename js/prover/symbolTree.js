/** 
 * A tree with each node having a string representing some symbol. This is used
 * to specify how to rearrange the terms in GH.Prover.reposition. The symbol 
 * tree is constructed by parsing a string with symbols interpersed with parentheses.
 */
GH.symbolTree = function(symbol, left, right) {
	this.symbol = symbol;
	this.left = left;
	this.right = right;
};

// Generates a symbol tree from an expression like '(A (B C)) D'.
GH.symbolTree.fromString = function(str) {
	var depth = 0;
	str = GH.symbolTree.removeParentheses(str);
	var leftStart = null;
	var leftEnd = null;
	var rightStart = null;
	var rightEnd = null;
	
	for (var i = 0; i < str.length; i++) {
		var c = str.charAt(i);
		if (c != ' ') {
			if (leftStart == null) {
				leftStart = i;
			}
			if ((rightStart == null) && (leftEnd != null)) {
				rightStart = i;
			}		
			if (rightStart != null) {
				rightEnd = i + 1;
			}
		}

		if (c == '(') {
			depth++;
		} else if (c == ')') {
			depth--;
		} else if (c == ' ') {
			if ((depth == 0) && (leftStart != null)) {
				leftEnd = i;
			}
		}
	}
	if (rightStart == null) {
		return new GH.symbolTree(str, null, null);
	} else {
		var leftTree  = GH.symbolTree.fromString(str.substring(leftStart,  leftEnd));
		var rightTree = GH.symbolTree.fromString(str.substring(rightStart, rightEnd));
		return new GH.symbolTree(null, leftTree, rightTree);
	}
};

// Returns what is inside the first and last parentheses, remove everything else
// including the parentheses.
GH.symbolTree.removeParentheses = function(str) {
	var i = 0;
	var depth = 0;
	while (str.charAt(i) == ' ') {
		i++;
	}

	// If there are symbols before the first parentheses, return the original string.
	if (str.charAt(i) != '(') {
		return str;
	}
	var start = i + 1;
	var end = null;
	for (; i < str.length; i++) {
		var c = str.charAt(i);
		if (c == '(') {
			depth++;
		} else if (c == ')') {
			depth--;
			if (depth == 0) {
				end = i;
			}
		} else if ((end != null) && (c != ' ')) {
			// If there are symbols after the last parentheses, return the original string.
			return str;
		}
	}
	return str.substring(start, end);
};


// Associates a symbol tree to the right. Input: (A B) C, Output: A (B C)
// Similiar to GH.Prover.associateRight, but that applies to s-expressions.
GH.symbolTree.prototype.associateRight = function() {
	var a = this.left.left;
	var b = this.left.right;
	var c = this.right;

	this.left = a;
	this.right = new GH.symbolTree(null, b, c);
};

// Associates a symbol tree to the left. Input: A (B C), Output: (A B) C
// Similiar to GH.Prover.associateLeft, but that applies to s-expressions.
GH.symbolTree.prototype.associateLeft = function() {
	var a = this.left;
	var b = this.right.left;
	var c = this.right.right;

	this.left = new GH.symbolTree(null, a, b)
	this.right = c;
};

// Output the tree as an array of symbols.
GH.symbolTree.prototype.getSymbolList = function() {
	if (this.symbol != null) {
		return [this.symbol];
	} else {
		return this.left.getSymbolList().concat(this.right.getSymbolList());
	}
}

// For two list returns an array specifying how to reorder the terms in the
// first list to equal the second list.
GH.symbolTree.getSymbolOrder = function(oldList, newList) {
	if (oldList.length != newList.length) {
		alert('The two symbol list do not have the same number of symbols.');
	}
	var order = [];
	for (var i = 0; i < oldList.length; i++) {
		var matches = 0;
		for (var j = 0; j < newList.length; j++) {
			if (oldList[i] == newList[j]) {
				matches++;
				order.push(j);
			}
		}
		if (matches != 1) {
			alert('Mismatch in the symbol lists.');
		}
	}
	return order;
};