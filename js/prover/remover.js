GH.remover = function(prover) {
	this.prover = prover;
};

GH.remover.REMOVE_OPERATIONS = [
	[ '->', ['impRemove1', 'impRemove2'], ['impNotRemove1', 'impNotRemove2']],
	['<->', [ 'biRemove1',  'biRemove2'], [ 'biNotRemove1',  'biNotRemove2']],
	['\\/', [ 'orRemove1',  'orRemove2'], [ 'orNotRemove1',  'orNotRemove2']], 
	['/\\',	[ 'anRemove1',  'anRemove2'], [ 'anNotRemove1',  'anNotRemove2']],
	[ 'A.', [        null,  'alRemove2'], [ null,            'alNotRemove2']],
	[ 'E.', [        null,  'exRemove2'], [ null,            'exNotRemove2']], 
	['{|}',	[        null,         null], [ null,            'abNotRemove2']],
];

// TODO: Use shorthand operations.
// These could be used to remove part of an expression with no parent. These could be used
// instead of the remove operations except the hypotheses are in the wrong order.
GH.remover.REMOVE_SHORTHAND_OPERATIONS = [
	[ '->', ['ax-mpRemove', null], [null, 'mtoRemove']],
	['<->', [ 'mpbiRemove', 'mpbirRemove'], [ 'mtbiRemove',  'mtbirRemove']]
];

GH.remover.prototype.remove = function(removee, isNegated) {
	var parent = removee.parent;
	var operandIndex = removee.siblingIndex;
	if (!parent) {
		// The remover and the removee are identical.
		return false;
	}
		
	var operator = parent.operator;
	
	var shorthandOperations = GH.remover.REMOVE_SHORTHAND_OPERATIONS;
	if (!parent.parent) {
		for (var i = 0; i < shorthandOperations.length; i++) {
			if (operator == shorthandOperations[i][0]) {
				var actionName = null;
				if (!isNegated) {
					actionName = shorthandOperations[i][1][operandIndex];
				} else {
					actionName = shorthandOperations[i][2][operandIndex];
				}
				if ((actionName) && (this.prover.symbolDefined(actionName))) {
					this.prover.print([], actionName);
					return true;
				}
			}
		}
	}
	
	var removeOperations = GH.remover.REMOVE_OPERATIONS;
	for (var i = 0; i < removeOperations.length; i++) {
		if (operator == removeOperations[i][0]) {
			var mandHyps = [];
			var actionName = null;
			mandHyps.push(parent.operands[1 - operandIndex]);
			if (!isNegated) {
				actionName = removeOperations[i][1][operandIndex];
			} else {
				actionName = removeOperations[i][2][operandIndex];
			}
			if ((!actionName) || (!this.prover.symbolDefined(actionName))) {
				return false;
			}
			this.prover.print(mandHyps, actionName);
		}
	}

	// Recursively replace the entire replacee follow the expression up to the root.
	if (parent.parent) {
		return this.prover.replacer.replace(parent, '<->');
	} else {
		this.prover.print([], 'mpbi');
		return true;
	}
};

GH.remover.prototype.removeBoolean = function(removee) {
	var myMatch = GH.Prover.findMatch(removee, GH.sExpression.fromRaw('T'));	
	if (myMatch && myMatch.parent) {
		this.prover.print([], 'tru');
		this.remove(myMatch, false);
	}
	myMatch = GH.Prover.findMatch(removee, GH.sExpression.fromRaw('F'));	
	if (myMatch && myMatch.parent) {
		this.prover.print([], 'notfal');
		this.remove(myMatch, true);
	}
};

GH.remover.prototype.isApplicable = function(removee, remover) {
	return this.maybeRemove(removee, remover, false);
};

GH.remover.prototype.maybeRemove = function(removee, remover, doRemove) {
	var output = [];
	var isNegated = false;
	var myMatch = GH.Prover.findMatch(removee, remover);
	if (myMatch && myMatch.parent && (myMatch.parent.operator == '-.')) {
		this.prover.print([], 'notnoti');
		isNegated = true;
		myMatch = myMatch.parent;
	}
	if ((!myMatch) && (remover.operator == '-.')) {
		isNegated = true;
		myMatch = GH.Prover.findMatch(removee, remover.child());
	}

	if (!myMatch) {
		return false;
	} else {
		var traversable = this.prover.replacer.isApplicableTraverse(myMatch, '<->');
		if (!traversable) {
			return false;
		} else {
			if (doRemove) {
				this.remove(myMatch, isNegated);
			}
			return true;
		}
	}
};