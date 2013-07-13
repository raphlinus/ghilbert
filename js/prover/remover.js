GH.remover = function(prover) {
	this.prover = prover;
};

GH.remover.REMOVE_OPERATIONS = [
	[ '->', ['impRemove1', 'impRemove2'], ['impNotRemove1', 'impNotRemove2']],
	['<->', [ 'biRemove1',  'biRemove2'], [ 'biNotRemove1',  'biNotRemove2']],
	['\\/', [ 'orRemove1',  'orRemove2'], [ 'orNotRemove1',  'orNotRemove2']], 
	['/\\',	[ 'anRemove1',  'anRemove2'], [ 'anNotRemove1',  'anNotRemove2']]
];

// TODO: Use shorthand operations.
// These could be used to remove part of an expression with no parent. These could be used
// instead of the remove operations except the hypotheses are in the wrong order.
GH.remover.REMOVE_SHORTHAND_OPERATIONS = [
	[ '->', ['ax-mpRemove', null], [null, 'mtoRemove']],
	['<->', [ 'mpbiRemove', 'mpbirRemove'], [ 'mtbiRemove',  'mtbirRemove']]
];

GH.remover.prototype.remove = function(removee, isNegated, output) {
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
				var stepName = null;
				if (!isNegated) {
					stepName = shorthandOperations[i][1][operandIndex];
				} else {
					stepName = shorthandOperations[i][2][operandIndex];
				}
				if ((!stepName) || (!this.prover.symbolDefined(stepName))) {
					return false;
				}
				this.prover.makeString([], stepName, output);
				return true;
			}
		}
	}
	
	var removeOperations = GH.remover.REMOVE_OPERATIONS;
	for (var i = 0; i < removeOperations.length; i++) {
		if (operator == removeOperations[i][0]) {
			var mandHyps = [];
			var stepName = null;
			//if (parent.parent) {
			mandHyps.push(parent.operands[1 - operandIndex]);
			if (!isNegated) {
				stepName = removeOperations[i][1][operandIndex];
			} else {
				stepName = removeOperations[i][2][operandIndex];
			}
			if ((!stepName) || (!this.prover.symbolDefined(stepName))) {
				return false;
			}
			this.prover.makeString(mandHyps, stepName, output);
		}
	}

	// Recursively replace the entire replacee follow the expression up to the root.
	if (parent.parent) {
		return this.prover.replacer.replace(parent, '<->', output);
	} else {
		output.push('mpbi');
		return true;
	}
};

GH.remover.prototype.removeBoolean = function(removee, output) {
	var myMatch = GH.Prover.findMatch(removee, GH.sExpression.fromRaw('T'));	
	if (myMatch && myMatch.parent) {
		output.push('tru');
		this.remove(myMatch, false, output);
	}
	myMatch = GH.Prover.findMatch(removee, GH.sExpression.fromRaw('F'));	
	if (myMatch && myMatch.parent) {
		output.push('notfal');
		this.remove(myMatch, true, output);
	}
};

GH.remover.prototype.isApplicable = function(removee, remover) {
	return this.maybeRemove(removee, remover) != null;
};

GH.remover.prototype.maybeRemove = function(removee, remover) {
	var output = [];
	var isNegated = false;
	var myMatch = GH.Prover.findMatch(removee, remover);
	if (myMatch && myMatch.parent && (myMatch.parent.operator == '-.')) {
		output.push('notnoti');
		isNegated = true;
		myMatch = myMatch.parent;
	}
	if ((!myMatch) && (remover.operator == '-.')) {
		isNegated = true;
		myMatch = GH.Prover.findMatch(removee, remover.child());
	}

	if (!myMatch) {
		return null;
	} else {
		var success = this.remove(myMatch, isNegated, output);
		if (success) {
			return output;
		} else {
			return null;
		}
	}
};