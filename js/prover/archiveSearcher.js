GH.archiveSearcher = function(prover) {
	this.prover = prover;
	this.archive = null;
	this.suggestThms = [];
	for (var i = 0; i < GH.archiveSearcher.SUGGESTION_TYPES.LENGTH; i++) {
		this.suggestThms[i] = null;
	}
};

GH.archiveSearcher.SUGGESTION_TYPES = {
	TRUTH: 0,
	CONTRADICTION: 1,
	REPLACEMENT: 2,
	LENGTH: 3,
};

GH.archiveSearcher.prototype.createArchive = function(syms) {
	if (!this.archive) {
		this.archive = {};
		for (var sym in syms) {
			if ((syms.hasOwnProperty(sym)) && syms[sym][6] && (syms[sym][6].suggest)) {
				var conclusion = GH.sExpression.fromRaw(syms[sym][3]);
				var vars = [];
				var symVars = syms[sym][4];
				for (var i = 0; i < symVars.length; i++) {
					vars.push(symVars[i][2]);
				}

				var suggest = syms[sym][6].suggest;
				for (var i = 0; i < suggest.length; i++) {
					var suggestCommand = suggest[i][0];
					var archiveBranch;
					var sexp;
					var newSuggestion;
					var replaceOp = conclusion.operator;
					if (suggestCommand == 'full') {
						archiveBranch = ['full', 'full'];
						sexp = conclusion;
					} else if (suggestCommand == 'right') {
						archiveBranch = ['replace', replaceOp];
						sexp = conclusion.left();
					} else if (suggestCommand == 'left') {
						archiveBranch = ['replace', replaceOp];
						sexp = conclusion.right();
					} else if (suggestCommand == 'auto-right') {
						sexp = conclusion.left();
						newSuggestion = new GH.archiveSuggestion(sym, suggest[i], syms[sym][6].title, syms[sym][1], symVars, sexp, []);
						this.addToArchive(newSuggestion, ['auto-replace', replaceOp], sexp, vars);
						archiveBranch = ['replace', replaceOp];
					} else if (suggestCommand == 'auto-left') {
						sexp = conclusion.right();
						newSuggestion = new GH.archiveSuggestion(sym, suggest[i], syms[sym][6].title, syms[sym][1], symVars, sexp, []);
						this.addToArchive(newSuggestion, ['auto-replace', replaceOp], sexp, vars);
						archiveBranch = ['replace', replaceOp];
					}
					var newSuggestion = new GH.archiveSuggestion(sym, suggest[i], syms[sym][6].title, syms[sym][1], symVars, sexp, []);
					this.addToArchive(newSuggestion, archiveBranch, sexp, vars);
				}
			}
		}
	}
};

GH.archiveSearcher.prototype.addToArchive = function(newSuggestion, archiveBranch, sexp, vars) {
	var hyps = newSuggestion.hyps;
	// A breadth-first traversal of the s-expression.
	var breadthFirst = [];
	var queue = [sexp]; 
	while (queue.length > 0) {
		var node = queue.shift();
		var index = vars.indexOf(node.operator);
		if (index >= 0) {
			breadthFirst.push('tvar');
			hyps.push(index);
		} else {
			breadthFirst.push(node.operator);
		}
		for (var i = 0; i < node.operands.length; i++) {
			queue.push(node.operands[i]);
		}
	}

	var archiveNode = this.archive;
	for (var i = 0; i < archiveBranch.length; i++) {
		if (!archiveNode.hasOwnProperty(archiveBranch[i])) {
			archiveNode[archiveBranch[i]] = {};
		}
		archiveNode = archiveNode[archiveBranch[i]];
	}
	
	for (var i = 0; i < breadthFirst.length; i++) {
		var operator = breadthFirst[i];
		if (!archiveNode.hasOwnProperty(operator)) {
			archiveNode[operator] = {};
		}
		archiveNode = archiveNode[operator];
	}	
	if (!archiveNode.hasOwnProperty('thms')) {
		archiveNode['thms'] = [];
	}
	archiveNode['thms'].push(newSuggestion);
};

// Returns an archive suggestion with the variables filled in from hyps.
// Puts the variables in the right order and removes duplicate matches.
GH.archiveSearcher.fillHypotheses = function(suggestion, hyps) {
	var newHyps = [];
	var newFreeness = [];
	for (var i = 0; i < suggestion.freeness.length; i++) {
		newFreeness.push(['', '']);
	}

	// Put in default values. Hyps may not have all of them if you're replacing an expression and
	// new variables appear on the right.
	var variables = suggestion.variables;
	for (var i = 0; i < variables.length; i++) {
		var type = variables[i][1];
		var defaultVar = null;
		if (type == 'wff') {
			defaultVar = 'ph';
		} else if (type == 'nat') {
			defaultVar = 'x';
		} else if (type == 'set') {
			defaultVar = 'S';
		}
		newHyps.push(GH.sExpression.createVariable(defaultVar));
	}
	for (var i = 0; i < hyps.length; i++) {
		newHyps[suggestion.hyps[i]] = hyps[i];
	}
	
	for (var i = 0; i < newHyps.length; i++) {
		for (var j = 0; j < suggestion.freeness.length; j++) {
			for (var k = 0; k < 2; k++) {
				if (suggestion.freeness[j][k].valueOf() == variables[i][2]) {
					newFreeness[j][k] = newHyps[i];
				}
			}
		}
	}
	var result = suggestion.copy();
	result.hyps = newHyps;
	result.freeness = newFreeness;
	return result;
};

// Check that variables that should be identical are identical.
GH.archiveSearcher.checkVariableMatches = function(theorems, hyps) {
	var matchingList = [];
	for (var k = 0; k < theorems.length; k++) {
		var theoremHyps = theorems[k].hyps;
		var match = true;
		for (var i = 0; i < hyps.length; i++) {
			for (var j = i + 1; j < hyps.length; j++) {
				if ((theoremHyps[i] == theoremHyps[j]) && !hyps[i].equals(hyps[j])) {
					match = false;
				}
			}
		}
		if (match) {
			matchingList.push(GH.archiveSearcher.fillHypotheses(theorems[k], hyps));
		}
	}
	return matchingList;
};


GH.archiveSearcher.checkFreenessConstraints = function(theorems, hyps) {
	var freeList = [];
	for (var k = 0; k < theorems.length; k++) {
		var thm = theorems[k];
		var violations = false;
		for (var i = 0; i < thm.freeness.length && !violations; i++) {
			if (thm.freeness[i][1]) {
				if (thm.freeness[i][1].operator == null) {
					// I'm not sure why this is happening, but it is for df-le in natural_specific.gh
					violations = true;
				} else {
					var bindVar = thm.freeness[i][1].operator.valueOf();
					// This finds serious freeness violations that can not be corrected by adding a freeness
					// constraint. Other freeness violations can be corrected automatically.
					violations = violations || (thm.freeness[i][0].isVariablePresent(bindVar));
				}
			}
		}
		if (!violations) {
			freeList.push(thm);
		}
	}
	return freeList;
};

GH.archiveSearcher.filterByAction = function(theorems, categoryName, actionName) {
	if (!categoryName) {
		return theorems;
	}
	var filteredThms = [];
	for (var i = 0; i < theorems.length; i++) {
		if ((theorems[i].categoryName == categoryName) &&
		    (!actionName || (theorems[i].actionName == actionName))) {
			filteredThms.push(theorems[i]);
		}
	}
	return filteredThms;
};

GH.archiveSearcher.search = function(queue, archive, hyps, categoryName, actionName) {
	while (queue.length > 0) {
		var node = queue.shift();
		var keys = [];
		if (archive.hasOwnProperty('tvar')) {
			keys.push('tvar');
		}
		var operator = node.operator;
		// if (((node.operands.length > 0) || GH.Prover.variableGenerator.isVariable(operator)) &&
		//    (archive.hasOwnProperty(operator))) {

		if (archive.hasOwnProperty(operator)) {
			keys.push(operator);
		}
		if (keys.length == 0) {
			return [];
		}

		var newArchives = [];
		var newQueues = [];
		var newHyps = [];
		for (var i = 0; i < keys.length; i++) {
			newArchives.push(archive[keys[i]]);
			var newQueue = queue.slice(0);
			var newHyp = hyps.slice(0);
			if (keys[i] != 'tvar') {
				for (var j = 0; j < node.operands.length; j++) {
					newQueue.push(node.operands[j]);
				}
			} else {
				newHyp.push(node);
			}
			newQueues.push(newQueue);
			newHyps.push(newHyp);
		}
		if (keys.length == 2) {
			return GH.archiveSearcher.search(newQueues[0], newArchives[0], newHyps[0], categoryName, actionName).concat(
 			       GH.archiveSearcher.search(newQueues[1], newArchives[1], newHyps[1], categoryName, actionName));
		} else {
			queue = newQueues[0];
			archive = newArchives[0];
			hyps = newHyps[0];
		}
	}
	var theorems = archive['thms'];
	theorems = GH.archiveSearcher.filterByAction(theorems, categoryName, actionName);
	theorems = GH.archiveSearcher.checkVariableMatches(theorems, hyps);
	theorems = GH.archiveSearcher.checkFreenessConstraints(theorems, hyps);
	return theorems;
};

GH.archiveSearcher.prototype.contradictionSearch = function(sexp) {
	if (!this.archive.hasOwnProperty('full') || !this.archive['full']['full'].hasOwnProperty('-.')) {
		return [];
	}
	return GH.archiveSearcher.search([sexp], this.archive['full']['full']['-.'], [], '', '');
};

GH.archiveSearcher.prototype.truthSearch = function(sexp) {
	if (!this.archive.hasOwnProperty('full')) {
		return [];
	}
	return GH.archiveSearcher.search([sexp], this.archive['full']['full'], [], '', '');
};

// TODO: Don't suggest things that do nothing like commutting A + A.
GH.archiveSearcher.prototype.replacementSearch = function(sexp, branch, categoryName, actionName) {
	if (!this.archive.hasOwnProperty(branch)) {
		return [];
	}
	var archiveNode = this.archive[branch];
	var result = [];
	for(key in archiveNode){
		// var replacementTester = this.getReplacementTester(key);
		if (!sexp.parent || (this.prover.replacer.isApplicableTraverse(sexp, key))) {  // This won't work for negated operators like >.
			result = result.concat(GH.archiveSearcher.search([sexp], archiveNode[key], [], categoryName, actionName));
		}
	}
	return result;
};

GH.archiveSearcher.prototype.applyAction = function(sexp, categoryName, actionName) {
	var theorems = [];
	if (this.archive.hasOwnProperty('full') && this.archive['full'].hasOwnProperty('-.')) {
		theorems = theorems.concat(GH.archiveSearcher.search([sexp], this.archive['full']['-.'], [], categoryName, actionName));
	}
	if (this.archive.hasOwnProperty('replace')) {
		theorems = theorems.concat(this.replacementSearch(sexp, 'replace', categoryName, actionName));
	}
	if (theorems.length > 1) {
		alert(theorems.length + ' theorems found for action ' + categoryName + ' ' + actionName + '.');
		return null;
	}
	if (theorems.length == 0) {
		return sexp;
	}

	var suggestion = theorems[0];
	this.prover.print(suggestion.hyps, suggestion.name);
	if ((suggestion.type == 'left') || (suggestion.type == 'auto-left')) {
		this.prover.commute(this.prover.getLast());
	}
	return this.prover.getLast();
};

GH.archiveSearcher.prototype.applyContradiction = function(sexp, suggestionIndex) {
	var suggestion = this.suggestThms[GH.archiveSearcher.SUGGESTION_TYPES.CONTRADICTION][suggestionIndex];
	this.prover.print(suggestion.hyps, suggestion.name);
	return this.prover.remove();
};

GH.archiveSearcher.prototype.applyTruth= function(sexp, suggestionIndex) {
	var suggestion = this.suggestThms[GH.archiveSearcher.SUGGESTION_TYPES.TRUTH][suggestionIndex];
	this.prover.print(suggestion.hyps, suggestion.name);
	return this.prover.remove();
};

GH.archiveSearcher.prototype.applyTheorem = function(sexp, suggestion) {
	suggestion.addMissingVariables();
	this.prover.print(suggestion.hyps, suggestion.name);
	if ((suggestion.type == 'left') || (suggestion.type == 'auto-left')) {
		this.prover.commute(this.prover.getLast());
	}
	if ((GH.operatorUtil.getType(sexp) != 'wff') || sexp.isProven || (sexp.parent)) {
		return this.prover.replace(sexp);
	} else {
		return this.prover.getLast().right();
	}
};

GH.archiveSearcher.prototype.applyReplacement = function(sexp, suggestionIndex) {
	var suggestion = this.suggestThms[GH.archiveSearcher.SUGGESTION_TYPES.REPLACEMENT][suggestionIndex];
	return this.applyTheorem(sexp, suggestion);
};

GH.archiveSearcher.prototype.autoApply = function(sexp) {
	var replacements = this.replacementSearch(sexp, 'auto-replace', '', '');
	while (replacements.length > 0) {
		sexp = this.applyTheorem(sexp, replacements[0]);
		replacements = this.replacementSearch(sexp, 'auto-replace', '', '');
	}
	for (var i = 0; i < sexp.operands.length; i++) {
		sexp = this.autoApply(sexp.operands[i]).parent;
	}
	return sexp;
};

/*GH.archiveSearcher.prototype.autoApply = function(sexp) {
	var siblingIndex = -1;
	if (sexp.parent) {
		siblingIndex = sexp.siblingIndex;
		sexp = sexp.parent;
	}

	var replacements = this.replacementSearch(sexp, 'auto-replace', '', '');
	if (replacements.length == 0) {
		siblingIndex = -1;
	}
	sexp = this.autoApply(sexp);
	if (siblingIndex >= 0) {
		sexp = sexp.operands[siblingIndex];
	}
	return sexp;
};*/

GH.archiveSearcher.prototype.getSuggestionTitle = function(suggestionType, suggestionIndex) { 
	return this.suggestThms[GH.archiveSearcher.SUGGESTION_TYPES.REPLACEMENT][suggestionIndex].title;
};

GH.archiveSearcher.prototype.applySuggestion = function(sexp, suggestionType, suggestionIndex) {
	var TYPES = GH.archiveSearcher.SUGGESTION_TYPES;
	var result;
	if (suggestionType == TYPES.CONTRADICTION) {
		result = this.applyContradiction(sexp, suggestionIndex);
	} else if (suggestionType == TYPES.TRUTH) {
		result = this.applyTruth(sexp, suggestionIndex);
	} else if (suggestionType == TYPES.REPLACEMENT) {
		result = this.applyReplacement(sexp, suggestionIndex);
	}

	return this.autoApply(result);
};

GH.archiveSearcher.prototype.addSuggestionType = function(type, suggestions) {
	this.suggestThms[type] = [];
	for (var i = 0; i < suggestions.length; i++) {
		this.suggestThms[type].push(suggestions[i]);
		var clickHandler = 'window.direct.prover.handleArchive(' + type + ', ' + i + ')';
		if (suggestions[i].actionName) {
			this.prover.buttonController.addCategorizedButton(suggestions[i].categoryName, suggestions[i].actionName, clickHandler, true);
		}
	}
};

GH.archiveSearcher.prototype.addSuggestions = function(sexp) {
	if (!sexp) {
		return;
	}

	var TYPES = GH.archiveSearcher.SUGGESTION_TYPES;
	this.suggestions = [];
	
	var type;
	var contradictions = this.contradictionSearch(sexp);
	if (contradictions.length > 0) {
		this.addSuggestionType(TYPES.CONTRADICTION, [contradictions[0]]);
	}

	var truths = this.truthSearch(sexp);
	if (truths.length > 0) {
		this.addSuggestionType(TYPES.TRUTH, [truths[0]]);
	}

	var replacements = this.replacementSearch(sexp, 'replace', '', '');
	type = TYPES.REPLACEMENT;
	this.addSuggestionType(TYPES.REPLACEMENT, replacements);
};

GH.archiveSuggestion = function(name, suggest, title, freeness, variables, theorem, hyps) {
	this.name = name;					// The name of the theorem in Ghilbert code.
	this.type = suggest[0];				// Full theorem, replace left, or replace right.
	this.categoryName = suggest[1];		// The category of suggestion.
	this.actionName = suggest.length < 3 ? null : suggest[2];		// The name appearing on the suggest button.
	this.title = title;					// The title that is displayed to the right of each step.
	this.freeness = freeness;			// The free variable constraints.
	this.theorem = theorem;
	this.variables = variables;			// The variables the theorem needs.
	this.hyps = hyps;					// These are the filled in variables from the current s-expression. Should probably rename this.
};

GH.archiveSuggestion.prototype.copy = function() {
	return new GH.archiveSuggestion(this.name, [this.type, this.categoryName, this.actionName], this.title, this.freeness, this.theorem, this.hyps);
};

GH.archiveSuggestion.prototype.addMissingVariables = function() {
};