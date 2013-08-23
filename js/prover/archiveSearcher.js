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
					if (suggestCommand == 'full') {
						archiveBranch = 'full';
						sexp = conclusion;
					} else if (suggestCommand == 'right') {
						archiveBranch = 'replace';
						sexp = conclusion.left();
					} else if (suggestCommand == 'left') {
						archiveBranch = 'replace';
						sexp = conclusion.right();
					} else if (suggestCommand == 'auto-right') {
						sexp = conclusion.left();
						this.addToArchive(sym, suggest[i], 'auto-replace', sexp, vars);
						archiveBranch = 'replace';
					} else if (suggestCommand == 'auto-left') {
						sexp = conclusion.right();
						this.addToArchive(sym, suggest[i], 'auto-replace', sexp, vars);
						archiveBranch = 'replace';
					}
					this.addToArchive(sym, suggest[i], archiveBranch, sexp, vars);
				}
			}
		}
	}
};

GH.archiveSearcher.prototype.addToArchive = function(name, suggest, archiveBranch, sexp, vars) {
	var hyps = [];
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

	if (!this.archive.hasOwnProperty(archiveBranch)) {
		this.archive[archiveBranch] = {};
	}
	var archiveNode = this.archive[archiveBranch];
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
	archiveNode['thms'].push(new GH.archiveSuggestion(name, suggest, sexp, hyps));
};

// Returns an archive suggestion with the hypotheses filled in from the hypotheses.
// Puts the hypotheses in the right order and removes duplicate matches.
GH.archiveSearcher.fillHypotheses = function(suggestion, hyps) {
	var newHyps = [];
	for (var i = 0; i < hyps.length; i++) {
		newHyps[suggestion.hyps[i]] = hyps[i];
	}
	var result = suggestion.copy();
	result.hyps = newHyps;
	return result;
};

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

GH.archiveSearcher.filterByAction = function(theorems, actionName) {
	if (!actionName) {
		return theorems;
	}
	var filteredThms = [];
	for (var i = 0; i < theorems.length; i++) {
		if (theorems[i].actionName == actionName) {
			filteredThms.push(theorems[i]);
		}
	}
	return filteredThms;
};

GH.archiveSearcher.search = function(queue, archive, hyps, actionName) {
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
			return GH.archiveSearcher.search(newQueues[0], newArchives[0], newHyps[0], actionName).concat(
 			       GH.archiveSearcher.search(newQueues[1], newArchives[1], newHyps[1], actionName));
		} else {
			queue = newQueues[0];
			archive = newArchives[0];
			hyps = newHyps[0];
		}
	}
	var theorems = archive['thms'];
	theorems = GH.archiveSearcher.filterByAction(theorems, actionName);
	return GH.archiveSearcher.checkVariableMatches(theorems, hyps);
};

GH.archiveSearcher.prototype.contradictionSearch = function(sexp) {
	if (!this.archive.hasOwnProperty('full') || !this.archive['full'].hasOwnProperty('-.')) {
		return [];
	}
	return GH.archiveSearcher.search([sexp], this.archive['full']['-.'], [], '');
};

GH.archiveSearcher.prototype.truthSearch = function(sexp) {
	if (!this.archive.hasOwnProperty('full')) {
		return [];
	}
	return GH.archiveSearcher.search([sexp], this.archive['full'], [], '');
};

// TODO: Don't suggest things that do nothing like commutting A + A.
GH.archiveSearcher.prototype.replacementSearch = function(sexp) {
	if (!this.archive.hasOwnProperty('replace')) {
		return [];
	}
	return GH.archiveSearcher.search([sexp], this.archive['replace'], [], '');
};

GH.archiveSearcher.prototype.autoReplacementSearch = function(sexp) {
	if (!this.archive.hasOwnProperty('auto-replace')) {
		return [];
	}
	return GH.archiveSearcher.search([sexp], this.archive['auto-replace'], [], '');
};

GH.archiveSearcher.prototype.applyAction = function(sexp, actionName) {
	var theorems = [];
	if (this.archive.hasOwnProperty('full') && this.archive['full'].hasOwnProperty('-.')) {
		theorems = theorems.concat(GH.archiveSearcher.search([sexp], this.archive['full']['-.'], [], actionName));
	}
	if (this.archive.hasOwnProperty('replace')) {
		theorems = theorems.concat(GH.archiveSearcher.search([sexp], this.archive['replace'], [], actionName));
	}
	if (theorems.length > 1) {
		alert(theorems.length + ' theorems found for action ' + actionName + '.');
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

GH.archiveSearcher.prototype.autoApplyRecursive = function(sexp) {
	var replacements = this.autoReplacementSearch(sexp);
	while (replacements.length > 0) {
		sexp = this.applyTheorem(sexp, replacements[0]);
		replacements = this.autoReplacementSearch(sexp);
	}
	for (var i = 0; i < sexp.operands.length; i++) {
		sexp = this.autoApplyRecursive(sexp.operands[i]).parent;
	}
	return sexp;
};

GH.archiveSearcher.prototype.autoApply = function(sexp) {
	var siblingIndex = -1;
	if (sexp.parent) {
		siblingIndex = sexp.siblingIndex;
		sexp = sexp.parent;
	}

	var replacements = this.autoReplacementSearch(sexp);
	if (replacements.length == 0) {
		siblingIndex = -1;
	}
	sexp = this.autoApplyRecursive(sexp);
	if (siblingIndex >= 0) {
		sexp = sexp.operands[siblingIndex];
	}
	return sexp;
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

	// Auto apply on parent.
	return this.autoApply(result);
};

GH.archiveSearcher.prototype.addSuggestionType = function(type, suggestions) {
	this.suggestThms[type] = [];
	for (var i = 0; i < suggestions.length; i++) {
		this.suggestThms[type].push(suggestions[i]);
		var clickHandler = 'window.direct.prover.handleArchive(' + type + ', ' + i + ')';
		this.prover.addSuggestion(suggestions[i].actionName, clickHandler, true);
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

	var replacements = this.replacementSearch(sexp);
	type = TYPES.REPLACEMENT;
	this.addSuggestionType(TYPES.REPLACEMENT, replacements);
};

GH.archiveSuggestion = function(name, suggest, theorem, hyps) {
	this.name = name;					// The name of the theorem in Ghilbert code.
	this.actionName = suggest[1];		// The name appearing on the suggest button.
	this.type = suggest[0];				// Full theorem, replace left, or replace right.
	this.theorem = theorem;
	this.hyps = hyps;
};

GH.archiveSuggestion.prototype.copy = function() {
	return new GH.archiveSuggestion(this.name, [this.type, this.actionName], this.theorem, this.hyps);
};