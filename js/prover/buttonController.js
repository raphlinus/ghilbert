GH.ButtonController = function(suggestArea) {
	this.primaryArea = document.createElement('div');
	this.secondaryArea = document.createElement('div');
	this.primaryButtons = document.createElement('span');
	this.secondaryButtons = document.createElement('span');
	this.activeExpDisplay = document.createElement('span');
	this.secondaryExpDisplay = document.createElement('span');
	this.primaryButtons.setAttribute('class', 'suggest-button');
	this.secondaryButtons.setAttribute('class', 'suggest-button');
	this.primaryArea.setAttribute('class', 'suggest-area');
	this.secondaryArea.setAttribute('class', 'suggest-area secondary');
	this.activeExpDisplay.setAttribute('class', 'suggest-exp');
	this.secondaryExpDisplay.setAttribute('class', 'suggest-exp');
	this.suggestCategories = [];
	this.primaryIndices = [];
	this.secondaryIndices = [];
	
	suggestArea.appendChild(this.secondaryArea);
	suggestArea.appendChild(this.primaryArea);
	this.primaryArea.appendChild(this.activeExpDisplay);
	this.primaryArea.appendChild(this.primaryButtons);
	this.secondaryArea.appendChild(this.secondaryExpDisplay);
	this.secondaryArea.appendChild(this.secondaryButtons);
};

GH.ButtonController.prototype.clearButtons = function() {
	while(this.primaryButtons.firstChild){
    	this.primaryButtons.removeChild(this.primaryButtons.firstChild);
	}
	this.suggestCategories = [];
	while(this.secondaryButtons.firstChild){
    	this.secondaryButtons.removeChild(this.secondaryButtons.firstChild);
	}
	this.secondaryExpDisplay.innerHTML = '';
	this.primaryIndices = [];
	this.secondaryIndices = [];
}

GH.ButtonController.prototype.setActive = function(areaNum, isActive) {
	var area = (areaNum == 0) ? this.primaryArea : this.secondaryArea;
	if (isActive) {
		GH.ProofSegment.addClass(area, 'active');
	} else {
		GH.ProofSegment.removeClass(area, 'active');
	}
};

GH.ButtonController.BUTTON_ORDER = [
    'Evaluate', 'Simplify', 'Cancel', 'Commute', 'Associate', 'Distribute', 'Equivalence', 'Define', 'Infer', 'Add', 'Remove', 
    'Copy', 'Substitute', 'Remove', 'Cond.', 'Exist.', 'Instant.'
];

GH.ButtonController.insertButton = function(buttons, insertion, indices, name) {
	var index = GH.ButtonController.BUTTON_ORDER.indexOf(name);
	if (index < -1) {
		window.console.log('Nonstandard button name used.');
		buttons.appendChild(insertion);
		return;
	}

	buttons.appendChild(insertion);
	var insertPoint = 0;
	while ((insertPoint < indices.length) && (index >  indices[insertPoint])) {
		insertPoint++;
	}
	indices.splice(insertPoint, 0, index);
	if (insertPoint == indices.length) {
		buttons.appendChild(insertion);
	} else {
		buttons.insertBefore(insertion, buttons.children[insertPoint]);
	}
};

GH.ButtonController.prototype.addSuggestionButton = function(name, clickHandler, isPrimary) {
	var suggestion = document.createElement('input');
	suggestion.setAttribute('type', 'button');
	suggestion.setAttribute('value', name);
	suggestion.setAttribute('onclick', clickHandler);
	var buttons = (isPrimary) ? this.primaryButtons : this.secondaryButtons;
	var indices = (isPrimary) ? this.primaryIndices: this.secondaryIndices;
	GH.ButtonController.insertButton(buttons, suggestion, indices, name);
};

GH.ButtonController.prototype.addCategorizedButton = function(category, name, clickHandler, isPrimary) {
	if (!this.suggestCategories.hasOwnProperty(category)) {
		var categoryElement = document.createElement('span');
		categoryElement.setAttribute('class', 'suggest-category');
		this.suggestCategories[category] = categoryElement;

		var label = document.createElement('span');
		label.setAttribute('class', 'category-label');
		label.innerHTML = category;
		categoryElement.appendChild(label);
		var buttons = (isPrimary) ? this.primaryButtons : this.secondaryButtons;
		var indices = (isPrimary) ? this.primaryIndices: this.secondaryIndices;
		GH.ButtonController.insertButton(buttons, categoryElement, indices, category);
	}
	var suggestion = document.createElement('input');
	suggestion.setAttribute('type', 'button');
	suggestion.setAttribute('value', name);
	suggestion.setAttribute('onclick', clickHandler);
	this.suggestCategories[category].appendChild(suggestion);
};

// Traverses the expression tree up to the where the current selection. Set classes and click handlers.
GH.ButtonController.prototype.displayActiveExp = function(activeExp) {
	if (!activeExp) {
		return;
	}	

	var root = activeExp.getRoot();
	var rootExpressionToShow = root.getExpression();
	var position = GH.Prover.findPosition(activeExp);

	if (!root.isProven) {
		this.activeExpDisplay.innerHTML = GH.sexptohtmlHighlighted(rootExpressionToShow, -1);
		return;
	}

	// if (position.length != 0) && (rootExpressionToShow.length == 2) { selectionState = 'selectable-ancestor';}  // Currently disabled.
	var selectionState = GH.Prover.getSelectionState(rootExpressionToShow, -1, -1, position.length > 0);
	rootExpressionToShow = ['htmlSpan', selectionState, rootExpressionToShow];
	expressionToShow = rootExpressionToShow[2];
	for (var i = 0; i < position.length; i++) {
		var pos = position[i] + 1;
		for (var j = 1; j < expressionToShow.length; j++) {
			selectionState = GH.Prover.getSelectionState(expressionToShow, j, pos, (i != position.length - 1));
			expressionToShow[j] = ['htmlSpan', selectionState, expressionToShow[j]];
		}
		expressionToShow = expressionToShow[pos];
		expressionToShow = expressionToShow[2];
	}
	for (var i = 1; i < expressionToShow.length; i++) {
		expressionToShow[i] = ['htmlSpan', 'selectable-child', expressionToShow[i]];
	}
	this.activeExpDisplay.innerHTML = GH.sexptohtmlHighlighted(rootExpressionToShow, -1);
	GH.Prover.addClickHandlers(this.activeExpDisplay, {operand: 0, parent: 0});
};

GH.ButtonController.highlightMatch = function(expression, match) {
	var position = GH.Prover.findPosition(match);
	if (position.length > 0) {
		var expressionRoot = expression;
		for (var i = 0; i < position.length; i++) {
			var pos = position[i] + 1;
			if (i < position.length - 1) {
				expression = expression[pos];
			} else {
				expression[pos] = ['htmlSpan', 'matching-exp', expression[pos]];
			}
		}
		return expressionRoot;
	} else {
		return ['htmlSpan', 'matching-exp', expression];
	}
};

GH.ButtonController.prototype.setSecondaryDisplay = function(expression, match) {
	GH.ButtonController.highlightMatch(expression, match);
	this.secondaryExpDisplay.innerHTML = GH.sexptohtmlHighlighted(expression, -1);
	this.setActive(1, true);
};