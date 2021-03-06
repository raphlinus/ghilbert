// When proofs are displayed they are organized hierarchically into proof segments.
// by Paul Merrell, 2013

GH.ProofSegment = function(state, type, step, hasPrevious) {
	this.parent = null;
	this.children = [];
	this.siblingIndex = -1;
	this.step = step;
	this.state = state;
	this.type = type;
	this.isOpen = false;
	this.hasPrevious = hasPrevious;
	this.attachChildrenData = null;  // Saved data to attach children when needed.
	this.hasCloseColumn = false;
	this.aligned = false; // If this expression should be aligned up next to the previous expression because they partially match.

	this.smallElement = null;
	// The large wrapper contains the arrow sidebar and the large element.
	this.largeWrapper = GH.ProofSegment.createLargeWrapper(type);
	this.largeElement = this.largeWrapper.children[1];
};

GH.ProofSegment.State = {
	SMALL: 0,
	LARGE: 1
};

// Most of the type enum never gets used, but this explains what all the types mean.
GH.ProofSegment.Type = {
	WHITE_OUTER: 0,  // A white-colored outer block.
	WHITE_INNER: 1,  // A block inside a white block. It is white when open, gray when closed.
	 GRAY_OUTER: 2,  // A gray-colored outer block.
	 GRAY_INNER: 3,  // A block inside a gray block. It is gray when open, white when closed.
};

GH.ProofSegment.createSegments = function(conclusion, stack, segmentCount, useLatex) {
	if (!conclusion.isError) {
		var rootSegment = new GH.ProofSegment(GH.ProofSegment.State.LARGE, GH.ProofSegment.Type.WHITE_OUTER, conclusion, false);
		rootSegment.siblingIndex = segmentCount;
		stack.appendChild(rootSegment.largeWrapper);
	
		var stepsData = GH.ProofSegment.findImportantSteps(conclusion, null);
		rootSegment.attachChildren(stepsData, true, useLatex);
		rootSegment.addNames();
		rootSegment.resize();
	} else {
		var errorBlock = GH.ProofSegment.createLargeWrapper(GH.ProofSegment.Type.WHITE_OUTER);
		errorBlock.className += ' error';
		stack.appendChild(errorBlock);
		var tableElement = GH.ProofSegment.addTable(errorBlock.children[1]);
		var errorMsg = GH.ProofStep.stepToHtml(conclusion.conclusion, '', false);
		tableElement.appendChild(errorMsg);
	}
	return rootSegment;
};

GH.ProofSegment.prototype.addHandlers = function() {
	var position = '[' + this.getPosition().toString() + ']';
	this.smallElement.setAttribute('onmouseover', 'GH.ProofSegment.handleMouseOver(' + position + ')');
	this.smallElement.setAttribute('onmouseout', 'GH.ProofSegment.handleMouseOut('  + position + ')');
	this.smallElement.setAttribute('onclick', 'GH.ProofSegment.handleClick('  + position + ')');
	if (this.type % 2) {
		GH.ProofSegment.addClass(this.largeElement, 'inner-block');
	}
};

GH.ProofSegment.prototype.addNames = function() {
	for (var i = 0; i < this.children.length; i++) {
		var prevStep = (i == 0) ? null : this.children[i - 1].step;
		var step = this.children[i].step;
		var nextStep = (i == this.children.length - 1) ? null : this.children[i + 1].step;

		// Double check that the previous step actually comes earlier in the proof. The steps can 
		// be reordered for consistent presentation. If it's not before, ignore it.
		if (prevStep && prevStep.begin > step.begin) {
			prevStep = null;
		}

		var singleStep = false;
		if (i == this.children.length - 1) {
			var steps = [];
			for (var j = 0; j < this.children.length; j++) {
				steps.push(this.children[j].step);
			}
			singleStep = (GH.ProofSegment.isSingleStep(this.step, steps));
		}
		var name;
		if (this.hasPrevious && (i == 0)) {
			name = '';
		} else if (singleStep) {
			name = step.title || step.name_.toString();
		} else {
			name = GH.ProofSegment.getName(prevStep, step, nextStep);
		}
		var smallElement = this.children[i].smallElement;
		this.getNameColumn(smallElement).children[0].innerHTML = name;
		this.children[i].addNames();
	}
};

GH.ProofSegment.prototype.getNameColumn = function(rowElement) {
	var nameIndex = this.hasCloseColumn ? rowElement.children.length - 3 : rowElement.children.length - 2;
	return rowElement.children[nameIndex];
};

GH.ProofSegment.getName = function(prevStep, step, nextStep) {
	var name = step.findBestTitle(prevStep).title;
	var hierarchy = step.hierarchy;
	while (hierarchy && (!prevStep || prevStep.end <= hierarchy.begin) && (!nextStep || nextStep.begin >= hierarchy.end)) {
		if (hierarchy.name) {
			name = hierarchy.name;
		}
		hierarchy = hierarchy.parent;
	}
	return name;
};

// Returns true, if the steps are equal to the hypotheses and conclusion of a single step.
GH.ProofSegment.isSingleStep = function(step, steps) {
	var hyps = steps.slice(0)
	hyps.pop();
	if (!(GH.ProofSegment.isSubset(step.hypotheses, hyps) &&
 	      GH.ProofSegment.isSubset(hyps, step.hypotheses))) {
		return false;
	}
	// This test probably isn't necessary, but why not.
	if (step.conclusion != steps[steps.length - 1].conclusion) {
		return false;
	}
	return true;
};

GH.ProofSegment.handleCloseBlock = function(position) {
	var segment = GH.ProofSegment.findSegments([position])[0];
	window.direct.removeText(segment.step.getBeginning(), segment.step.end);
};

GH.ProofSegment.handleCloseStep = function(position) {
	var segment = GH.ProofSegment.findSegments([position])[0];
	window.direct.removeText(segment.step.begin, segment.step.end);
};

GH.ProofSegment.prototype.createCloseColumn = function(i, steps) {
	var xElement = document.createElement("td");
	xElement.innerHTML='X';
	if ((i != 0) && (i != steps.length - 1)) {
		xElement.setAttribute('class', 'inactive-x step-x');
	} else {
		xElement.setAttribute('class', 'step-x');
		if (i == 0) {
			xElement.setAttribute('onclick', 'GH.ProofSegment.handleCloseBlock(' + this.getPosition() + ')');
		} else {
			xElement.setAttribute('onclick', 'GH.ProofSegment.handleCloseStep(' + this.getPosition() + ')');
		}
	}
	return xElement;
};

GH.ProofSegment.prototype.attachChildren = function(stepsData, recursion, useLatex) {
	var steps = stepsData.steps;
	var tableElement = GH.ProofSegment.addTable(this.largeElement);
	this.hasCloseColumn = (this.getPosition().length == 1);
	
	for (var i = 0; i < steps.length; i++) {
		var endStep = (i > 0) ? steps[i - 1] : null;
		var newStepsData = GH.ProofSegment.findImportantSteps(steps[i], endStep);
		// If this is a single step or in other words it corresponds directly to a particular theorem, use 
		// the styling of that theorem to display the steps in a table with similar terms arranged in columns.
		var isSingleStep = GH.ProofSegment.isSingleStep(this.step, steps);
		var stylized = this.step.styling && isSingleStep;

		// If this is stylized in a table, we unfortunately cannot display the child of this step as an inner block.
		// The problem is that there is no way to replace one row of the table with the inner block. 
		var type = this.type + 1;
		var skipType = stylized && (type % 2 == 1);
		type += skipType ? 1 : 0;
		type = type % 4;
		var child = new GH.ProofSegment(GH.ProofSegment.State.SMALL, type, steps[i], newStepsData.hasEnd);
		child.parent = this;
		this.children.push(child);
		child.siblingIndex = i;

		var isConclusion = (i == steps.length - 1);
		if (stylized) {
			var styleIndex = isConclusion ? i : this.step.hypotheses.indexOf(steps[i]);
			var stylizedExpression = GH.ProofSegment.styleExpression(this.step.styling[styleIndex], steps[i].conclusion);
			var partialHtml = GH.sexptohtml(stylizedExpression, useLatex);
			var nameHtml = GH.ProofStep.nameToHtml(steps[i].name_, steps[i].title, steps[i].link, isConclusion);
			var fullHtml = GH.ProofStep.stepToHtml(partialHtml, nameHtml, useLatex);
			child.smallElement = fullHtml;
			tableElement.appendChild(child.smallElement);
			if (useLatex) {
				MathJax.Hub.Queue(["Typeset", MathJax.Hub, child.smallElement]);
			}
		} else {
			tableElement = GH.ProofSegment.addTable(this.largeElement);
			var text;
			if ((i > 0) && (GH.ProofSegment.alignRepeatedParts(steps[i-1], steps[i]))) {
				child.aligned = true;
				if (i < steps.length - 1) {
					// The last step is aligned, but not hidden.
					var sexp = steps[i].conclusion.slice(0);
					sexp[1] = ['htmlSpan', 'hidden', sexp[1]];   // Hide.
					text = GH.sexptohtml(sexp, useLatex);
				} else {
					text = GH.sexptohtml(steps[i].conclusion, useLatex);
				}
			} else {
				child.aligned = false;
				text = GH.sexptohtml(steps[i].conclusion, useLatex);
			}	
			var link = isSingleStep ? steps[i].link : '';
			var nameHtml = GH.ProofStep.nameToHtml(steps[i].name_, steps[i].title, link, isSingleStep && isConclusion);
			child.smallElement = GH.ProofStep.stepToHtml(text, nameHtml, useLatex);
			tableElement.appendChild(child.smallElement);
			if (useLatex) {
				MathJax.Hub.Queue(["Typeset", MathJax.Hub, child.smallElement]);
			}
		}
		if (this.hasCloseColumn) {
			child.smallElement.appendChild(this.createCloseColumn(i, steps));
		}

		if (type % 2 == 0) {
			var referenceElement = skipType ? this.largeWrapper : this.parent.largeWrapper;
			stack.insertBefore(child.largeWrapper, referenceElement);
		} else {
			this.largeElement.appendChild(child.largeWrapper);
		}
		child.addHandlers();
		child.updateVisibility();

		if (recursion) {
			var newIsSubset = (GH.ProofSegment.isSubset(newStepsData.steps, stepsData.steps));
			var oldIsSubset = (GH.ProofSegment.isSubset(stepsData.steps, newStepsData.steps));
			if (!oldIsSubset || !newIsSubset) {
				// Calling child.attachChildren(newStepsData, !newIsSubset) here is slow if
				// we're not displaying any of the children. We save all the information so that we can display
				// the children when they are needed.
				child.attachChildrenData = {stepsData: newStepsData, recursion: !newIsSubset, useLatex: useLatex};
			}
		}
	}
	if (useLatex) {
		var self = this;
		MathJax.Hub.Queue(function() {
			self.resizeTables();
		});
	}
};

GH.ProofSegment.alignRepeatedParts = function(prevStep, step) {
	var isHidden = false;
	var hideableOperators = ['->', '<', '<=', '>', '>='].concat(GH.operatorUtil.EQUIVALENCE_OPERATORS);
	var sexp = step.conclusion;
	var prevSexp = prevStep.conclusion;
	var operator = String(sexp[0]);
	if (operator == String(prevSexp[0])) {
		var hideable = false;
		for (var i = 0; i < hideableOperators.length && !hideable; i++) {
			hideable = hideable || (operator == hideableOperators[i]);
		}
		if (hideable) {
			var prevLeft = GH.sExpression.fromRaw(prevSexp[1]);
			var left = GH.sExpression.fromRaw(sexp[1]);
			isHidden = left.equals(prevLeft)
		}
	}
	return isHidden;
};

/**
 * Add styling to an expression. The styling and the expression are both trees that we traverse
 * together. Whenever we encounter a node in the styling tree that has a "table" in it, we wrap
 * the expression there in a "table" node.
 */
GH.ProofSegment.styleExpression = function(styling, expression) {
	if (styling[0] == "table") {
		var styledExpression = GH.ProofSegment.styleExpression(styling[2], expression);
		return [styling[0], styling[1], styledExpression, styling[3]];
	} else if (styling[0] == 'htmlSpan') {
		var styledExpression = GH.ProofSegment.styleExpression(styling[2], expression);
		return [styling[0], styling[1], styledExpression];
	} else {
		if (typeof styling == 'string') {
			return expression;
		} else {
			var newExpression = [expression[0]];
			for (var i = 1; i < styling.length; i++) {
				newExpression.push(GH.ProofSegment.styleExpression(styling[i], expression[i]));
			}
		}
		return newExpression;
	}
};

GH.ProofSegment.prototype.delayedAttachChildren = function() {
	var data = this.attachChildrenData;
	if (data) {
		this.attachChildren(data.stepsData, data.recursion, data.useLatex);
		this.addNames();
	}
	this.attachChildrenData = null;
};

// Returns true if the steps in A are a subset of the steps in B.
GH.ProofSegment.isSubset = function(A, B) {
	for (var i = 0; i < A.length; i++) {
		var match = false;
		for (var j = 0; j < B.length; j++) {
			if (A[i] == B[j]) {
				match = true;
			}
		}
		if (!match) {
			return false;
		}
	}
	return true;
};

GH.ProofSegment.addTable = function(parent) {
	var tableElement = document.createElement("table");
	tableElement.setAttribute('cellspacing', 0);
	tableElement.setAttribute('class', 'table-no-border');
	parent.appendChild(tableElement);
	return tableElement;
};

GH.ProofSegment.createLargeWrapper = function(type) {
	var largeWrapper = document.createElement("div");
	largeWrapper.setAttribute('class', 'large-wrapper');
	var sidebar = document.createElement("div");
	var largeElement = document.createElement("div");
	if (type % 2 == 0) {
		sidebar.setAttribute('class', 'sidebar');
		largeElement.setAttribute('class', 'proof-block outer-block');
	} else {
		largeElement.setAttribute('class', 'proof-block');
	}
	largeWrapper.appendChild(sidebar);
	largeWrapper.appendChild(largeElement);
	return largeWrapper;
};

GH.ProofSegment.prototype.getPrevElement = function() {
	return this.parent && this.parent.children[this.siblingIndex - 1].smallElement;
};

GH.ProofSegment.prototype.updateVisibility = function() {
	if (this.state == GH.ProofSegment.State.SMALL) {
		this.smallElement.setAttribute('style', '');
		GH.ProofSegment.removeClass(this.smallElement, 'highlighted-step');
		GH.ProofSegment.removeClass(this.smallElement, 'highlighted-bottom');
		GH.ProofSegment.removeClass(this.smallElement, 'open-top');
		GH.ProofSegment.removeClass(this.smallElement, 'open-bottom');
		GH.ProofSegment.removeClass(this.smallElement, 'highlighted-open-top');
		GH.ProofSegment.removeClass(this.smallElement, 'highlighted-open-bottom');
		this.largeWrapper.setAttribute('style', 'display: none');
	} else if (this.state == GH.ProofSegment.State.LARGE) {
		if (this.type % 2) {
			this.smallElement.setAttribute('style', 'display: none');
			if (this.hasPrevious) {
				this.parent.children[this.siblingIndex - 1].smallElement.setAttribute('style', 'display: none');
			}
		} else {
			GH.ProofSegment.addClass(this.smallElement, 'highlighted-step');
			if (this.hasPrevious) {
				GH.ProofSegment.addClass(this.smallElement, 'highlighted-open-top');
				GH.ProofSegment.addClass(this.getPrevElement(), 'highlighted-bottom');
			}
		}
		this.largeWrapper.setAttribute('style', '');
	}
	if (((this.type + !this.isOpen) % 4) >= 2) {
		GH.ProofSegment.addClass(this.largeElement, 'gray-block');
	} else {
		GH.ProofSegment.removeClass(this.largeElement, 'gray-block');
	}
};

// Enlarge the last column of each table so that each row spans the width of the block.
GH.ProofSegment.prototype.resize = function() {
	for (var i = 0; i < this.children.length; i++) {
		this.children[i].resize();
	}
	if (this.state == GH.ProofSegment.State.LARGE) {
		this.resizeTables();
	}
};

// Enlarge the last column of each table so that each row spans the width of the block.
GH.ProofSegment.prototype.resizeTables = function(){
	var alignedGroup = [];
	for (var i = 0; i < this.children.length; i++) {
		var row = this.children[i].smallElement;
		var firstCell = row.children[1];
		firstCell.setAttribute('style', 'padding-left: auto');
		var lastCell = this.getNameColumn(row);
		if (lastCell) {
			// I don't know why this isn't always true.
			lastCell.setAttribute('style', 'padding-left: auto');
		}
		if (this.children[i].aligned && (i > 0)) {
			alignedGroup.push(alignedGroup[i - 1]);
		} else {
			alignedGroup.push(i);
		}
	}
	// Determine the maximum width for each aligned group.
	var groupIndices = [];
	var maxWidth = 0;
	var alignedWidths = [];
	for (var i = 0; i < this.children.length; i++) {
		var firstCell = this.children[i].smallElement.children[1];
		var width = parseInt(window.getComputedStyle(firstCell).width);
		if (i == alignedGroup[i]) {
			for (var j = 0; j < groupIndices.length; j++) {
				alignedWidths.push(maxWidth);
			}
			groupIndices = [i];
			maxWidth = width;
		} else {
			groupIndices.push(i);
			maxWidth = Math.max(maxWidth, width);
		}
	}
	for (var j = 0; j < groupIndices.length; j++) {
		alignedWidths.push(maxWidth);
	}	
	for (var i = 0; i < this.children.length; i++) {
		var row = this.children[i].smallElement;
		var firstCell = row.children[1];
		var lastCell = this.getNameColumn(row);
		if (lastCell) {
			// I don't know why this isn't always true.
			lastCell.setAttribute('style', 'width: auto');
		}
		var margin = (this.type % 2 == 0) ? 62 : 84;
		var largeWrapper = (this.type % 2 == 0) ? this.largeWrapper : this.parent.largeWrapper;
		var alignedWidth = alignedWidths[i];
		var width = parseInt(window.getComputedStyle(firstCell).width);
		var extraRight = alignedWidth - width;
		
		var padding = largeWrapper.offsetWidth - row.offsetWidth - margin;
		firstCell.setAttribute('style', 'padding-left: ' + Math.floor((padding - extraRight) / 2));
		if (lastCell) {
			// I don't know why this isn't always true.
			lastCell.setAttribute ('style', 'padding-left: ' + Math.ceil( (padding + extraRight) / 2));
		}
	}
};

GH.ProofSegment.prototype.getActiveElement = function () {
	if (this.state == GH.ProofSegment.State.SMALL) {
		return this.smallElement;
	}
	if (this.state == GH.ProofSegment.State.LARGE) {
		return this.largeWrapper;
	}
};

GH.ProofSegment.prototype.close = function() {
	this.isOpen = false;
	for (var i = 0; i < this.children.length; i++) {
		var child = this.children[i];
		child.close();
		child.state = GH.ProofSegment.State.SMALL;
		child.updateVisibility();
	}
	this.updateVisibility();
	this.resize();	
};

GH.ProofSegment.prototype.expand = function() {
	if (this.parent) {
		this.parent.isOpen = true;
	}
	this.close();
	this.updateVisibility();
	if (this.parent) {
		this.parent.updateVisibility();
	}
	this.resizeTables();	
};

GH.ProofSegment.prototype.highlight = function() {
	GH.ProofSegment.addClass(this.smallElement, GH.ProofStep.ORANGE_STEP_);
	GH.ProofSegment.addClass(this.largeElement, GH.ProofStep.ORANGE_BLOCK_);
	if (this.hasPrevious) {
		GH.ProofSegment.addClass(this.getPrevElement(), GH.ProofStep.ORANGE_STEP_);
		GH.ProofSegment.addClass(this.getPrevElement(), 'open-bottom');
		GH.ProofSegment.addClass(this.smallElement, 'open-top');
		var prevSegment = this.parent && this.parent.children[this.siblingIndex - 1];
	}
};

GH.ProofSegment.prototype.lowlight = function() {
	GH.ProofSegment.removeClass(this.smallElement, GH.ProofStep.ORANGE_STEP_);
	GH.ProofSegment.removeClass(this.largeElement, GH.ProofStep.ORANGE_BLOCK_);
	if (this.hasPrevious) {
		GH.ProofSegment.removeClass(this.getPrevElement(), GH.ProofStep.ORANGE_STEP_);
		GH.ProofSegment.removeClass(this.getPrevElement(), 'open-bottom');
		GH.ProofSegment.removeClass(this.smallElement, 'open-top');
	}
};

GH.ProofSegment.prototype.handleClick = function() {
	this.delayedAttachChildren();
	this.clearArrows();
	if (this.largeElement.children.length > 0) {
		this.state = GH.ProofSegment.State.LARGE;
		this.lowlight();
		this.expand();
		this.close();
	}
};

GH.ProofSegment.expand = function (step) {
	if (step.hypotheses.length == 0) {
		return new GH.StepSegment(step);
	}
	var childSegments = [];
	for (var i = 0; i < step.hypotheses.length; i++) {
		childSegments.push(new GH.StepSegment(step.hypotheses[i]));
	}
	childSegments.push(new GH.StepSegment(step));
	return new GH.BlockSegment(childSegments);
};

GH.ProofSegment.prototype.getPosition = function() {
	var position = [];
	var segment = this;
	while (segment.parent) {
		position.push(segment.siblingIndex);
		segment = segment.parent;
	}
	position.push(segment.siblingIndex);
	return position;
};

GH.ProofSegment.findSegments = function(position) {
	var segment = window.direct.rootSegments[position.pop()];
	if (!segment) {
		return [];
	}
	while (position.length > 0) {
		segment = segment.children[position.pop()];
	}

	var parentOpen = (segment.parent && segment.parent.isOpen);
	var hasChildren = (segment.largeElement.children.length > 0) || segment.attachChildrenData;
    var lastSibling = segment.parent && (segment.siblingIndex == segment.parent.children.length - 1);
	var isPrevious = segment.parent && segment.parent.hasPrevious && (segment.siblingIndex == 0);
	var isHighlighted = GH.ProofSegment.hasClass(segment.smallElement, 'highlighted-step');
	if (GH.ProofSegment.hasClass(segment.smallElement, 'highlighted-bottom') && segment.parent) {
		return [segment.parent.children[segment.siblingIndex + 1]];
	}
	if ((!parentOpen && (!lastSibling || hasChildren) && !isPrevious) || isHighlighted) {
		return [segment];
	} else {
		if (!isPrevious || parentOpen) {
			return [segment.parent];
		} else {
			return [segment.parent.parent, segment.parent];
		}
	}
};

GH.ProofSegment.prototype.findCollapseArrows = function() {
	var arrows = [];
	for (var i = 0; i < this.children.length; i++) {		
		if (this.children[i].state == GH.ProofSegment.State.LARGE) {
			arrows = this.children[i].findCollapseArrows();
			// Delete the previous arrow if this overlaps with it.
			if ((arrows.length > 0) && (arrows[arrows.length - 1].segment.getSidebar() == this.children[i].getSidebar())) {
				arrows.pop();
			}
			var className = (this.children[i].type % 2 == 0) ? 'collapse-down' : 'collapse-in';
			arrows.push({segment: this.children[i], class: className});
		}
	}
	return arrows;
};

GH.ProofSegment.findArrows = function(position) {
	var segment = window.direct.rootSegments[position.pop()];
	if (!segment) {
	return [];
	}
	while (position.length > 0) {
		segment = segment.children[position.pop()];
	}

	var parentOpen = (segment.parent && segment.parent.isOpen);
	var hasChildren = (segment.largeElement.children.length > 0) || segment.attachChildrenData;
    var lastSibling = segment.parent && (segment.siblingIndex == segment.parent.children.length - 1);
	var isPrevious = segment.parent && segment.parent.hasPrevious && (segment.siblingIndex == 0);
	var isHighlighted = GH.ProofSegment.hasClass(segment.smallElement, 'highlighted-step');
	if (GH.ProofSegment.hasClass(segment.smallElement, 'highlighted-bottom') && segment.parent) {
		return segment.parent.findCollapseArrows();
	}
	if ((!parentOpen && (!lastSibling || hasChildren) && !isPrevious) || isHighlighted) {
		if (isHighlighted) {
			return segment.findCollapseArrows();
		}
		var prevSegment = segment.parent && segment.parent.children[segment.siblingIndex - 1];
		if (prevSegment && segment.hasPrevious) {
			return [
				{segment: prevSegment, class: 'expand-up'},
				// The down arrow occurs on the segment line, but the top arrow creates and offset which
				// is negected by using the prevSegment again.
				{segment: prevSegment, class: 'expand-down'}
			];
		} else {
			return [{segment: segment, class: 'expand-up'}];
		}
	} else {
		if (!isPrevious || parentOpen) {
			return segment.parent.findCollapseArrows();
		} else {
			return segment.parent.parent.findCollapseArrows();
		}
	}
};

GH.ProofSegment.prototype.getSidebar = function() {
	var blockSegment;
	if (((this.state != GH.ProofSegment.State.SMALL) && (this.type % 2 != 1)) || (!this.parent)) {
		blockSegment = this;
	} else if (this.parent.type % 2 == 1) {
		blockSegment = this.parent.parent;
	} else {
		blockSegment = this.parent;
	}
	return blockSegment.largeWrapper.children[0];
};

GH.ProofSegment.getSidebarPosition = function(block, siblingIndex) {
	var position = GH.ProofSegment.PADDING;
	if (block.type % 2 == 1) {
		position += GH.ProofSegment.getSidebarPosition(block.parent, block.siblingIndex);
	}
	for (var i = 0; i < siblingIndex; i++) {
		var child = block.children[i];
		if ((child.state == GH.ProofSegment.State.SMALL) || (child.type % 2 == 0)) {
			position += child.smallElement.clientHeight;
		} else {
			position += child.largeElement.clientHeight;
		}
	}
	return position;
};

GH.ProofSegment.addArrows = function(arrows) {
	var segment = arrows.segment;
	var className = arrows.class;

	var top;
	var bottom;	
	var sidebar;
	if ((segment.state == GH.ProofSegment.State.SMALL) || (segment.type % 2 == 1)) {
		top    = GH.ProofSegment.getSidebarPosition(segment.parent, segment.siblingIndex);
		bottom = GH.ProofSegment.getSidebarPosition(segment.parent, segment.siblingIndex + 1);
	} else {
		top    = GH.ProofSegment.getSidebarPosition(segment, 0);
		bottom = GH.ProofSegment.getSidebarPosition(segment, segment.children.length);
	}
	sidebar = segment.getSidebar();
	var height = bottom - top;

	if (className == 'collapse-in') {
		var topArrows = document.createElement("div");
		var bottomArrows = document.createElement("div");
		topArrows.setAttribute('class', 'collapse-down');
		bottomArrows.setAttribute('class', 'collapse-up');
		topArrows.setAttribute('style', 'height: ' + (height / 2) + 'px; top: ' + top + 'px');
		bottomArrows.setAttribute('style', 'height: ' + (height / 2) + 'px; top: ' + top + 'px');
		sidebar.appendChild(topArrows);
		sidebar.appendChild(bottomArrows);
	} else {
		var arrows = document.createElement("div");
		arrows.setAttribute('class', className);
		arrows.setAttribute('style', 'height: ' + height + 'px; top: ' + top + 'px');
		sidebar.appendChild(arrows);
	}
};

GH.ProofSegment.prototype.clearArrows = function() {
	var sidebar = this.getSidebar();
	if (sidebar) {
		sidebar.innerHTML = '';
	}
	this.largeWrapper.children[0].innerHTML = '';
	for (var i = 0; i < this.children.length; i++) {
		if (this.children[i].state == GH.ProofSegment.State.LARGE) {
			this.children[i].clearArrows();
		}
	}
};

GH.ProofSegment.handleMouseOver = function(position) {
	if (position[position.length - 1] == 0) {
		return;  // The proof statement is not interactive.
	}
	var positionCopy = position.slice(0);
	var segments = GH.ProofSegment.findSegments(position);
	for (var i = 0; i < segments.length; i++) {
		segments[i].clearArrows();
		segments[i].highlight();
	}
	var arrows = GH.ProofSegment.findArrows(positionCopy);
	for (var i =0; i < arrows.length; i++) {
		GH.ProofSegment.addArrows(arrows[i]);
	}
};

GH.ProofSegment.handleMouseOut = function(position) {
	if (position[position.length - 1] == 0) {
		return;  // The proof statement is not interactive.
	}
	var segments = GH.ProofSegment.findSegments(position);
	for (var i = 0; i < segments.length; i++) {
		segments[i].clearArrows();
		segments[i].lowlight();
	}
};

GH.ProofSegment.handleClick = function(position) {
	if (position[position.length - 1] == 0) {
		return;  // The proof statement is not interactive.
	}
	var segments = GH.ProofSegment.findSegments(position);
	segments[0].handleClick();
	window.direct.text.setCursorPosition(segments[0].step.end);
};

GH.ProofSegment.findImportantSteps = function(startStep, endStep) {
	var importantSteps = GH.ProofSegment.findImportantStepsEnd(startStep, endStep);
	var originalHasEnd = importantSteps.hasEnd;
	if (importantSteps.steps.length == 2) {
		endStep = importantSteps.steps[0];
		importantSteps = GH.ProofSegment.findImportantStepsEnd(startStep, endStep);
		importantSteps.hasEnd = originalHasEnd;
	}
	return importantSteps;
};

// Same as findImportantStepsRecursive, but includes the start and end steps if either is missing.
GH.ProofSegment.findImportantStepsEnd = function(startStep, endStep) {
	var importantSteps = GH.ProofSegment.findImportantStepsRecursive(startStep, startStep, endStep);
	// Include the start step, if it is missing.
	if (importantSteps.steps[importantSteps.steps.length - 1] != startStep) {
		importantSteps.steps.push(startStep);
	}
	// Include the end step if it is missing.
	if (endStep && importantSteps.hasEnd && importantSteps.steps[0] != endStep) {
		importantSteps.steps.splice(0, 0, endStep);
	}
	return importantSteps;
};

GH.ProofSegment.findImportantStepsRecursive = function(step, startStep, endStep) {
	if (step == endStep) {
		// We found the end step. We traverse the tree backwards now. This is our first step in the reverse direction.
		return {depth: 1e10, steps: [], hasEnd: true, hasBranch: false};
	}

	var results = [];
	var conclusionDepth = step.hierarchy.getDepth();
	var minDepth = 1e10;
	var minIndices = [];
	var endIndex = -1;
	for (var i = 0; i < step.hypotheses.length; i++) {
		var branchResult = GH.ProofSegment.findImportantStepsRecursive(step.hypotheses[i], startStep, endStep);
		results.push(branchResult);
		if (branchResult.depth < minDepth) {
			minDepth = branchResult.depth;
			minIndices = [i];
		} else if (branchResult.depth == minDepth) {
			minIndices.push(i);
		}
		if (branchResult.hasEnd) {
			endIndex = i;
		}
	}

	if (endIndex == -1) {
		if ((conclusionDepth < minDepth) && ((step != startStep) || (results.length == 0))) {
			return {depth: conclusionDepth, steps: [step], hasEnd: false, hasBranch: false};
		}
		if (minIndices.length > 1) {
			// If there are two branches with the lowest depth, we are doing a branch which includes everything
			// even high depth hypotheses.
			var steps = [];
			for (var i = 0; i < step.hypotheses.length; i++) {
				steps.push(step.hypotheses[i]);
			}
			steps.push(step);
			return {depth: minDepth, steps: steps, hasEnd: false, hasBranch: true};
		}
		var result = results[minIndices[0]];
		if (conclusionDepth <= minDepth) {
			if (result.hasBranch) {
				// This is not ideal, but we haven't set it up to do linear steps and then a branch.
				// In this case, do not include anything in the branch. Just keep the linear part.
				result.steps = [result.steps[0]];
			}
			result.steps.push(step);
		}
		return {depth: minDepth, steps: result.steps, hasEnd: false, hasBranch: false};
	} else {
		var endStep = step.hypotheses[endIndex];
		var endDepth = endStep.hierarchy.getDepth();
		var endSteps = results[endIndex].steps;

		// The end and the start step are right next to each other. Copy all the hypotheses,
		// we're doing a branch.		
		if ((step == startStep) && (endSteps.length == 0)) {
			var steps = [endStep];
			for (var i = 0; i < step.hypotheses.length; i++) {
				if (i != endIndex) {
					steps.push(step.hypotheses[i]);
				}
			}
			steps.push(step);
			return {depth: 1e10, steps: steps, hasEnd: true, hasBranch: true};
		}
		
		var addConclusion = false;
		if ((conclusionDepth < minDepth) && (step != startStep)) {
			return {depth: conclusionDepth, steps: [step], hasEnd: true};
		}
		if (minDepth >= endDepth) {
			// Add hypothesis if not already included.
			if (endSteps[endSteps.length - 1] != endStep) {
				endSteps.push(endStep);
				addConclusion = true;
			}
		}
		if (conclusionDepth <= endDepth) {
			addConclusion = true;
		}
		if (addConclusion) {
			endSteps.push(step);
		}
		return {depth: minDepth, steps: endSteps, hasEnd: true, hasBranch: false};
	}
};

// Returns true if an element has a particular class.
GH.ProofSegment.hasClass = function(element, className) {
	return element && element.className.match(new RegExp(className));
};

// Add a class to an element.
GH.ProofSegment.addClass = function(element, className) {
	if (element && !GH.ProofSegment.hasClass(element, className)) {
		element.className += ' ' + className;
	}
};

// Remove a class from an element.
GH.ProofSegment.removeClass = function(element, className) {
	if (element) {
		element.className = element.className.replace(new RegExp(' ' + className), '');
	}
};

// The top padding in the proof-block class plus 1 for the border.
GH.ProofSegment.PADDING = 7;