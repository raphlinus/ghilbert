// Javascript for displaying proof steps. Steps are organized into proof blocks.
// by Paul Merrell, 2013

/**
 * This represents a hierarchy of proof steps. A proofHierarchy either contains a single
 * proof step or it contains a list of children that are proofHierarchies themselves.
 * If it has children, the children contains all the proof steps between a pair of <d> and
 * </d> tags.
 *   - step: A single proof step or null.
 *   - begin: The cursor position where the hierarchy begins.
 *   - name: The name in the <d> tag.
 */
GH.ProofHierarchy = function(step, begin, name) {
	this.parent = null;
	this.step = step;
	this.name = name;
	this.children = []; // An array of proofHierarchies.
	if (step) {
		step.hierarchy = this;
		this.end = step.end;
	} else {
		this.end = GH.ProofHierarchy.MAX_SIZE;
	}
	this.begin = begin;
	this.siblingIndex = -1;
};

GH.ProofHierarchy.MAX_SIZE = 1e10;

// Returns true if the hierarchy is still open and being added to.
GH.ProofHierarchy.prototype.isOpen = function() {
	return (this.end == GH.ProofHierarchy.MAX_SIZE);
};

GH.ProofHierarchy.prototype.appendChild = function(child) {
	child.siblingIndex = this.children.length;
	child.parent = this;
	this.children.push(child);
	if (child.begin < this.begin) {
		this.begin = child.begin;
	}
};

GH.ProofHierarchy.prototype.removeChild = function(siblingIndex) {
	for (var i = siblingIndex + 1; i < this.children.length; i++) {
		this.children[i].siblingIndex--;
	}
	this.children.splice(siblingIndex, 1);
};

// Find the highest position with the hierarchy that a statement is not the conclusion of.
GH.ProofHierarchy.prototype.findPosition = function() {
	if (this.parent && (this.siblingIndex == this.parent.children.length - 1)) {
		return this.parent.findPosition();
	} else {
		return this.parent;
	}
};

// Returns the depth of the position.
GH.ProofHierarchy.prototype.getDepth = function() {
	var position = this.findPosition();
	var depth = 0;
	while(position && position.parent) {
		position = position.parent;
		depth++;
	}
	return depth;
};

// Lower this proof hierarchy. It will acquire a new parent and become a grandchild of its current parent.
GH.ProofHierarchy.prototype.reparent = function(newParent) {
	this.parent.removeChild(this.siblingIndex);
	newParent.appendChild(this);
};

GH.ProofHierarchy.prototype.getLastStep = function() {
	if (this.step) {
		return this.step;
	} else {
		if (this.children.length > 0) {
			return this.children[this.children.length - 1].getLastStep();
		} else {
			return null;
		}
	}
};

/**
 * Represents the input and output of each proof step.
 *   name (string): The name of this proof step.
 *   hypotheses (Array.<ProofStep>): An array of proof steps used as inputs to this step.
 *   conclusion: (s-expression) An s-expression that is the result of this step.
 *   begin (number): The cursor position of the beginning of this step.
 *   end (number): The cursor position of the end of this step.
 *   sExpressions (Array.<s-expression>): An array of s-expressions used to create this step.
 *   isError: Whether the expression is signaling an error.
 *   depth: The depth of the proof step. Proof steps with a higher depth are less important and less visible.
 *   styling: The way to style the statements.
 */
GH.ProofStep = function(name, hypotheses, conclusion, begin, end, sExpressions, isError, styling) {
	this.name_ = name;
	this.hypotheses = hypotheses;
	this.conclusion = conclusion;
	this.begin = begin;
	this.end = end;
	this.isError = isError;
	this.link = styling ? GH.ProofStep.computeLink(styling.filename, styling.isAxiom, name) : null;
	this.substitution = null;
	this.thmNumber = styling ? styling.thmNumber : 0;
	this.styling = styling ? styling.table : null;
	this.title = styling && styling.title ? styling.title : '';
	this.hierarchy = null;

	this.sExpressions_ = [];
	for (var i = 0; i < sExpressions.length; i++) {
		this.sExpressions_.push(GH.sExpression.fromRaw(sExpressions[i][1]));
	}
};

// Html for adding a new cell to a table.
GH.ProofStep.NEW_CELL  = '</td><td>';

GH.ProofStep.prototype.print = function() {
	return GH.sExpression.printRaw(this.conclusion);
};

GH.ProofStep.computeLink = function(filename, isAxiom, stepName) {
	if (filename == '') {
		return null;
	}
	filename = filename.replace(new RegExp('/git'), '');
	if (filename.match(new RegExp('/proofs_upto'))) {
		var splitUp = filename.split('/');
		splitUp.splice(0, 4);
		splitUp.pop();
		filename = '/' + splitUp.join('/');
	} else if (!isAxiom) {
		filename = filename.replace(new RegExp('.ghi'), '.gh');
	}
	return filename + '/' + stepName;
};

/**
 * Find the beginning of the proof step this includes the beginning of any hypotheses
 * that this step depends on.
 */
GH.ProofStep.prototype.getBeginning = function() {
	if (this.hypotheses.length > 0) {
		return this.hypotheses[0].getBeginning();
	} else {
		if (this.sExpressions_.length > 0) {
			return this.sExpressions_[0].getBeginning();
		} else {
			return this.begin;
		}
	}
};

GH.ProofStep.prototype.findBestTitle = function(prevStep) {
	if (prevStep == this) {
		return {title: this.title, score: 0};
	}
	var bestTitle = this.title || this.name_.toString();;
	var bestScore = this.thmNumber;
	if ((this.title.search('Substitution') != -1) && (this.name_.search('Replace') != -1)) {
		// The substitution theorems are not important even if they have a high number.
		bestScore = 0;
	}
	for (var i = 0; i < this.hypotheses.length; i++) {
		var hypResult = this.hypotheses[i].findBestTitle(prevStep);
		if (hypResult.score > bestScore) {
			bestScore = hypResult.score;
			bestTitle = hypResult.title;
		}
	}
	return {title: bestTitle, score: bestScore};
};

// Render the proof step name in HTML.
GH.ProofStep.nameToHtml = function(name, title, link, isPrimary) {
	if ((title == '') || (title === undefined)) {
		title = name;
	}

	var classes = 'proof-step-name';
	classes += (isPrimary ? ' primary-step-name' : '');
	if (isPrimary && link) {
		return '<a href="/edit' + link + '"  class=\'' + classes + '\'>' + title + '</a>';
	} else {
		return '<span class=\'' + classes + '\'>' + title + '</span>';
	}
};

/**
 * Returns the proof step displayed as a set of blocks.
 * This is the main entry point for displaying the proof steps.
 */
GH.ProofStep.prototype.displayStack = function(stack, summary, header, segmentCount, useLatex) {
	if (header != '') {
		if (summary !== null) {
			var summaryElement = document.createElement("div");
			stack.appendChild(summaryElement);
			summaryElement.innerHTML = summary;
			if (summary != '') {
				summaryElement.setAttribute('class', 'summary');
			} else {
				summaryElement.setAttribute('class', 'no-summary');
			}
		}
		var headerElement = document.createElement("div");
		stack.appendChild(headerElement);
		headerElement.innerHTML = header;
		headerElement.setAttribute('class', 'thmHeader');
	}
	return GH.ProofSegment.createSegments(this, stack, segmentCount, useLatex);
};

GH.ProofStep.createCloseColumn = function(inputArg) {
	var xElement = document.createElement("td");
	xElement.innerHTML='X';
	xElement.setAttribute('class', 'step-x');
	xElement.setAttribute('onclick', 'window.direct.removeText(' + inputArg[1].beg + ',' + inputArg[1].end + ')');
	return xElement;
};

// Display the left over input arguments on the stack
GH.ProofStep.displayInputArguments = function(stack, inputArgs, expectedTypes, useLatex) {
	var rowCount = Math.max(inputArgs.length, expectedTypes.length && expectedTypes[0].length);
	if (rowCount == 0) {
		return;
	}

	var headerElement = document.createElement("div");
	stack.appendChild(headerElement);
	headerElement.innerHTML = 'Input Argument' + ((inputArgs.length > 1) ? 's' : '');
	headerElement.setAttribute('class', 'thmHeader');
		
	var classes = 'proof-block input-args';
	var newBlock = new GH.ProofSegment(GH.ProofSegment.State.LARGE, 0, null, false);
	newBlock.hasCloseColumn = true;
	newBlock.largeElement.className += ' input-args';
	var tableElement = GH.ProofSegment.addTable(newBlock.largeElement);
	// var nameHtml = '<span class=proof-step-name>Input Argument' + ((inputArgs.length > 1) ? 's' : '') + '</span>';
	for (var i = 0; i < inputArgs.length; i++) {
		var child = new GH.ProofSegment(GH.ProofSegment.State.SMALL, 0, null, false);
		newBlock.children.push(child);
		// var iNameHtml = (i == 0) ? nameHtml : '';
		var partialHtml = GH.sexptohtml(inputArgs[i][1], useLatex);
		//var fullHtml = GH.ProofStep.stepToHtml(partialHtml, iNameHtml, useLatex);
		var fullHtml = GH.ProofStep.stepToHtml(partialHtml, '', useLatex);
		child.smallElement = fullHtml;
		child.smallElement.appendChild(GH.ProofStep.createCloseColumn(inputArgs[i]));
		tableElement.appendChild(child.smallElement);
	}
	stack.appendChild(newBlock.largeWrapper);
	if (useLatex) {
		MathJax.Hub.Queue(["Typeset", MathJax.Hub, newBlock.largeElement]);
	}

	if (expectedTypes.length > 0) {
		for (var i = 0; i < rowCount; i++) {
			var expectedContainer = document.createElement("td");
			expectedContainer.setAttribute('class', 'type-container');
			var expectedElement = document.createElement("span");
			
			// Error results unless the types are the same, or we expected a natural number and got a binding variable.
			var suffix = '';
			if ((expectedTypes[0][i] != expectedTypes[1][i]) && (!((expectedTypes[0][i] == 'nat') && (expectedTypes[1][i] == 'bind')))) {
				suffix = '-error';
			}
			expectedElement.setAttribute('class', 'type-tag type-' + expectedTypes[0][i] + suffix);  // Expected types
			expectedElement.innerHTML = expectedTypes[0][i];
			expectedContainer.appendChild(expectedElement);
			
			var actualContainer = document.createElement('td');
			actualContainer.setAttribute('class', 'type-container');
			var actualElement = document.createElement('span');
			actualElement.setAttribute('class', 'type-tag type-' + expectedTypes[1][i] + suffix);    // Actual types
			actualElement.innerHTML = expectedTypes[1][i];
			actualContainer.appendChild(actualElement);

			if (i >= tableElement.childNodes.length) {
				var rowElement = document.createElement('tr');				
				rowElement.setAttribute('class', 'proof-step-div unstyled');
				rowElement.appendChild(expectedContainer);
				rowElement.appendChild(actualContainer);
				var child = new GH.ProofSegment(GH.ProofSegment.State.SMALL, 0, null, false);
				child.smallElement = rowElement;
				newBlock.children.push(child);
				tableElement.appendChild(child.smallElement);
			} else {
				var rowElement = tableElement.children[i];
				rowElement.insertBefore(expectedContainer, rowElement.children[0]);
				rowElement.insertBefore(  actualContainer, rowElement.children[1]);
			}
		}
	}	
	if (useLatex) {
		var self = this;
		MathJax.Hub.Queue(function() {
			newBlock.resize();
		});
	} else {
		newBlock.resize();
	}
};

// Display a proof step.
//   text: The text inside the step.
//   name: The name of the proofstep.
GH.ProofStep.stepToHtml = function(text, name, useLatex) {
	useLatex = useLatex && GH.ENABLE_LATEX;
	var row = document.createElement("tr");
	row.setAttribute('class', 'proof-step-div ');

	// Split the text using the html tags into the cells of a table.
	var cellTexts = [];
	var index = text.indexOf(GH.ProofStep.NEW_CELL);
	var newCellLength = GH.ProofStep.NEW_CELL.length;
	while(index > -1) {
		cellTexts.push(text.substring(0, index));
		text = text.substring(index + newCellLength, text.length);
		index = text.indexOf(GH.ProofStep.NEW_CELL);
	}
	cellTexts.push(text);

	var cell = document.createElement("td");
	cell.setAttribute('class', 'first-column');
	row.appendChild(cell);

	// Add the table cells into a row of the table.
	for (var i = 0; i < cellTexts.length; i++) {
		cell = document.createElement("td");
		var cellText = cellTexts[i];
		var classname = '';
		cell.setAttribute('class', classname);
		if (useLatex) {
			cell.innerHTML = '$$' + cellText + '$$';
		} else {
			cell.innerHTML = cellText;
		}
		row.appendChild(cell);
	}
	cell = document.createElement("td");
	cell.innerHTML = name;
	row.appendChild(cell);

	cell = document.createElement("td");
	cell.setAttribute('class', 'last-column');
	row.appendChild(cell);

	return row;
};

/**
 * Class name of the highlighted block.
 */
GH.ProofStep.ORANGE_BLOCK_ = 'orange-block';

/**
 * Class name to highlight a step in orange.
 */
GH.ProofStep.ORANGE_STEP_ = 'orange-step';
