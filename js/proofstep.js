// Javascript for displaying proof steps. Steps are organized into proof blocks.
// by Paul Merrell, 2013


/**
 * Represents an s-expression.
 */
 GH.sExpression = function(operator, begin, end, isString) {
	this.parent = null;
	this.operator = operator;
	this.operands = [];
	this.siblingIndex = null;

	// If the expression comes from a string.	
	this.isString = isString;

	// Where the expression begins and ends within the textarea.
	this.begin = begin;
	this.end = end;

	// Set to true later, if the expression is a proven statement on the proof stack.
	this.isProven = false;
};

GH.sExpression.prototype.appendOperand = function(operand) {
	operand.parent = this;
	operand.siblingIndex = this.operands.length;
	this.operands.push(operand);
};

GH.sExpression.prototype.replaceOperand = function(operand, index) {
	operand.parent = this;
	operand.siblingIndex = index;
	this.operands[index] = operand;
};
 
GH.sExpression.fromRaw = function(expression) {
	var isString = (GH.typeOf(expression) == 'string');
	var operator = isString ? expression : expression[0];
	var result = new GH.sExpression(operator, expression.beg, expression.end, isString);

	if (!isString) {
		for (var i = 1; i < expression.length; i++) {
			result.appendOperand(GH.sExpression.fromRaw(expression[i]));
		}		
	}
	return result;
};

// Create an s-expression for a number between 0 and 10.
GH.sExpression.createDigit = function(num) {
	return new GH.sExpression(num.toString(), -1, -1, false);
};

// Create an s-expression for a variable.
GH.sExpression.createVariable = function(name) {
	return new GH.sExpression(name, -1, -1, true);
};

GH.sExpression.createOperator = function(operator, operands) {
	var result = new GH.sExpression(operator, -1, -1, false);
	for (var i = 0; i < operands.length; i++) {
		result.appendOperand(operands[i]);
	}
	return result;
};

GH.sExpression.prototype.getRoot = function() {
	var result = this;
	while(result.parent) {
		result = result.parent;
	}
	return result;
};

GH.sExpression.fromString = function(str) {
	return GH.sExpression.fromRaw(GH.sExpression.stringToExpression(str));
};

GH.sExpression.stringToExpression = function(str) {
	var depth = 0;
	var starts = [];
	var ends = [];
	var start = null;
	var end = null;
	
	for (var i = 0; i < str.length; i++) {
		var c = str.charAt(i);
		if (c != ' ') {
			if ((start == null) && (depth == 1)) {
				start = i;
			}
		}

		if (c == '(') {
			depth++;
		} else if (c == ')') {
			if ((depth == 1) && (start != null)) {
				end = i;
			}
			depth--;
		} else if (c == ' ') {
			if ((depth == 1) && (start != null)) {
				end = i;
			}
		}
		if (end != null) {
			starts.push(start);
			ends.push(end);
			start = null;
			end = null;
		}
	}
	if (starts.length > 0) {
		var expressions = [];
		for (var i = 0; i < starts.length; i++) {
			expressions.push(GH.sExpression.stringToExpression(str.substring(starts[i], ends[i])));
		}
		return expressions;
	} else {
		return str;
	}
};

// Construct the expression from the operator and operands.
GH.sExpression.prototype.getExpression = function() {
	if (this.isString) {
		return this.operator;
	} else {
		var expression = [];
		expression.push(this.operator);
		for (var i = 0; i < this.operands.length; i++) {
			expression.push(this.operands[i].getExpression());
		}
		return expression;
	}
};

GH.sExpression.prototype.copy = function() {
	var newCopy = GH.sExpression.fromRaw(this.getExpression());
	newCopy.isProven = this.isProven;
	return newCopy;
};

GH.sExpression.prototype.child = function () {
	if (this.operands.length > 1) {
		alert('Warning this expression has more than one child.');
	} else if (this.operands.length == 0) {
		alert('Warning this expression has no children.');
	}
	return this.operands[0];
};

GH.sExpression.prototype.left = function () {
	if (this.operands.length < 2) {
		alert('Warning this expression does not have a left side.');
	}
	return this.operands[0];
};

GH.sExpression.prototype.right = function () {
	if (this.operands.length < 2) {
		alert('Warning this expression does not have a right side.');
	}
	return this.operands[1];
};

GH.sExpression.prototype.replace = function () {
	if (this.operands.length < 2) {
		alert('Warning this expression does not have a right side.');
	}
	return this.operands[1];
};

// Find all matches to sexp within this expression.
GH.sExpression.prototype.findExp = function(sexp) {
	var result = [];
	if (this.equals(sexp)) {
		result.push(this);
	}
	for (var i = 0; i < this.operands.length; i++) {
		result = result.concat(this.operands[i].findExp(sexp));
	}
	return result;
};

GH.sExpression.stripParams = function(operator) {
	delete operator['beg'];
	delete operator['end'];
	return operator;
};

// Returns true is the s-expressions are identical.
GH.sExpression.prototype.equals = function(sexp) {
	var numOperands = this.operands.length;
	GH.sExpression.stripParams(this.operator);
	GH.sExpression.stripParams(sexp.operator);
	if (this.operator.length != sexp.operator.length) {
		return false;
	}
	for (var i = 0; i < this.operator.length; i++) {
		if (this.operator[i] != sexp.operator[i]) {
			return false;
		}
	}
	if ((numOperands != sexp.operands.length)) {
		return false;
	}
	for (var i = 0; i < numOperands; i++) {
		if (!this.operands[i].equals(sexp.operands[i])) {
			return false;
		}
	}
	return true;
};

/**
 * Displays an s-expression. If the cursor is inside of the s-expression, it is highlighted.
 * If the cursor is touching a particular symbol, that symbol is further hightlighted.
 */
GH.sExpression.prototype.display = function(stack, indentation, cursorPosition) {
	var text = GH.sexptohtmlHighlighted(this.getExpression(), cursorPosition);
	var isHighlighted = this.begin <= cursorPosition && cursorPosition <= this.end;
	// For now comment out the highlighting. Add it back in when we get a better editor like ACE or CodeMirror.
	//var mouseOverFunc = 'GH.setSelectionRange(' + this.begin + ',' + this.end +')';
	var mouseOverFunc = '';
	stack.appendChild(GH.ProofStep.stepToHtml(text, indentation, isHighlighted, false, mouseOverFunc, '', '', ''));
};

GH.sExpression.prototype.toString = function() {
	var result = [];	
	result.push(this.operator);
	for (var i = 0; i < this.operands.length; i++) {
		result.push(this.operands[i].toString());
	}
	result = result.join(' ');
	if (!this.isString) {
		result = '(' + result + ')';
	}
	return result;
};


GH.sExpression.prototype.getBeginning = function() {
	return this.begin;
};

/**
 * Proof steps are rendered into blocks containing one or more steps.
 * The steps can be organized into tables.
 */
GH.ProofBlock = function(classes) {
	this.classes = classes;
	this.steps = [];
	this.tableList = [];
};

// Render a proof block into html.
GH.ProofBlock.prototype.display = function(stack, cursorPosition) {
	var blockElement = document.createElement("div");
	blockElement.setAttribute('class', this.classes);
	this.addTables(blockElement, cursorPosition);
	stack.appendChild(blockElement);
	GH.ProofBlock.resizeTables(blockElement);
	return blockElement;
};

// Enlarge the last column of each table so that each row spans the width of the block.
GH.ProofBlock.resizeTables = function(block){
	for (var i = 0; i < block.childElementCount; i++) {
		var table = block.children[i];
		var lastCell = table.firstChild.lastChild;
		// The width is equal to the current width plus the difference between the block and the table width.
		var newWidth = block.offsetWidth - table.offsetWidth + parseInt(window.getComputedStyle(lastCell).width) - 20;
		lastCell.setAttribute('style', 'width: ' + newWidth);
	}
};

/**
 *  Add table elements to the block element. Every step is added to a table. The table list
 * contains groups of steps that are put into tables together. If there is no table list
 * for a step it is added into a one-line table.
 */ 
GH.ProofBlock.prototype.addTables = function(blockElement, cursorPosition) {
	var i = 0;
	while (i < this.steps.length) {
		var styled = false;
		for (var j = 0; (j < this.tableList.length) && !styled; j++) {
			if (this.tableList[j].begin == i) {
				this.addTable(this.tableList[j], blockElement, cursorPosition);
				i = this.tableList[j].end;
				styled = true;
			}
		}
		if (!styled) {
			this.addOneLineTable(i, blockElement, cursorPosition);
			i++;
		}
	}
};

// Add in a table to a block. Add in the styling for the table if
// it is present. Unstyled tables simply indent the hypotheses.
GH.ProofBlock.prototype.addTable = function(table, blockElement, cursorPosition) {
	var tableElement = document.createElement("table");
	tableElement.setAttribute('cellspacing', 0);

	var hasHighlightedStep = false;
	for (var i = table.begin; i < table.end; i++) {
		var step = this.steps[i];
		hasHighlightedStep = hasHighlightedStep || (step.classes_.match(new RegExp(GH.ProofStep.HIGHLIGHTED_STEP_)) != null);
		if (table.styling) {
			var styleIndex = i - table.begin;
			step.expression_ = GH.RenderableProofStep.styleExpression(table.styling[styleIndex], step.expression_);
		} else {
			step.classes_ += ' unstyled';
		}
		tableElement.appendChild(step.render(cursorPosition));
	}

	// Do not include the table border if there aren't any steps outside the table.
	if (table.end - table.begin < this.steps.length) {
		tableElement.className += 'table-border';
		if (!hasHighlightedStep) {
			// table-background is currently not used, but it might be later.
			tableElement.className += ' table-background';
		}
	}

	blockElement.appendChild(tableElement);
};

GH.ProofBlock.hideableOperators = ['<->', '->', '=', '=_', '<', '<='];

// Render the proof step. Hide parts on the left-side of an expression that are identical in the previous
// step.
GH.ProofBlock.renderVisibleParts = function(prevStep, step, tableElement, cursorPosition) {
	var isHidden = false;
	if (prevStep != null) {
		var hideableOperators = GH.ProofBlock.hideableOperators;
		var sexp = step.expression_;
		var prevSexp = prevStep.expression_;
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
	}

	if (isHidden) {
		var sexp = step.expression_;
		sexp[1] = ['htmlSpan', 'hidden', sexp[1]];   // Hide.
		tableElement.appendChild(step.render(cursorPosition));
		sexp[1] = sexp[1][2]; // Revert the s-expression.
	} else {
		tableElement.appendChild(step.render(cursorPosition));
	}
};

// Add a one line table with no border or styling to it.
GH.ProofBlock.prototype.addOneLineTable = function(i, blockElement, cursorPosition) {
	var tableElement = document.createElement("table");
	tableElement.setAttribute('cellspacing', 0);
	tableElement.className = 'table-no-border';

	var step = this.steps[i];
	var notLast = (i < this.steps.length - 1);
	var prevStep = (i > 0) && notLast ? this.steps[i - 1] : null;
	step.classes_ += ' unstyled';
	GH.ProofBlock.renderVisibleParts(prevStep, step, tableElement, cursorPosition);

	blockElement.appendChild(tableElement);
};


// Stores information for styling a table within a block.
GH.proofTable = function(styling, begin, end) {
	this.styling = styling;
	this.begin = begin;
	this.end = end;
};

/**
 * This represents a hierarchy of proof steps. A proofHierarchy either contains a single
 * proof step or it contains a list of children that are proofHierarchies themselves.
 * If it has children, the children contains all the proof steps between a pair of <d> and
 * </d> tags.
 *   - step: A single proof step or null.
 *   - begin: The cursor position where the hierarchy begins.
 */
GH.ProofHierarchy = function(step, begin) {
	this.parent = null;
	this.step = step;
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

// Return true, if the step at this part of the hierarchy is important at a particular cursor position.
GH.ProofHierarchy.prototype.isImportant = function(cursorPosition) {
	var position = this.findPosition();
	return position && (position.begin <= cursorPosition) && (cursorPosition <= position.end);
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
 *   isThm: Whether this is a theorem "thm" and not an axiom "stmt".
 *   depth: The depth of the proof step. Proof steps with a higher depth are less important and less visible.
 *   styling: The way to style the statements.
 */
GH.ProofStep = function(name, hypotheses, conclusion, begin, end, sExpressions, isError, isThm, styling) {
	this.name_ = name;
	this.hypotheses = hypotheses;
	this.conclusion = conclusion;
	this.begin = begin;
	this.end = end;
	this.isError = isError;
	this.isThm = isThm;
	this.substitution = null;
	this.styling = styling ? styling.table : null;
	this.title = styling && styling.title ? styling.title : '';
	this.hierarchy = null;

	this.sExpressions_ = [];
	for (var i = 0; i < sExpressions.length; i++) {
		this.sExpressions_.push(GH.sExpression.fromRaw(sExpressions[i][1]));
	}
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

// Returns true, if the position is inside this proof step or its descendants.
GH.ProofStep.prototype.isInsideBroad = function(position) {
	return ((this.getBeginning() <= position) && (position <= this.end));
};

// Returns true, if the position is inside this proof step.
GH.ProofStep.prototype.isInsideNarrow = function(position) {
	return ((this.begin <= position) && (position <= this.end))
};

// Render the proof step name in HTML.
GH.ProofStep.nameToHtml = function(name, title, isLink, isPrimary, isHypothesis) {
	if ((title == '') || (title === undefined)) {
		title = name;
	}

	var classes = 'proof-step-name';
	//classes += (isHypothesis ? ' display-on-hover'  : '');
	classes += (isPrimary    ? ' primary-step-name' : '');
	if (isLink) {
		return '<a href="/edit' + url + '/' + name + '"  class=\'' + classes + '\'>' + title + '</a>';
	} else {
		return '<span class=\'' + classes + '\'>' + title + '</span>';
	}
};

// Html for adding a new cell to a table.
GH.ProofStep.NEW_CELL  = '</td><td>';

/**
 * Returns the proof step displayed as a set of blocks.
 * This is the main entry point for displaying the proof steps.
 */
GH.ProofStep.prototype.displayStack = function(stack, summary, cursorPosition) {
	if (summary != '') {
		var summaryElement = document.createElement("div");
		summaryElement.innerHTML = summary;
		summaryElement.setAttribute('class', 'summary');
		stack.appendChild(summaryElement);
	}
	var blocks = this.display(false, cursorPosition);
	for (var i = 0; i < blocks.length; i++) {
		blocks[i].display(stack, cursorPosition);
	}
};

// Display the left over input arguments on the stack
GH.ProofStep.displayInputArguments = function(stack, inputArgs, expectedTypes, cursorPosition) {
	var rowCount = Math.max(inputArgs.length, expectedTypes.length && expectedTypes[0].length);
	if (rowCount == 0) {
		return;
	}
		
	var classes = 'proof-block input-args';
	var newBlock = new GH.ProofBlock(classes);
	var nameHtml = '<span class=proof-step-name>Input Argument' + ((inputArgs.length > 1) ? 's' : '') + '</span>';
	for (var i = 0; i < inputArgs.length; i++) {
		var iNameHtml = (i == 0) ? nameHtml : '';
		newBlock.steps.push(new GH.RenderableProofStep(GH.sexptohtml(inputArgs[i][1]), '', -1, -1, false, false, iNameHtml, 0));
	}
	var blockElement = newBlock.display(stack, cursorPosition);

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
			expectedContainer.appendChild(expectedElement );
			
			var actualContainer = document.createElement('td');
			actualContainer.setAttribute('class', 'type-container');
			var actualElement = document.createElement('span');
			actualElement.setAttribute('class', 'type-tag type-' + expectedTypes[1][i] + suffix);    // Actual types
			actualElement.innerHTML = expectedTypes[1][i];
			actualContainer.appendChild(actualElement);

			if (i >= blockElement.childNodes.length) {
				var tableElement = document.createElement('table');
				tableElement.setAttribute('class', 'table-no-border');
				blockElement.appendChild(tableElement);

				var rowElement = document.createElement('tr');				
				rowElement.setAttribute('class', 'proof-step-div unstyled');
				rowElement.appendChild(expectedContainer);
				rowElement.appendChild(actualContainer);
				tableElement.appendChild(rowElement);
			} else {
				var rowElement = blockElement.children[i].children[0];
				rowElement.insertBefore(expectedContainer, rowElement.children[0]);
				rowElement.insertBefore(  actualContainer, rowElement.children[1]);
			}
		}
		for (var i = 0; i < rowCount; i++) {
			var rowElement = blockElement.children[i].children[0];
			rowElement.lastChild.setAttribute('style', '')
		}
		GH.ProofBlock.resizeTables(blockElement);
	}
};

GH.ProofStep.createBlock = function(isGrayed, blocks) {
	var classes = 'proof-block' + (blocks.length == 0 ? ' ' + GH.ProofStep.PRIMARY_BLOCK_ : '') + (isGrayed ? ' gray-block' : '');
	var newBlock = new GH.ProofBlock(classes)
	return [newBlock];
};

GH.ProofStep.prototype.findImportantAncestors = function(cursorPosition) {
	var importantAncestors = [];
	for (var i = 0; i < this.hypotheses.length; i++) {
		if (this.hypotheses[i].hierarchy.isImportant(cursorPosition)) {
			importantAncestors.push(this.hypotheses[i]);
		}
	}
	if (importantAncestors.length == 0) {
		for (var i = 0; i < this.hypotheses.length; i++) {
			importantAncestors = importantAncestors.concat(this.hypotheses[i].findImportantAncestors(cursorPosition));
		}
	}
	return importantAncestors;
};

GH.ProofStep.prototype.findImportantAncestor = function(cursorPosition) {
	var importantAncestors = this.findImportantAncestors(cursorPosition);
	if (importantAncestors.length == 1) {
		return importantAncestors[0];
	} else {
		// Not sure if this is the best way to handle this case.
		return null;
	}
};

/**
 * Returns an array of strings recursively displaying each proof step.
 *   isGrayed: True if the proof-block is a gray color. The blocks alternate
 *       between white and gray blocks.
 *   cursorPosition: The cursor position in the text input box.
 */
GH.ProofStep.prototype.display = function(isGrayed, cursorPosition) {
	var lowestDepth = 1e10;
	var mostImportantHyp = null;
	for (var i = 0; i < this.hypotheses.length; i++) {
		var depth = this.hypotheses[i].hierarchy.getDepth();
		if (depth < lowestDepth) {
			lowestDepth = depth;
			if (this.hypotheses[i].hierarchy.isImportant(cursorPosition)) {
				mostImportantHyp = this.hypotheses[i];
			} else {
				mostImportantHyp = null;
			}		
		} else if (depth == lowestDepth) {
			mostImportantHyp = null;   // There can only be one most important hyp or none.
		}
	}
	if (!mostImportantHyp) {
		mostImportantHyp = this.findImportantAncestor(cursorPosition);
	}
	var isExpanded = this.isInsideNarrow(cursorPosition);
	var highlightedIndex = -1;
	for (var i = 0; i < this.hypotheses.length; i++) {
		if (this.hypotheses[i] != mostImportantHyp) {
			if ((this.hypotheses[i].isInsideNarrow(cursorPosition)) ||
 			    (this.hypotheses[i].isInsideBroad(cursorPosition) && (!mostImportantHyp || !mostImportantHyp.isInsideBroad(cursorPosition)))) {
				highlightedIndex = i;
				isExpanded = true;
			}
		}
	}

	var visibleHypotheses;
	if (isExpanded) {
		visibleHypotheses = this.hypotheses;
	} else if (mostImportantHyp) {
		visibleHypotheses = [mostImportantHyp];
	} else {
		visibleHypotheses = []
	}

	var oneHyp = !!mostImportantHyp;
	var blocks = [];
	var displayedHyps = [];

	// Display a new block for the hypothesis that the cursor is inside of, but only if that hypothesis
	// is not the one important hypothesis, since a single important hypothesis should be not be separated
	// to the current block.
	var highlighted = [];
	for (var i = 0; i < this.hypotheses.length; i++) {
		if (i == highlightedIndex) {
			var newBlocks = this.hypotheses[i].display(!isGrayed, cursorPosition);
			blocks = blocks.concat(newBlocks);
			highlighted.push(true);
		} else {
			highlighted.push(false);
		}
	}

	for (var i = 0; i < visibleHypotheses.length; i++) {
		var blockOffset = highlighted[i] ? 1 : 0;
		var isIndented = (visibleHypotheses.length > 1) && (visibleHypotheses[i] != mostImportantHyp);
		var prevOutsideTable = oneHyp && isExpanded && (visibleHypotheses[i] == mostImportantHyp);
		displayedHyps.push(visibleHypotheses[i].displayStep(isIndented, cursorPosition, true, highlighted[i], blockOffset, prevOutsideTable));
	}

	var newBlocks = [];
	// Add the hypotheses to an existing block if there is a most important hypotheses.
	if (mostImportantHyp) {
		newBlocks = mostImportantHyp.display(isGrayed, cursorPosition);
	}
	// Otherwise add the hypotheses to a new block.
	if (newBlocks.length == 0) {
		newBlocks = GH.ProofStep.createBlock(isGrayed, blocks);
	}
	var lastBlock = newBlocks[newBlocks.length - 1];
	if (lastBlock.steps.length > 0) {
		// Remove the conclusion. It gets added as a displayedHyp.
		lastBlock.steps.pop();
	}
	var oneHypSteps = lastBlock.steps.length;
	for (var i = 0; i < displayedHyps.length; i++) {
		lastBlock.steps.push(displayedHyps[i]);
	}
	blocks = blocks.concat(newBlocks);

    // Hook up the highlighted from the conclusion of a block to the step in the previous block.
	if (blocks.length > 1) {
		var steps = blocks[blocks.length - 2].steps;
		steps[steps.length - 1].setConclusionMouseOver(1, highlightedIndex + oneHypSteps);
	}

	// Add conclusion to the last block.
	lastBlock.steps.push(this.displayStep(false, cursorPosition, false, false, 0, false));

	// Only add the styling when none of the unimportant hypotheses are hidden.
	var numBlockHypotheses = lastBlock.steps.length;
	var numTableHypotheses = numBlockHypotheses - oneHypSteps;
	if (isExpanded) {
		var begin = numBlockHypotheses - numTableHypotheses;
		var styling = (this.styling && (numTableHypotheses == this.styling.length)) ? this.styling : null;
		lastBlock.tableList.push(new GH.proofTable(styling, begin, numBlockHypotheses));
	}

	return blocks;
};

/**
 * Display just this step without recursion.
 */
GH.ProofStep.prototype.displayStep = function(isIndented, cursorPosition, isHypothesis, isHighlighted, blockOffset, prevOutsideTable) {
	var inStep = this.begin <= cursorPosition && cursorPosition <= this.end;
	var classes = '';
	if (isIndented) {
		classes += ' ' + GH.ProofStep.INDENTED_STEP_;
	}
	if (this.Error_) {
		classes += ' error-in-step';
	}
	if (isHighlighted) {
		classes += ' ' + GH.ProofStep.HIGHLIGHTED_STEP_;
	}
	var nameHtml = GH.ProofStep.nameToHtml(this.name_, this.title, this.isThm, inStep, isHypothesis);
	return new GH.RenderableProofStep(this.conclusion, classes, this.begin, this.end, inStep, prevOutsideTable, nameHtml, blockOffset);
};

/**
 * Stores the data necessary to render a single line of the proof.
 */
GH.RenderableProofStep = function(expression, classes, begin, end, cursorInside, prevOutsideTable, nameHtml, blockOffset) {
	this.expression_ = expression;

	this.classes_ = classes;
	this.begin = begin;
	this.end = end;
	this.blockOffset_ = blockOffset;
	this.cursorInside = cursorInside;  // True if the cursor is inside this step.
	this.nameHtml_ = nameHtml;
	this.hypIndex_ = null;
	this.prevOutsideTable = prevOutsideTable;
};

/**
 * Add styling to an expression. The styling and the expression are both trees that we traverse
 * together. Whenever we encounter a node in the styling tree that has a "table" in it, we wrap
 * the expression there in a "table" node.
 */
GH.RenderableProofStep.styleExpression = function(styling, expression) {
	if (styling[0] == "table") {
		var styledExpression = GH.RenderableProofStep.styleExpression(styling[2], expression);
		return [styling[0], styling[1], styledExpression, styling[3]];
	} else if (styling[0] == 'htmlSpan') {
		var styledExpression = GH.RenderableProofStep.styleExpression(styling[2], expression);
		return [styling[0], styling[1], styledExpression];
	} else {
		if (typeof styling == 'string') {
			return expression;
		} else {
			var newExpression = [expression[0]];
			for (var i = 1; i < styling.length; i++) {
				newExpression.push(GH.RenderableProofStep.styleExpression(styling[i], expression[i]));
			}
		}
		return newExpression;
	}
};

/**
 * Sets the values needed for handling a mouseover of a conclusion. On mouseover, the conclusion
 * gets highlighted where it appears as a hypothesis.
 *   blockOffset: The number of blocks to traverse down to reach the block where the conclusion
 *                appears as a hypothesis.
 *   hypIndex: An index describing which hypotheses corresponds to the conclusion.
 */
GH.RenderableProofStep.prototype.setConclusionMouseOver = function(blockOffset, hypIndex) {
	this.blockOffset_ = blockOffset;
	this.hypIndex_ = hypIndex;
};

// Render the proof step into HTML.
GH.RenderableProofStep.prototype.render = function(cursorPosition) {
	var mouseOverFunc;
	if (this.hypIndex_ != null) {
		mouseOverFunc = 'GH.ProofStep.handleConclusionMouseOver(' + this.begin + ',' + this.end + ', ' + this.blockOffset_ + ', ' + this.hypIndex_ + ', this)';
	} else {
		mouseOverFunc = 'GH.ProofStep.handleMouseOver(' + this.begin + ',' + this.end + ', ' + this.blockOffset_ + ', ' + this.prevOutsideTable + ', this)';
	}
	var mouseOutFunc  = 'GH.ProofStep.handleMouseOut()';
	var clickFunc  = 'GH.ProofStep.handleClick(' + this.begin + ',' + this.end +', ' + this.cursorInside + ')';
	var text = GH.sexptohtmlHighlighted(this.expression_, cursorPosition);
	return GH.ProofStep.stepToHtml(text, this.classes_, mouseOverFunc, mouseOutFunc, clickFunc, this.nameHtml_);
};

// Display a proof step.
//   text: The text inside the step.
//   classes: The CSS classes applied to this step.
//   mouseOverFunc: The function to call on mouseover.
//   mouseOutFunc: The function to call on mouseout.
//   clickFunc: The function to call on a mouse click.
//   name: The name of the proofstep.
GH.ProofStep.stepToHtml = function(text, classes, mouseOverFunc, mouseOutFunc, clickFunc, name) {
	var row = document.createElement("tr");
	row.setAttribute('class', 'proof-step-div ' + classes);
	row.setAttribute('onmouseover', mouseOverFunc);
	row.setAttribute('onmouseout', mouseOutFunc);
	row.setAttribute('onclick', clickFunc);

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

	// Add the table cells into a row of the table.
	for (var i = 0; i < cellTexts.length; i++) {
		var cell = document.createElement("td");
		var cellText = cellTexts[i];
		var classname = '';

		// Add classes for the first and last column.
		// Add the name of the step onto the last column.
		if (i == 0) {
			classname = 'first-column';
		}
		cell.setAttribute('class', classname);
		cell.innerHTML = cellText;
		row.appendChild(cell);
	}		
	var cell = document.createElement("td");
	cell.setAttribute('class', 'last-column');
	cell.innerHTML = name;
	row.appendChild(cell);		

	return row;
};

// Get the previous step. If it has no previous siblings, check its previous cousin.
GH.ProofStep.getPreviousStep = function(step) {
	if (step.previousElementSibling) {
		return step.previousElementSibling;
	} else {
		var result = step.parentElement;
		result = result.previousElementSibling;
		if (!result) {
			return null;
		} else {
			return result.lastChild;
		}
	}
};

// Highlight in orange this proof step and any steps it directly depends on.
GH.ProofStep.orangeStep_ = function(prevOutsideTable, hoveredStep) {
	var step = hoveredStep;
	var block = step.parentElement.parentElement;
	var orangeSteps = [[step]];
	var numOrangeSteps = 1;
	if (!GH.ProofStep.hasClass_(step, GH.ProofStep.INDENTED_STEP_)) {
		var splitGroup;
		if (prevOutsideTable) {
			// Grab the first step above the table.
			splitGroup = (step.parentElement.firstChild != step);
			step = step.parentElement.previousElementSibling && step.parentElement.previousElementSibling.lastChild;
		} else {
			step = GH.ProofStep.getPreviousStep(step);
			splitGroup = false;
		}
		var done = false;
		while (step && !done) {
			if (splitGroup) {
				orangeSteps.push([step]);
				splitGroups = false;
			} else {
				orangeSteps[orangeSteps.length - 1].push(step);
			}
			numOrangeSteps++;
			done = done || (!GH.ProofStep.hasClass_(step, GH.ProofStep.INDENTED_STEP_));
			step = GH.ProofStep.getPreviousStep(step);
		}
	}

	// If all the steps in a block or a table are orange then orange the whole thing rather than the individual steps.
	var numBlockSteps = GH.ProofStep.getStepElements(block).length;
	if (numOrangeSteps == numBlockSteps) {
		GH.ProofStep.addClass_(block, GH.ProofStep.ORANGE_BLOCK_);
	} else if ((hoveredStep.parentElement.className.match(/table-border/) != null) && (hoveredStep == hoveredStep.parentElement.lastChild)) {
		GH.ProofStep.addClass_(hoveredStep.parentElement, 'orange-table');
	} else {
		for (var j = 0; j < orangeSteps.length; j++) {
			for (var i = 0; i < orangeSteps[j].length; i++) {
				var orangeStep = orangeSteps[j][i];
				if (i != 0) {
					GH.ProofStep.addClass_(orangeStep, GH.ProofStep.OPEN_BOTTOM_);
				}
				if (i != orangeSteps[j].length - 1) {
					GH.ProofStep.addClass_(orangeStep, GH.ProofStep.OPEN_TOP_);
				}
				GH.ProofStep.addClass_(orangeStep, GH.ProofStep.ORANGE_STEP_);
			}
		}
	}
};

GH.ProofStep.findCorrespondingBlock_ = function(step, blockOffset) {
	var correspondingBlock = null;
	if (blockOffset) {
		correspondingBlock = step.parentElement.parentElement;
		if (blockOffset > 0) {
			for (var i = 0; i < blockOffset; i++) {
				correspondingBlock = correspondingBlock.previousSibling;
			}
		} else {
			for (var i = 0; i < -blockOffset; i++) {
				correspondingBlock = correspondingBlock.nextSibling;
			}
		}
	}
	return correspondingBlock;
};

GH.ProofStep.handleMouseOver = function(start, end, blockOffset, prevOutsideTable, hoveredStep) {
	GH.ProofStep.orangeStep_(prevOutsideTable, hoveredStep);

	// For now comment out the highlighting. Add it back in when we get a better editor like ACE or CodeMirror.
	//GH.setSelectionRange(start, end);
	var highlightBlock = GH.ProofStep.findCorrespondingBlock_(hoveredStep, blockOffset);
	if (highlightBlock) {
		if (!GH.ProofStep.hasClass_(highlightBlock, GH.ProofStep.ORANGE_BLOCK_)) {
			GH.ProofStep.addClass_(highlightBlock, GH.ProofStep.ORANGE_BLOCK_);
		}
	}
};

GH.ProofStep.getStepElements = function(blockElement) {
	var steps = [];
	for (var j = 0; j < blockElement.childElementCount; j++) {
		var table = blockElement.children[j];
		for (var k = 0; k < table.childElementCount; k++) {
			steps.push(table.children[k]);
		}
	}
	return steps;
};

// When a conclusion of a block is moused over, this highlights the same statement as a hypothesis
// in the previous block.
GH.ProofStep.handleConclusionMouseOver = function(start, end, blockOffset, hypIndex, hoveredStep) {
	GH.ProofStep.handleMouseOver(start, end, 0, false, hoveredStep);
	var highlightBlock = GH.ProofStep.findCorrespondingBlock_(hoveredStep, -blockOffset);
	if (highlightBlock) {
		var steps = GH.ProofStep.getStepElements(highlightBlock);
		GH.ProofStep.addClass_(steps[hypIndex], GH.ProofStep.ORANGE_STEP_);
	}
};

// Returns true if an element has a particular class.
GH.ProofStep.hasClass_ = function(element, className) {
	return element.className.match(new RegExp(className));
};

// Add a class to an element.
GH.ProofStep.addClass_ = function(element, className) {
	if (!GH.ProofStep.hasClass_(element, className)) {
		element.className += ' ' + className;
	}
};

// Remove a class from an element.
GH.ProofStep.removeClass_ = function(element, className) {
	element.className = element.className.replace(new RegExp(' ' + className), '');
};

// Handle a mouse out event. Remove all the highlighting that was added in the mouseover handling.
GH.ProofStep.handleMouseOut = function() {
	var stack = document.getElementById('stack');
	for (var i = 0; i < stack.childElementCount; i++) {
		var block = stack.children[i];
		GH.ProofStep.removeClass_(block, GH.ProofStep.ORANGE_BLOCK_);
		for (var j = 0; j < block.childElementCount; j++) {
			var table = block.children[j];
			GH.ProofStep.removeClass_(table, 'orange-table');
			for (var k = 0; k < table.childElementCount; k++) {
				var step = table.children[k];
				GH.ProofStep.removeClass_(step, GH.ProofStep.ORANGE_STEP_);
				GH.ProofStep.removeClass_(step, GH.ProofStep.OPEN_TOP_);
				GH.ProofStep.removeClass_(step, GH.ProofStep.OPEN_BOTTOM_);
			}
		}
	}
};

// Handle clicking on a proof step.
GH.ProofStep.handleClick = function(start, end, incrementClicks) {
	GH.setSelectionRange(start, end);
	window.direct.update(true);
};

/**
 * Class name of the highlighted step.
 */
GH.ProofStep.HIGHLIGHTED_STEP_ = 'highlighted-step';

/**
 * Class name of the indented step in a proof block. The hypotheses are indented.
 */
GH.ProofStep.INDENTED_STEP_ = 'indented-step';

/**
 * Class name of the highlighted block.
 */
GH.ProofStep.ORANGE_BLOCK_ = 'orange-block';

/**
 * Class name of the primary block.
 */
GH.ProofStep.PRIMARY_BLOCK_ = 'primary-block';

/**
 * Class name to highlight a step in orange.
 */
GH.ProofStep.ORANGE_STEP_ = 'orange-step';

/**
 * Class name that indicates that the border is open at the bottom.
 */
GH.ProofStep.OPEN_BOTTOM_ = 'open-bottom';

/**
 * Class name that indicates that the border is open at the top.
 */
GH.ProofStep.OPEN_TOP_ = 'open-top';
