// Javascript for displaying proof steps. Steps are organized into proof blocks.
// by Paul Merrell, 2013


/**
 * Represents an s-expression.
 */
GH.sExpression = function(expression, parent, siblingIndex) {
	// TODO: Maybe delete this.expression_.
	this.expression_ = expression;
	this.operator_ = expression[0];
	this.operands_ = [];
	for (var i = 1; i < expression.length; i++) {
		this.operands_.push(new GH.sExpression(expression[i], this, i - 1));
	}
	// Where the expression begins and ends within the textarea.
	this.begin_ = expression.beg;
	this.end_ = expression.end;
	this.parent_ = parent;
	this.siblingIndex_ = siblingIndex;
	this.hasParentheses_ = (GH.typeOf(expression) != 'string');
};

GH.sExpression.fromString = function(str) {
	return new GH.sExpression(GH.sExpression.stringToExpression(str));
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

GH.sExpression.prototype.copy = function(newParent) {
	return new GH.sExpression(this.expression_, newParent, this.siblingIndex);
};

GH.sExpression.prototype.child = function () {
	if (this.operands_.length > 1) {
		alert('Warning this expression has more than one child.');
	} else if (this.operands_.length == 0) {
		alert('Warning this expression has no children.');
	}
	return this.operands_[0];
};

GH.sExpression.prototype.left = function () {
	if (this.operands_.length < 2) {
		alert('Warning this expression does not have a left side.');
	}
	return this.operands_[0];
};

GH.sExpression.prototype.right = function () {
	if (this.operands_.length < 2) {
		alert('Warning this expression does not have a right side.');
	}
	return this.operands_[1];
};

GH.sExpression.prototype.replace = function () {
	if (this.operands_.length < 2) {
		alert('Warning this expression does not have a right side.');
	}
	return this.operands_[1];
};

// Find all matches to sexp within this expression.
GH.sExpression.prototype.findExp = function(sexp) {
	var result = [];
	if (this.equals(sexp)) {
		result.push(this);
	}
	for (var i = 0; i < this.operands_.length; i++) {
		result = result.concat(this.operands_[i].findExp(sexp));
	}
	return result;
};

GH.sExpression.stripParams = function(operator) {
	delete operator['beg'];
	delete operator['end'];
	return operator;
}

// Returns true is the s-expressions are identical.
GH.sExpression.prototype.equals = function(sexp) {
	var numOperands = this.operands_.length;
	GH.sExpression.stripParams(this.operator_);
	GH.sExpression.stripParams(sexp.operator_);
	if (this.operator_.length != sexp.operator_.length) {
		return false;
	}
	for (var i = 0; i < this.operator_.length; i++) {
		if (this.operator_[i] != sexp.operator_[i]) {
			return false;
		}
	}
	if ((numOperands != sexp.operands_.length)) {
		return false;
	}
	for (var i = 0; i < numOperands; i++) {
		if (!this.operands_[i].equals(sexp.operands_[i])) {
			return false;
		}
	}
	return true;
};

/**
 * Displays an s-expression. If the cursor is inside of the s-expression, it is highlighted.
 * If the cursor is touching a particular symbol, that symbol is further hightlighted.
 */
GH.sExpression.prototype.display = function(indentation, cursorPosition) {
	var text = GH.sexptohtmlHighlighted(this.expression_, cursorPosition);
	var isHighlighted = this.begin_ <= cursorPosition && cursorPosition <= this.end_;
	// For now comment out the highlighting. Add it back in when we get a better editor like ACE or CodeMirror.
	//var mouseOverFunc = 'GH.setSelectionRange(' + this.begin_ + ',' + this.end_ +')';
	var mouseOverFunc = '';
	return GH.ProofStep.stepToHtml(text, indentation, isHighlighted, false, mouseOverFunc, '', '', '');
};

GH.sExpression.prototype.toString = function() {
	var result = [];	
	result.push(this.operator_);
	for (var i = 0; i < this.operands_.length; i++) {
		result.push(this.operands_[i].toString());
	}
	result = result.join(' ');
	if (this.hasParentheses_) {
		result = '(' + result + ')';
	}
	return result;
};


GH.sExpression.prototype.getBeginning = function() {
	return this.begin_;
};

/**
 * Proof steps are rendered into blocks. A block may contain multiple hypotheses and contains a
 * sequence of one or more conclusions.
 */
GH.ProofBlock = function(classes) {
	this.classes = classes;
	this.hypotheses = [];
	this.conclusions = [];
};

// Render a proof block into html.
GH.ProofBlock.prototype.display = function() {
	html = [];
	html.push("<div class=\"" + this.classes + "\">");
	for (var i = 0; i < this.hypotheses.length; i++) {
		html.push(this.hypotheses[i].render());
	}
	for (var i = 0; i < this.conclusions.length; i++) {
		html.push(this.conclusions[i].render());
	}
	html.push("</div>");
	return html;
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
 */
GH.ProofStep = function(name, hypotheses, conclusion, begin, end, sExpressions, isError, isThm, depth) {
	this.name_ = name;
	this.hypotheses_ = hypotheses;
	this.conclusion_ = conclusion;
	this.begin_ = begin;
	this.end_ = end;
	this.isError_ = isError;
	this.isThm_ = isThm;
	this.depth = depth;

	this.sExpressions_ = [];
	for (var i = 0; i < sExpressions.length; i++) {
		this.sExpressions_.push(new GH.sExpression(sExpressions[i][1], null, 0));
	}
};

/**
 * Find the beginning of the proof step this includes the beginning of any hypotheses
 * that this step depends on.
 */
GH.ProofStep.prototype.getBeginning = function() {
	if (this.hypotheses_.length > 0) {
		return this.hypotheses_[0].getBeginning();
	} else {
		if (this.sExpressions_.length > 0) {
			return this.sExpressions_[0].getBeginning();
		} else {
			return this.begin_;
		}
	}
};

// Returns true, if the position is inside this proof step.
GH.ProofStep.prototype.isInside = function(position) {
	return ((this.getBeginning() <= position) && (position <= this.end_));
};

// Render the proof step name in HTML.
GH.ProofStep.nameToHtml = function(text, isLink, isPrimary, isHypothesis) {
	var classes = 'proof-step-name';
	classes += (isHypothesis ? ' display-on-hover'  : '');
	classes += (isPrimary    ? ' primary-step-name' : '');
	if (isLink) {
		return '<a href="/edit/peano/peano_thms.gh/' + text + '"  class=\'' + classes + '\'>' + text + '</a>';
	} else {
		return '<span class=\'' + classes + '\'>' + text + '</span>';
	}
};

// Steps with lower depth are more important. Returns true if the depth is below
// the maxDepth threshold.
GH.ProofStep.prototype.isImportant = function(maxDepth) {
	return (this.depth <= maxDepth);
};

// Find the minimum depth within this proof step. This includes the current step and any hypotheses it depends upon.
GH.ProofStep.prototype.minRecursiveDepth = function() {
	var depth = this.depth;
	if (depth > 0) {
		for (var i = 0; i < this.hypotheses_.length; i++) {
			depth = Math.min(depth, this.hypotheses_[i].minRecursiveDepth());
		}
	}
	return depth;
};

// Find the maximum depth within this proof step. This includes the current step and any hypotheses it depends upon.
GH.ProofStep.prototype.maxRecursiveDepth = function() {
	var depth = this.depth;
	for (var i = 0; i < this.hypotheses_.length; i++) {
		depth = Math.max(depth, this.hypotheses_[i].maxRecursiveDepth());
	}
	return depth;
};

// Returns the step having a lower depth than maxDepth.
GH.ProofStep.prototype.getImportantSteps = function(maxDepth) {
	var importantSteps = [];
	// Returns the current step if it is important enough. Otherwise, search through the hypotheses.
	if (this.isImportant(maxDepth)) {
		importantSteps.push(this);
	} else {
		for (var i = 0; i < this.hypotheses_.length; i++) {
			importantSteps = importantSteps.concat(this.hypotheses_[i].getImportantSteps(maxDepth));
		}
	}
	return importantSteps;
};

// Returns the hypotheses having a lower depth than maxDepth.
GH.ProofStep.prototype.getImportantHypotheses_ = function(maxDepth) {
	var importantHypotheses = [];
	for (var i = 0; i < this.hypotheses_.length; i++) {
		importantHypotheses = importantHypotheses.concat(this.hypotheses_[i].getImportantSteps(maxDepth));
	}
	return importantHypotheses;
};

// Returns the important hypotheses by the cursor position and the maxDepth.
GH.ProofStep.prototype.getImportantHypothesesByPosition_ = function(cursorPosition, maxDepth) {
	var importantHypotheses;
	if ((cursorPosition > this.end_) || (cursorPosition < this.getBeginning())) {
		importantHypotheses = this.getImportantHypotheses_(this.depth);
	} else if ((this.begin_ <= cursorPosition) && (cursorPosition <= this.end_)) {
		var depth = maxDepth;
		//depth = Math.max(this.depth, maxDepth);
		importantHypotheses = this.getImportantHypotheses_(depth);
		while ((importantHypotheses.length == 0) && (this.hypotheses_.length > 0)) {
			depth++;
			importantHypotheses = this.getImportantHypotheses_(depth);
		}
	} else {
		var depth = 0;
		var depthFound = false;
		while (!depthFound && (depth <= this.maxRecursiveDepth())) {
			importantHypotheses = this.getImportantHypotheses_(depth);
			for (var i = 0; i < importantHypotheses.length; i++) {
				if (importantHypotheses[i].isInside(cursorPosition)) {
					depthFound = true;
				}
			}
			depth++;
		}
	}
	return importantHypotheses;
};

/**
 * Returns the proof step displayed as a set of blocks.
 * This is the main entry point for displaying the proof steps.
 */
GH.ProofStep.prototype.displayStack = function(cursorPosition, maxDepth) {
	var blocks = this.display(false, cursorPosition, maxDepth);
	var html = [];
	for (var i = 0; i < blocks.length; i++) {
		html = html.concat(blocks[i].display());
	}
	return html;
};

/**
 * Returns an array of strings recursively displaying each proof step.
 *   isGrayed: True if the proof-block is a gray color. The blocks alternate
 *       between white and gray blocks.
 *   cursorPosition: The cursor position in the text input box.
 *   maxDepth: The maximum visible depth. Steps having a depth above maxDepth are not displayed.
 */
GH.ProofStep.prototype.display = function(isGrayed, cursorPosition, maxDepth) {
	var importantHypotheses = this.getImportantHypothesesByPosition_(cursorPosition, maxDepth);
	var depth = 0;
	for (var i = 0; i < importantHypotheses.length; i++) {
		depth = Math.max(depth, importantHypotheses[i].depth);
	}

	var oneHyp = (importantHypotheses.length == 1);
	var blocks = [];
	var displayedHyps = [];
	var numBlocks = 0;

	// Display details on certain hypotheses.
	for (var i = 0; i < importantHypotheses.length; i++) {
		// Display details on a hypothesis if it's the only one or if the cursor is inside of it or if it has lower depth.
		if (oneHyp || (importantHypotheses[i].isInside(cursorPosition)) || (depth > importantHypotheses[i].minRecursiveDepth())) {
			var newIsGrayed = oneHyp ? isGrayed : !isGrayed;
			blocks.push(importantHypotheses[i].display(newIsGrayed, cursorPosition, maxDepth));
			numBlocks += (blocks[blocks.length - 1].length);
		} else {
			blocks.push([]);
		}
	}

	// Display each important hypothesis. Hook up the highlighting between it and its corresponding proof blocks.
	for (var i = 0; i < importantHypotheses.length; i++) {
		var isHighlighted = (blocks[i].length > 0);
		var blockOffset = 0;
		if (isHighlighted) {
			// The block offset is the number of blocks to tranverse to reach the corresponding block for this step.
			// It is equal to the number of blocks for all the important hypotheses beyond this one plus one.
			blockOffset = 1;
			for (j = i + 1; j < importantHypotheses.length; j++) {
				blockOffset += blocks[j].length;
			}
			if (!oneHyp) {
				var conclusions = blocks[i][blocks[i].length - 1].conclusions;
				conclusions[conclusions.length - 1].setConclusionMouseOver(blockOffset, i);
			}
		}
		displayedHyps.push(importantHypotheses[i].displayStep(!oneHyp, cursorPosition, true, isHighlighted, blockOffset));
	}

	// Display the s-expressions. Commented out for now.
	/*for (var i = 0; i < this.sExpressions_.length; i++) {
		proofStepHtml.push(this.sExpressions_[i].display(indentation + 1, cursorPosition));
	}*/

	// Create a new block if there are multiple hypotheses.
	if (!oneHyp) {
		var classes = 'proof-block' + (numBlocks == 0 ? ' ' + GH.ProofStep.PRIMARY_BLOCK_ : '') + (isGrayed ? ' gray-block' : '');
		var newBlock = new GH.ProofBlock(classes)
		newBlock.hypotheses = displayedHyps;
		blocks.push([newBlock]);
	}
	// Add the conclusion onto whatever is the last block.
	var lastBlockGroup = blocks[blocks.length - 1];
	var lastBlock = lastBlockGroup[lastBlockGroup.length - 1];
	lastBlock.conclusions.push(this.displayStep(false, cursorPosition, false, false, 0));

	// Flatten an array of an array of blocks into just an array of blocks.
	var flattenedBlocks = [];
	for (var i = 0; i < blocks.length; i++) {
		for (var j = 0; j < blocks[i].length; j++) {
			flattenedBlocks.push(blocks[i][j]);
		}
	}
	return flattenedBlocks;
};

/**
 * Display just this step without recursion.
 */
GH.ProofStep.prototype.displayStep = function(isIndented, cursorPosition, isHypothesis, isHighlighted, blockOffset) {
	var text = GH.sexptohtmlHighlighted(this.conclusion_, cursorPosition);
	var inStep = this.begin_ <= cursorPosition && cursorPosition <= this.end_;
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
	var nameHtml = GH.ProofStep.nameToHtml(this.name_, this.isThm_, inStep, isHypothesis);
	return new GH.RenderableProofStep(text, classes, this.begin_, this.end_, nameHtml, blockOffset);
};

/**
 * Stores the data necessary to render a single line of the proof.
 */
GH.RenderableProofStep = function(text, classes, begin, end, nameHtml, blockOffset) {
	this.text_ = text;
	this.classes_ = classes;
	this.begin_ = begin;
	this.end_ = end;
	this.blockOffset_ = blockOffset;
	this.nameHtml_ = nameHtml;
	this.hypIndex_ = null;
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
GH.RenderableProofStep.prototype.render = function() {
	var mouseOverFunc;
	if (this.hypIndex_ != null) {
		mouseOverFunc = 'GH.ProofStep.handleConclusionMouseOver(' + this.begin_ + ',' + this.end_ + ', ' + this.blockOffset_ + ', ' + this.hypIndex_ + ', this)';
	} else {
		mouseOverFunc = 'GH.ProofStep.handleMouseOver(' + this.begin_ + ',' + this.end_ +', ' + this.blockOffset_ + ', this)';
	}
	var mouseOutFunc  = 'GH.ProofStep.handleMouseOut()';
	var clickFunc  = 'GH.ProofStep.handleClick(' + this.begin_ + ',' + this.end_ +', this)';
	return GH.ProofStep.stepToHtml(this.text_, this.classes_, mouseOverFunc, mouseOutFunc, clickFunc, this.nameHtml_);
};

// Display a proof step.
//   text: The text inside the step.
//   classes: The CSS classes applied to this step.
//   mouseOverFunc: The function to call on mouseover.
//   mouseOutFunc: The function to call on mouseout.
//   name: The name of the proofstep.
//   proofStepHtml: The full list of proof steps. The output goes here.
GH.ProofStep.stepToHtml = function(text, classes, mouseOverFunc, mouseOutFunc, clickFunc, name) {
	var html = '';
	html += '<div class=\'proof-step-div' + classes + '\' ';
	if (mouseOverFunc != '') {
		html += 'onmouseover=\'' + mouseOverFunc + '\' ';
	}
	if (mouseOutFunc != '') {
		html += 'onmouseout=\''  + mouseOutFunc  + '\' ';
	}
	if (clickFunc != '') {
		html += 'onclick=\''  + clickFunc  + '\' ';
	}
	html += '\'>';
	html += text;
	html += name;
	html += '</div>\n';
	return html;
};

// Highlight in orange this proof step and any steps it directly depends on.
GH.ProofStep.orangeStep_ = function(step) {
	var block = step.parentElement;
	var orangeSteps = [step];
	if (!GH.ProofStep.hasClass_(step, GH.ProofStep.INDENTED_STEP_)) {
		step = step.previousElementSibling;
		if (step) {
			if (GH.ProofStep.hasClass_(step, GH.ProofStep.INDENTED_STEP_)) {
				while (step) {
					orangeSteps.push(step);
					step = step.previousElementSibling;
				}
			} else {
				orangeSteps.push(step);
			}
		}
	}

	if (orangeSteps.length == block.childElementCount) {
		GH.ProofStep.addClass_(block, GH.ProofStep.HIGHLIGHTED_BLOCK_);
	} else {
		for (var i = 0; i < orangeSteps.length; i++) {
			if (i != 0) {
				GH.ProofStep.addClass_(orangeSteps[i], GH.ProofStep.OPEN_BOTTOM_);
			}
			if (i != orangeSteps.length - 1) {
				GH.ProofStep.addClass_(orangeSteps[i], GH.ProofStep.OPEN_TOP_);
			}
			GH.ProofStep.addClass_(orangeSteps[i], GH.ProofStep.ORANGE_STEP_);
		}
	}
};

GH.ProofStep.findCorrespondingBlock_ = function(step, blockOffset) {
	var correspondingBlock = null;
	if (blockOffset) {
		correspondingBlock = step.parentElement;
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

GH.ProofStep.handleMouseOver = function(start, end, blockOffset, hoveredStep) {
	GH.ProofStep.orangeStep_(hoveredStep);

	// For now comment out the highlighting. Add it back in when we get a better editor like ACE or CodeMirror.
	//GH.setSelectionRange(start, end);
	var highlightBlock = GH.ProofStep.findCorrespondingBlock_(hoveredStep, blockOffset);
	if (highlightBlock) {
		if (!GH.ProofStep.hasClass_(highlightBlock, GH.ProofStep.HIGHLIGHTED_BLOCK_)) {
			GH.ProofStep.addClass_(highlightBlock, GH.ProofStep.HIGHLIGHTED_BLOCK_);
		}
	}
};

GH.ProofStep.handleConclusionMouseOver = function(start, end, blockOffset, hypIndex, hoveredStep) {
	GH.ProofStep.handleMouseOver(start, end, 0, hoveredStep);
	var highlightBlock = GH.ProofStep.findCorrespondingBlock_(hoveredStep, -blockOffset);
	if (highlightBlock) {
		var step = highlightBlock.children[hypIndex];
		GH.ProofStep.addClass_(step, GH.ProofStep.ORANGE_STEP_);
	}
};

// Returns true if an element has a particular class.
GH.ProofStep.hasClass_ = function(element, className) {
	return element.className.match(new RegExp(className));
};

// Add a class to an element.
GH.ProofStep.addClass_ = function(element, className) {
	element.className += ' ' + className;
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
		GH.ProofStep.removeClass_(block, GH.ProofStep.HIGHLIGHTED_BLOCK_);
		for(var j = 0; j < block.childElementCount; j++) {
			var step = block.children[j];
			GH.ProofStep.removeClass_(step, GH.ProofStep.ORANGE_STEP_);
			GH.ProofStep.removeClass_(step, GH.ProofStep.OPEN_TOP_);
			GH.ProofStep.removeClass_(step, GH.ProofStep.OPEN_BOTTOM_);
		}
	}
};

// Handle clicking on a proof step.
GH.ProofStep.handleClick = function(start, end, clickedStep) {
	GH.setSelectionRange(start, end);
	var clickedBlock = clickedStep.parentElement;
	if ((GH.ProofStep.hasClass_(clickedBlock, GH.ProofStep.PRIMARY_BLOCK_)) &&
	    (!GH.ProofStep.hasClass_(clickedStep, GH.ProofStep.INDENTED_STEP_))) {
		window.direct.incrementMaxDepth();
	} else {
		window.direct.resetMaxDepth();
	}
	window.direct.update();
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
GH.ProofStep.HIGHLIGHTED_BLOCK_ = 'highlighted-block';

/**
 * Class name of the primary block.
 */
GH.ProofStep.PRIMARY_BLOCK_ = 'primary-block';

/**
 * Class name to highlight a step in orange.
 */
GH.ProofStep.ORANGE_STEP_ = 'proof-step-orange';

/**
 * Class name that indicates that the border is open at the bottom.
 */
GH.ProofStep.OPEN_BOTTOM_ = 'open-bottom';

/**
 * Class name that indicates that the border is open at the top.
 */
GH.ProofStep.OPEN_TOP_ = 'open-top';
