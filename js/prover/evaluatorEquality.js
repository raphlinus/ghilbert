// This file is now storing broken code that needs to be fixed. 
// It is not hooked up to anything.

GH.Prover.prototype.oneDigitNotZero = function(sexp) {
	var predecessor = parseInt(sexp.operator_) - 1;	
	this.print(['(' + predecessor + ')'], 'pa_ax1');
	var result = this.getLast().child().right();

	this.print(['(' + predecessor + ')'], 'a1suc');
	result = this.replace(result, this.getLast())
	this.successorLeft(result);
};

GH.Prover.prototype.oneDigitInequality = function(leftNum, rightNum) {
	if (leftNum >= rightNum) {
		// Not written yet.
		return;
	}
	var diff = rightNum - leftNum;
	this.println('x (' + diff + ') tyex');
	this.println('x (' + diff + ') (' + leftNum + ') addeq2');
	
	var result = this.getLast().right().right();
	result = this.replaceWith(this.addSingleDigits, result);
	
	this.println('x 19.22i');
	this.println('ax-mp');

    this.println('(' + leftNum + ') (' + rightNum + ') x df-le');
    this.println('mpbir');  // Could also use replace.

    // TODO: Put this is a not equal function
		// TODO: Don't use a fake s-expression.
		var fakeSexp = {operator_: diff};
		this.oneDigitNotZero(fakeSexp);
		this.println('(0) (' + leftNum + ') (' + diff + ') addcan')
		this.println('mtbir');
	
		result = this.getLast().child();
		result = this.replaceRight(this.addSingleDigits, result);
		result = this.additiveIdentity(result.left());
		
	this.println('pm3.2i');
	this.println('(' + leftNum + ') (' + rightNum + ') df-lt');
	this.println('bicomi');
	this.println('mpbi');
};