GH.numUtil = {};

// Convert from a number to an s-expression string. Only the numbers 0 to 10 are defined
// in Ghilbert, so multi-digit numbers are formed by combining these digits according
// to the standard base-10 numbering system.
GH.numUtil.numToSexpString = function(num) {
	if (num < 0) {
		return '(-n ' + GH.numUtil.numToSexpString(-num) + ')';
	}
	
	// Handle single-digit numbers.
	if ((0 <= num) && (num <= 10)) {
		return '(' + num.toString() + ')';
	}
	
	// Find the value of the highest digit.
	var digit = 1;
	var value = num;
	while (value > 10) {
		value = Math.floor(value / 10);
		digit *= 10;
	}
	var upperDigit = value * digit;
	var remainder = num - upperDigit;   // Remainder stores the value of the lower digits.
	if (remainder == 0) {
		// If the lower digits are all zero, return the value of the upper digit.
		return '(* (' + value.toString() + ') ' + GH.numUtil.numToSexpString(digit) + ')';
	} else {
		// If there are lower digits, add the upper and lower digit numbers.
		var lowerDigits = GH.numUtil.numToSexpString(remainder);
		var upperDigits = GH.numUtil.numToSexpString(upperDigit);
		return '(+ ' + upperDigits + ' ' + lowerDigits + ') ';
	}
};

// Same as GH.numUtil.numToSexpString, but convert to a proper s-expression object type.
GH.numUtil.createNum = function(num) {
	if (num < 0) {
		alert('Negative numbers not yet supported.');
		return;
	}
	
	// Handle single-digit numbers.
	if ((0 <= num) && (num <= 10)) {
		return GH.sExpression.createDigit(num);
	}
	
	// Find the value of the highest digit.
	var digit = 1;
	var value = num;
	while (value > 10) {
		value = Math.floor(value / 10);
		digit *= 10;
	}
	var upperDigit = value * digit;
	var remainder = num - upperDigit;   // Remainder stores the value of the lower digits.
	if (remainder == 0) {
		// If the lower digits are all zero, return the value of the upper digit.
		var multiplier = GH.sExpression.createDigit(value);
		var base = GH.numUtil.createNum(digit);
		return GH.sExpression.createOperator('*', [multiplier, base]);
	} else {
		// If there are lower digits, add the upper and lower digit numbers.
		var lowerDigits = GH.numUtil.createNum(remainder);
		var upperDigits = GH.numUtil.createNum(upperDigit);
		return GH.sExpression.createOperator('+', [upperDigits, lowerDigits]);
	}
};

// TODO: Create a proper converter that works for numbers past 10.
GH.numUtil.numToFullSexp = function(num) {
	if (num > 10) {
		alert('numToFullSexp not specified for numbers above 10.');
	}
	return GH.sExpression.fromRaw([num.toString()]);
};


// The following functions numOfDigits, powerOfTen, decimalNumber are used in typesetting.
// Consider moving to typeset.js.

GH.numUtil.numOfDigits = function(num) {
	if (num >= 10) {
		return GH.numUtil.numOfDigits(num / 10) + 1;
	} else if ((0 < num) && (num < 1)) {
		return GH.numUtil.numOfDigits(num * 10) - 1;
	} else {
		return 1;
	}
};

// Returns the most significant digit. For example, for 536, returns 500.
GH.numUtil.mostSignificantDigit = function(num) {
	return num - num % Math.pow(10, GH.numUtil.numOfDigits(num) - 1);
};

GH.numUtil.isTen = function(str) {
	return ((str == '10') || (str == '10z') || (str == '10q'));
};

GH.numUtil.powerOfTen = function(sexp) {
	if (GH.numUtil.isTen(sexp[0])) {
		return 10;
	} else if (sexp[0] == '.1') {
		return 0.1;
	} else if ((sexp[0] == '*') && GH.numUtil.isTen(sexp[1][0])) {
		return 10 * GH.numUtil.powerOfTen(sexp[2]);
	} else if ((sexp[0] == '*') && (sexp[1][0] == '.1')) {
		return 0.1 * GH.numUtil.powerOfTen(sexp[2]);
	}
	return 0;
};

// Returns a number if the sexp is in the correct decimal format.
GH.numUtil.decimalNumber = function(sexp) {
	if (!sexp) {
		return NaN;
	}
	if (GH.typeset.typeOf(sexp) == 'string') {
		return NaN;
	}
	if (sexp[0].valueOf() == '1to1') {
		return NaN;
	}
	
	if (sexp[0] == '.1') {
		return 0.1;
	}

	var num = parseInt(sexp[0]);
	if ((0 <= num) && (num <= 10)) {
		return num;
	} else if (sexp[0] == '+') {
		var upperDigit = GH.numUtil.decimalNumber(sexp[1]);
		var lowerDigit = GH.numUtil.decimalNumber(sexp[2]);
		// Only allow one possible representation.
		//   The right side should not be zero. 40 is represented as 4 * 10, not 4 * 10 + 0.
		//   The left side must have more digits than the right.
		//   An addition can not appear on the left side.
		if ((GH.numUtil.numOfDigits(upperDigit) > GH.numUtil.numOfDigits(lowerDigit)) &&
			(lowerDigit != 0) && (sexp[1][0] != '+')){
			return upperDigit + lowerDigit;
		}
	} else if (sexp[0] == '*') {
		var digit = GH.numUtil.decimalNumber(sexp[1]);
		var base10 = GH.numUtil.powerOfTen(sexp[2]);
		// Only allow one possible representation. Ten is expressed as 10, not 1 * 10. Zero cannot be expressed as 0 * 10.
		if ((base10 != 0) && (1 < digit) && (digit <= 10) && ((digit != 10) || (base10 >= 1))) {
			return digit * base10;
		}
	}
	return NaN;
};

// Same as power of ten, but for GH.sExpressions.
GH.numUtil.powerOfTenSexp = function(sexp) {
	if (sexp.operator == '10') {
		return 10;
	} else {
		if ((sexp.operator == '*') && (sexp.operands[0].operator == '10')) {
			return 10 * GH.numUtil.powerOfTenSexp(sexp.operands[1]);
		}
	}
	return 0;
};

// Returns a number if the sexp is in the correct decimal format.
GH.numUtil.decimalNumberSexp = function(sexp) {
	if (GH.typeset.typeOf(sexp) == 'string') {
		return NaN;
	}

	var sign = 1;
	if (sexp.operator == '-n') {
		sign = -1;
		sexp = sexp.child();
		if ((sexp.operator == '-n') || (sexp.operator == '0')) {
			return NaN;  // Double Negatives and -0 are unacceptable.
		}
	}
	var num = parseInt(sexp.operator);
	if ((0 <= num) && (num <= 10)) {
		return sign * num;
	} else if (sexp.operator == '+') {
		var upperDigit = GH.numUtil.decimalNumberSexp(sexp.operands[0]);
		var lowerDigit = GH.numUtil.decimalNumberSexp(sexp.operands[1]);
		// Only allow one possible representation.
		//   The right side should not be zero. 40 is represented as 4 * 10, not 4 * 10 + 0.
		//   The left side must have more digits than the right.
		//   An addition can not appear on the left side.
		if ((GH.numUtil.numOfDigits(upperDigit) > GH.numUtil.numOfDigits(lowerDigit)) &&
			(lowerDigit != 0) &&
		    (sexp.operands[0].operator != '+')){
			return sign * (upperDigit + lowerDigit);
		}
	} else if (sexp.operator == '*') {
		var digit = GH.numUtil.decimalNumberSexp(sexp.operands[0]);
		var base10 = GH.numUtil.powerOfTenSexp(sexp.operands[1]);
		// Only allow one possible representation. Ten is expressed as 10, not 1 * 10. Zero cannot be expressed as 0 * 10.
		if ((base10 != 0) && (1 < digit) && (digit <= 10)) {
			return sign * digit * base10;
		}
	}
	return NaN;
};

GH.numUtil.isReduced = function(sexp) {
	return !isNaN(GH.numUtil.decimalNumberSexp(sexp));
};