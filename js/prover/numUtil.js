GH.numUtil = {};

// Convert from a number to an s-expression. Only the numbers 0 to 10 are defined
// in Ghilbert, so multi-digit numbers are formed by combining these digits according
// to the standard base-10 numbering system.
GH.numUtil.numToSexp = function(num) {
	if (num < 0) {
		alert('Negative numbers not yet supported.');
		return;
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
		return '(* (' + value.toString() + ') ' + GH.numUtil.numToSexp(digit) + ')';
	} else {
		// If there are lower digits, add the upper and lower digit numbers.
		var lowerDigits = GH.numUtil.numToSexp(remainder);
		var upperDigits = GH.numUtil.numToSexp(upperDigit);
		return '(+ ' + upperDigits + ' ' + lowerDigits + ') ';
	}
};
	
// Convert an s-expression into a number.
// Simply performs all the multiplication and additions within the expression.
GH.numUtil.sexpToNum = function(sexp) {
	if (sexp.operator_ == '*') {
		return GH.numUtil.sexpToNum(sexp.left()) * GH.numUtil.sexpToNum(sexp.right());
	} else if (sexp.operator_ == '+') {
		return GH.numUtil.sexpToNum(sexp.left()) + GH.numUtil.sexpToNum(sexp.right());
	} else {
		return parseInt(sexp.operator_);
	}
};

// Returns the number of digits of a number. The number can be in long form or short form.
GH.numUtil.getDigitNum = function(sexp) {
	if (sexp.operator_ == '+') {
		return GH.numUtil.getDigitNum(sexp.left());
	} else if (sexp.operator_ == '*') {
		return GH.numUtil.numOfDigits(GH.numUtil.sexpToNum(sexp.right()));
	} else {
		return 1;
	}
};


// The following functions numOfDigits, powerOfTen, decimalNumber are used in typesetting.
// Consider moving to typeset.js.

GH.numUtil.numOfDigits = function(num) {
	if (num >= 10) {
		return 1 + GH.numUtil.numOfDigits(num / 10);
	} else {
		return 1;
	}
};

GH.numUtil.powerOfTen = function(sexp) {
	if (sexp[0] == '10') {
		return 10;
	} else {
		if ((sexp[0] == '*') && (sexp[1][0] == '10')) {
			return 10 * GH.numUtil.powerOfTen(sexp[2]);
		}
	}
	return 0;
};

// Returns a number if the sexp is in the correct decimal format.
GH.numUtil.decimalNumber = function(sexp) {
	if (GH.typeOf(sexp) == 'string') {
		return NaN;
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
			(lowerDigit != 0) &&
		    (sexp[1][0] != '+')){
			return upperDigit + lowerDigit;
		}
	} else if (sexp[0] == '*') {
		var digit = GH.numUtil.decimalNumber(sexp[1]);
		var base10 = GH.numUtil.powerOfTen(sexp[2]);
		// Only allow one possible representation. Ten is expressed as 10, not 1 * 10. Zero cannot be expressed as 0 * 10.
		if ((base10 != 0) && (1 < digit) && (digit <= 10)) {
			return digit * base10;
		}
	}
	return NaN;
};

// Same as power of ten, but for GH.sExpressions.
GH.numUtil.powerOfTenSexp = function(sexp) {
	if (sexp.operator_ == '10') {
		return 10;
	} else {
		if ((sexp.operator_ == '*') && (sexp.operands_[0].operator_ == '10')) {
			return 10 * GH.numUtil.powerOfTenSexp(sexp.operands_[1]);
		}
	}
	return 0;
};

// Returns a number if the sexp is in the correct decimal format.
GH.numUtil.decimalNumberSexp = function(sexp) {
	if (GH.typeOf(sexp) == 'string') {
		return NaN;
	}

	var num = parseInt(sexp.operator_);
	if ((0 <= num) && (num <= 10)) {
		return num;
	} else if (sexp.operator_ == '+') {
		var upperDigit = GH.numUtil.decimalNumberSexp(sexp.operands_[0]);
		var lowerDigit = GH.numUtil.decimalNumberSexp(sexp.operands_[1]);
		// Only allow one possible representation.
		//   The right side should not be zero. 40 is represented as 4 * 10, not 4 * 10 + 0.
		//   The left side must have more digits than the right.
		//   An addition can not appear on the left side.
		if ((GH.numUtil.numOfDigits(upperDigit) > GH.numUtil.numOfDigits(lowerDigit)) &&
			(lowerDigit != 0) &&
		    (sexp.operands_[0].operator_ != '+')){
			return upperDigit + lowerDigit;
		}
	} else if (sexp.operator_ == '*') {
		var digit = GH.numUtil.decimalNumberSexp(sexp.operands_[0]);
		var base10 = GH.numUtil.powerOfTenSexp(sexp.operands_[1]);
		// Only allow one possible representation. Ten is expressed as 10, not 1 * 10. Zero cannot be expressed as 0 * 10.
		if ((base10 != 0) && (1 < digit) && (digit <= 10)) {
			return digit * base10;
		}
	}
	return NaN;
};