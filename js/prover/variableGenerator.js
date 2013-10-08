GH.Prover.variableGenerator = function() {
	this.usedVariables = { wff: 0, nat: 0, bind: 0, set: 0};
};
	

GH.Prover.variableGenerator.VARIABLE_NAMES = {
	wff: ['ph', 'ps', 'ch', 'th', 'ta', 'et', 'zi', 'si', 'ph\'', 'ps\'', 'ch\'', 'th\'', 'ta\''],
	nat: ['A', 'B', 'C', 'D', 'A\'', 'B\'', 'C\'', 'D\'', 'A0', 'A1', 'A2', 'A3'], 
	bind: ['x', 'y', 'z', 'v', 'w\'', 'x\'', 'y\'', 'z\'', 'v\'', 'w\''],
	set: ['S', 'T', 'U', 'V', 'S0', 'S1', 'S2', 'S3', 'S4', 'S5', 'S6', 'S7', 'S8', 'S9']
};

GH.Prover.variableGenerator.prototype.generate = function(type) {
	if (GH.Prover.variableGenerator.VARIABLE_NAMES[type].length <= this.usedVariables[type]) {
		alert('No more unused variable names.');
	}
	var result = GH.Prover.variableGenerator.VARIABLE_NAMES[type][this.usedVariables[type]];
	this.usedVariables[type]++;
	return result;
};

GH.Prover.variableGenerator.isVariable = function(name) {
	var varNames = GH.Prover.variableGenerator.VARIABLE_NAMES;
	return ((varNames.wff.indexOf(name) >= 0) ||
	        (varNames.nat.indexOf(name) >= 0) ||
	        (varNames.bind.indexOf(name) >= 0) ||
	        (varNames.set.indexOf(name) >= 0));
};

GH.Prover.variableGenerator.generateUnused = function(sexp, type) {
	var names = GH.Prover.variableGenerator.VARIABLE_NAMES[type];
	var isUsed = [];
	for (var i = 0; i < names.length; i++) {
		isUsed.push(false);
	}
	GH.Prover.variableGenerator.determineUse(sexp, names, isUsed);
	for (var i = 0; i < isUsed.length; i++) {
		if (!isUsed[i]) {
			return names[i];
		}
	}
	alert('All the variable names have been used up.');
};

GH.Prover.variableGenerator.determineUse = function(sexp, names, isUsed) {
	if (sexp.operands.length == 0) {
		for (var i = 0; i < names.length; i++) {
			if (names[i] == sexp.operator) {
				isUsed[i] = true;
			}
		}
	} else {
		for (var i = 0; i < sexp.operands.length; i++) {
			GH.Prover.variableGenerator.determineUse(sexp.operands[i], names, isUsed);
		}
	}
};

GH.Prover.variableGenerator.fillInMissing = function(names, types) {
	var NAMES = GH.Prover.variableGenerator.VARIABLE_NAMES;
	for (var i = 0; i < names.length; i++) {
		if (!names[i]) {
			var done = false;
			var possibleNames = NAMES[types[i]];
			for (var j = 0; j < possibleNames.length && !done; j++) {
				var matchFound = false;
				for (var k = 0; k < names.length && !matchFound; k++) {
					matchFound = names[k] && (names[k].operator == possibleNames[j]);
				}
				if (!matchFound) {
					done = true;
					names[i] = GH.sExpression.createVariable(possibleNames[j]);
				}
			}
			if (!done) {
				alert('All the variable names were used in fillInMissing.');
			}
		}
	}
};
