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