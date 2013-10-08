GH.theoremFactory = function(writer) {
	this.bases = {};
	this.writer = writer;
};

GH.theoremFactory.prototype.createBase = function(name, rawThm) {
	var newTheorem = new GH.ProofGenerator.baseTheorem(this.writer, name, rawThm);
	this.bases[name] = newTheorem;
	return newTheorem;
};

GH.theoremFactory.prototype.getTheorem = function(name) {
	return this.bases[name];
};