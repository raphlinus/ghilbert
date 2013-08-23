GH.ProofGenerator.evaluatorPrime = function(prover) {
  this.prover = prover;
  this.operators = ['prime'];
};

GH.ProofGenerator.evaluatorPrime.prototype.action = function(sexp) {
	var num = this.prover.calculate(sexp.child());
	return new GH.action(num + 'prime', []);
};

GH.ProofGenerator.evaluatorPrime.prototype.isApplicable = function(sexp) {
	return true;
};

GH.ProofGenerator.evaluatorPrime.prototype.inline = function(sexp) {
	var num = this.prover.calculate(sexp.child());
	if (this.calculate(sexp)) {
		return this.provePrime(sexp, num);
	} else {
		return this.proveComposite(sexp, num);
	}
};

GH.ProofGenerator.evaluatorPrime.prototype.proveComposite = function(sexp, num) {
	var divisor = GH.ProofGenerator.evaluatorPrime.findDivisor(num);
	this.prover.openExp(sexp, 'Has a Divisor');
	this.prover.evaluate(GH.operatorUtil.create('|', [divisor, num]));
	this.prover.closeExp(sexp);
	this.prover.evaluate(GH.operatorUtil.create('<', [1, divisor]));
	this.prover.evaluate(GH.operatorUtil.create('<', [divisor, num]));
	this.prover.print([], 'pm3.2i');
	this.prover.print([], 'notPrime');
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorPrime.prototype.canAddTheorem = function(sexp) {
	return false;
};

GH.ProofGenerator.evaluatorPrime.findDivisor = function(num) {
	for (var i = 2; i * i <= num; i++) {
		if ((num % i) == 0) {
			return i;
		}
	}
	return 1;
};

GH.ProofGenerator.evaluatorPrime.prototype.calculate = function(sexp) {
	var num = this.prover.calculate(sexp.child());
	return (GH.ProofGenerator.evaluatorPrime.findDivisor(num) == 1);
};