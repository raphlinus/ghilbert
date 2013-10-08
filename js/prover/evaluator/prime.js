GH.ProofGenerator.evaluatorPrime = function(prover) {
  this.prover = prover;
  this.operators = ['prime'];
};

GH.ProofGenerator.evaluatorPrime.prototype.action = function(sexp) {
	var num = this.prover.calculate(sexp.child());
	if (this.calculate(sexp)) {
		return new GH.action(num + 'prime', []);
	} else {
		return new GH.action(num + 'notprime', []);
	}
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
	this.prover.evaluate(this.prover.create('|', [divisor, num]));
	this.prover.closeExp(sexp);
	this.prover.evaluate(this.prover.create('<', [1, divisor]));
	this.prover.evaluate(this.prover.create('<', [divisor, num]));
	this.prover.print([], 'pm3.2i');
	this.prover.print([], 'notPrime');
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorPrime.prototype.provePrime = function(sexp, num) {
	var divisibility;
	for (var i = 2; i < num; i++) {
		this.prover.evaluate(this.prover.create('|', [i, this.prover.create('+', [num - 1, 1])]));
		this.prover.println('x notDividesSeti');
		divisibility = this.prover.getLast();
		this.prover.operationExchange(divisibility, '⊆');
	}
	for (var i = 3; i < num; i++) {
		this.prover.print([], 'unSubset');
	}
	divisibility = this.prover.getLast()
	var interval = this.prover.evaluate(this.prover.create('{...}', [2, num - 1]));
	this.prover.commute(interval.parent);
	this.prover.replace(divisibility.left());
	this.prover.evaluate(this.prover.create('<=', [num - 1, 0]));
	this.prover.print([], 'provePrime');
	this.prover.evaluate(this.prover.getLast().child());
	return this.prover.getLast();
};

GH.ProofGenerator.evaluatorPrime.prototype.canAddTheorem = function(sexp) {
	var num = this.prover.calculate(sexp.child());
	return (num > 2);
};

GH.ProofGenerator.evaluatorPrime.prototype.theoremName = function(sexp) {
	return 'Prime Number Calculation';
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