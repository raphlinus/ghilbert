GH.ProofGenerator.evaluatorPrime = function(prover) {
  this.prover = prover;
  this.operators = ['prime'];
  this.repeator = new GH.ProofGenerator.repeatedUnionSubset(prover);
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
	var inlined = (num > 14);  // Inlined because we run out of variable names.
	for (var i = 2; i < num; i++) {
		window.console.log(i);
		this.prover.evaluate(this.prover.create('|', [i, num]));
		this.prover.println('x notDividesSeti');
		divisibility = this.prover.getLast();
		if (inlined) {			
			this.prover.println('elSubseti');
			if (i > 2) {
				this.prover.println('unSubset');
			}
		}
	}
	var setArray = [];
	for (var i = 2; i < num; i++) {
		setArray.push(i);  // The numbers here are not important. Only the length of the set matters.
	}
	if (!inlined) {
		var repeatorSet = GH.setUtil.createSet(setArray);
		this.prover.apply(this.repeator, repeatorSet);
	}
	
	divisibility = this.prover.getLast();
	var decrement = this.prover.create('.-', [num, 1]);
	var interval = this.prover.evaluate(this.prover.create('{...}', [2, decrement]));
	this.prover.commute(interval.parent);
	this.prover.replace(divisibility.left());
	this.prover.evaluate(this.prover.create('<', [1, num]));
	this.prover.print([], 'provePrime2');
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




// This generates theorems used by evaluateElementOf.
GH.ProofGenerator.repeatedUnionSubset = function(prover) {
	this.prover = prover;
};

GH.ProofGenerator.repeatedUnionSubset.prototype.action = function(sexp) {
	var set = this.prover.calculate(sexp);
	var name;
	if (set.length == 0) {
		name = 'undefined';
	} else {
		name = set.length + 'elementsInSubset';
	}
	return new GH.action(name, []);
};

GH.ProofGenerator.repeatedUnionSubset.prototype.canAddTheorem = function(sexp) {
	var set = this.prover.calculate(sexp);
	// We can run out of variable names.
	return (set.length < 14) && this.prover.symbolDefined('unSubset');
};

GH.ProofGenerator.repeatedUnionSubset.prototype.addTheorem = function(sexp) {
	var set = this.prover.calculate(sexp);
	sexp = sexp.copy();
	this.prover.println('## <title> ' + set.length + ' Elements Inside Subset </title>');

	// Find name.
	var name = this.action(sexp).name;

	// Find hypotheses.
	var varGenerator = new GH.Prover.variableGenerator();
	var setVar = varGenerator.generate('set');
	var hyps = '';
	var hypVariables = [];
	for (var i = 0; i < set.length; i++) {
		hypVariables.push(varGenerator.generate('nat'));
		hyps += 'hyp' + i + ' (e. ' + hypVariables[i] + ' ' + setVar + ') ';
	}
	
	// Find conclusion.
	var temp = sexp;
	var conclusion = this.prover.create('{}', [hypVariables[0]]);
	for (var i = 1; i < set.length; i++) {
		var newSet = this.prover.create('{}', [hypVariables[i]])
		conclusion = this.prover.create('u.', [conclusion, newSet]);
	}
	conclusion = this.prover.create('C_', [conclusion, setVar]);

	this.prover.println('thm (' + name + ' () (' + hyps + ') ' + conclusion.toString());
	this.prover.depth++;
	for (var i = 0; i < set.length; i++) {
		this.prover.println('hyp' + i);
		this.prover.println('elSubseti');
		if (i > 0) {
			this.prover.println('unSubset');
		}
	}
	this.prover.depth--;
	this.prover.println(')');
};
