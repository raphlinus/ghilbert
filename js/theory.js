// A Theory maintains some kinds, operators, and theorems.
exports.Theory = function() {
    var thisTheory = this;
    // implementation of a reversible map between objects.
    function Bimap() {
        var forward = {};
        var backward = {};
        this.set = function(k, v) {
            var oldV = backward[forward[k]];
            if (oldV) {
                delete oldV[k];
            }
            forward[k] = v;
            if (!backward[v]) backward[v] = {};
            backward[v][k] = k;
        };
        this.lookup = function(k) {
            return forward[k];
        };
        this.lookdown = function(v) {
            return backward[v];
        };
        // Returns the endpoint of the map chain with the given start.
        this.endpoint = function(start) {
            var v;
            while ((v = this.lookup(start))) {
                start = v;
            }
            return start;
        };
    }
    var that = this;
    // ================ Private State ================
    // A Kind corresponds to a ghilbert (kind).
    function Kind(name) {
        this.toString = function() {
            return name;
        };
    }
    // An Operator corresponds to a ghilbert (term).  Each input must be a
    // kind. No reference to inputs must be retained.  Only one Operator of each
    // name should exist; Operators can be compared with ===.
    function Operator(name, output, inputs) {
        this.toString = function() { return name; };
        this.arity = function() { return inputs.length; };
        this.input = function(i) { return inputs[i]; };
        this.kind = function() { return output; };
        this.toSource = function() { return "exports.theory.operator('" + name + "')"; };
    };
    // A Term is either a Variable or a Tuple, and has a Kind.  All Terms are immutable.
    function Term() {
        this.kind = function() { throw "virtual";};
        this.toString = function() { throw "virtual";};
        // Extracts all variables in this term into the given set.
        // The varSet key is opaque, but the value is {kind, paths}.
        // paths is an array of xpaths to instances of
        // the variable in this term, each prefixed with inPath.
        this.extractVars = function(varSet, inPath) { throw "virtual";};
    }

    // A Variable has meaning only within a Tuple, and serves to bind operator inputs
    // of the same kind together.  It can have any Kind.  Each new variable is
    // assigned a unique serial number; they can be compared with ===.  Every
    // variable is in exactly one Tuple Tree.
    var Variable =
        (function() {
             var nextId = 0;
             return function(kind) {
                 var id = nextId++;
                 this.kind = function() {
                     return kind;
                 };
                 this.toString = function() {
                     return kind + "." + id;
                 };
                 this.toSource = function() { return "'" + this.toString() + "'"; };
             };
         })();
    Variable.prototype = new Term;

    // TODO: protected
    Variable.prototype.clone = function(cloneMap) {
        if (!cloneMap) cloneMap = {};
        if (cloneMap[this]) return cloneMap[this];
        return (cloneMap[this] = new Variable(this.kind()));
    };
    // TODO: protected
    Variable.prototype.xpath = function(xpath) {
        if (xpath.length == 0) return this;
        debugger;
        throw new Error("Bad path:" + xpath + " beyond " + this);
    };
    // TODO: protected
    Variable.prototype.unifyTerm = function(term, unification, path) {
        //if (!unification) unification = new Unification([this, term]);
	if (term === this) return true;
        if (!path) path = [];
        return unification.mapVarToTerm(0, path, this, term);
    };
    // TODO: protected
    Variable.prototype.specify = function(substSet, path) {
        if (!path) path = [];
        if (substSet.hasOwnProperty(path)) return substSet[path];
        return this;
    };
    Variable.prototype.extractVars = function(set, path) {
        if (!set) set = ({});
        if (!path) path = [];
        // If binding is already true, don't mess with it.  But if
        // it's absent, set it to false.
        if (!set[this]) {
            set[this] = {
                kind: this.kind(),
                paths: [path.slice()]
            };
        } else {
            set[this].paths.push(path.slice());
        }
        return set;
    };
    Variable.prototype.equals = function(otherTerm, varMap) {
        if (!(otherTerm instanceof Variable)) return false;
        if (!varMap) varMap = new Bimap();
        if (varMap.lookup(this)) {
            return varMap.lookup(this) === otherTerm;
        }
        if (varMap.lookdown(otherTerm)) {
            return varMap.lookdown(otherTerm) === this;
        }
        varMap.set(this, otherTerm);
        return true;
    };
    Variable.prototype.toTermArray = function() {
        return this;
    };
    Variable.prototype.specifyAt = function(substSet, xpath) {
        if (xpath && xpath.length > 0) throw new Error("Bad path past " + this);
        var toReturn;
        for (var p in substSet) if (substSet.hasOwnProperty(p)) {
            if (p) throw new Error("Bad substSet entry " + p + " past " + this);
            toReturn = substSet[p];
        }
        return toReturn;
    };
    Variable.prototype.extract = function(path, replacement) {
	if (path && path.length > 0) {
	    throw new Error("can't extract past " + this);
	}
	if (replacement) throw new Error("can't replace a var " + this);
	return this;
    };
    // A Tuple is an Operator with a list of inputs of appropriate
    // kind.  Its Kind is the kind of its operator.  No
    // outside reference to inputs must be retained.
    function Tuple(operator, inputs) {
        if (!(operator instanceof Operator)) {
            throw new Error("Bad operator " + operator);
        }
        this.kind = function() { return operator.kind(); };
        if (!(inputs instanceof Array)) {
            throw "Bad inputs " + inputs;
        }
        if (operator.arity() != inputs.length) {
            throw "Input length mismatch " + operator + " : " + operator.arity() +
                " != " + inputs.length;
        }
        for (var i = operator.arity() - 1; i >= 0; i--) {
            if (inputs[i].kind() != operator.input(i)) {
                throw "Bad input kind " + i + ": " + operator.input(i) + " != "  +
                    inputs[i].kind();
            }
        }
        // TODO: protected
        this.clone = function(cloneMap) {
            if (!cloneMap) cloneMap = {};
            return new Tuple(operator, inputs.map(
                                 function(t) {return t.clone(cloneMap);}));
        };
        // TODO: protected
        this.xpath = function(path) {
            if (path.length == 0) return this.clone();
            var index = path[0];
            if (index == -1) return operator;
            if (index >= inputs.length) throw "Bad path " + path + " at "+ this;
            return inputs[index].xpath(path.slice(1));
        };
        // TODO: protected
        this.specify = function(substSet, path) {
            if (!path) path = [];
            var termArray = [this.operator()];
            var n = this.operator().arity();
            for (var i = 0; i < n; i++) {
                path.push(i);
                termArray.push(this.input(i).specify(substSet, path));
                path.pop();
            }
            return termArray;
        };

        // ================ public methods ================
        this.toString = function() {
            return "[" + operator.toString() + ", " + inputs.join(", ") + "]";
        };
        this.operator = function() {
            return operator;
        };
        this.input = function(i) {
            return inputs[i];
        };
        this.extractVars = function(set, path) {
            if (!set) set = ({});
            if (!path) path = [];
            path = path.slice();
            path.push(0);
            for (var i = 0; i < inputs.length; i++) {
                path.splice(path.length - 1, 1, i);
                inputs[i].extractVars(set, path);
            }
            return set;
        };
	// TODO: protected
	// TODO: I have failed in my efforts to get isolation of Variables right.  Perhaps
	// input(i) should be replaced with xpath([i]) everywhere?
	// If you call this method with a second argument, this term is forever
	// radioactive.
	this.extract = function(path, replacement) {
            if (path.length == 0) return this;
            if (path.length == 1) {
		var i = path.shift();
		var toReturn = inputs[i];
		if (replacement) inputs[i] = replacement;
		return toReturn;
	    }
            return this.input(path.shift()).extract(path, replacement);
	};

    }
    Tuple.prototype = new Term;
    // TODO: protected
    Tuple.prototype.unifyTerm = function(term, unification, path) {
        //if (!unification) unification = new Unification([this, term]);
        if (!path) path = [];
        if (!term.operator) {
            return unification.mapVarToTerm(1, path, term, this);
        };
        if (term.operator() !== this.operator()) {
            return false;
        }
        var n = this.operator().arity();
        for (var i = 0; i < n; i++) {
            path.push(i);
            if (!this.input(i).unifyTerm(term.input(i), unification, path)) {
                return false;
            } else if (unification.isDirty()) {
		return true;
	    }
            path.pop();
        }
        return unification;
    };
    // If this tuple equals the other tuple, returns true and populates varMap
    // with the mapping from our vars to their vars.
    Tuple.prototype.equals = function(otherTerm, varMap) {
        if (!varMap) varMap = new Bimap();
        if (!otherTerm.operator || (otherTerm.operator() != this.operator())) {
            return false;
        }
        var n = this.operator().arity();
        for (var i = 0; i < n; i++) {
            if (!this.input(i).equals(otherTerm.input(i), varMap)) {
                return false;
            }
        }
        return true;
    };
    //TODO: doc this, if it's even right
    Tuple.prototype.applyArrow = function(xpath, otherTerm, templateArg) {
        var equalityMap = new Bimap();
        if (!otherTerm.input(templateArg).equals(this.extract(xpath.slice()),
                                                 equalityMap)) {
            throw new Error("Subterm not equal");
        }
        var otherArray = otherTerm.toTermArray();
        // use the equalityMap to convert otherTerm's vars to our vars.
        function performSub(termArray) {
            for (var i = 1; i < termArray.length; i++) {
                if (termArray[i] instanceof Array) {
                    performSub(termArray[i]);
                } else {
                    var mappedVar = equalityMap.lookup(termArray[i]);
                    if (mappedVar) {
                        termArray[i] = mappedVar;
                    }
                }
            }
        }
        performSub(otherArray);
        otherArray = otherArray[2 - templateArg];
        var thisArray = this.toTermArray();
        xpath = xpath.slice();
        // Swap in the result array.
        function descend(termArray) {
            if (xpath.length == 0) return otherArray;
            var child = xpath.shift();
            termArray[child + 1] = descend(termArray[child + 1]);
            return termArray;
        }
        var out =  descend(thisArray);
        return out;
    };

    // Returns a termArray for a new term that is a specification of this
    // term.  Each key in substSet is an xpath, and each value is a legal
    // termArray.  pathPrefix, if present, indicates a subterm to which the
    // paths in substSet are relative.  When a variable is changed, it will
    // be changed everywhere in the term.  If a path points to a term instead of
    // a variable, this will be a no-op.
    Tuple.prototype.specifyAt = function(substSet, xpath) {
        var varSet = this.extractVars();
        var newSubst = {};
        xpath = xpath ? xpath : [];
        for (var pathStr in substSet) {
            var path = xpath.concat(pathStr ? pathStr.split(/,/) : []);
            var sourceVar = this.xpath(path);
            if (!sourceVar) throw new Error("No var at " + xpath + " in " + this.toString());
            if (sourceVar instanceof Tuple) {
                // path to a term -- probably because the var at this path was
                // already replaced with a term in a previous specify.  For
                // convenience, we'll just ignore it.
                continue;
            }
            varSet[sourceVar].paths.forEach(
                function(p) {newSubst[p] = substSet[pathStr];});
        }
        var ret = this.specify(newSubst, []);
        return ret;
    };

    // A Unification object stores (and helps build) the result of unifying one
    // term with another.  Upon a successful call to unify(), the Unification
    // object will hold instructions for specifying the two terms to a common
    // term.
    function Unification(term0, term1) {
	// These terms are radioactive and must not leave this object.
	var terms = [term0.clone(), term1.clone()];
	var steps = [[], []];
	var dirty = false;
	this.unify = function() {
	    // Special case if either term is just a var.
	    for (var i = 0; i < 2; i++) {
		if (terms[i] instanceof Variable) {
		    var newSubst = {};
		    newSubst[[]] = terms[1 - i].toTermArray();
		    steps[i].push(newSubst);
		    return true;
		}
	    }
	    do {
		dirty = false;
		if (!terms[0].unifyTerm(terms[1], this)) return false;
	    } while (dirty);
	    return true;
	};
	this.isDirty = function() {
	    return dirty;
	};
        // unified[termIndex] has a variable at path xpath.  We need to map it to
        // theTerm, which appears in unified[1-termIndex] at the same path. Returns
        // true on success, false if the action would violate the dv constraints
        // or create a cyclic dependency,
        this.mapVarToTerm = function(termIndex, xpath, theVar, theTerm) {
	    if (theTerm === theVar) return true;
	    // Check for cyclic dependency
	    var newTermsVars = theTerm.extractVars();
	    if (newTermsVars[theVar]) return false;
	    var oldTermsVars = terms[termIndex].extractVars();
	    var oppositeTermsVars = terms[1 - termIndex].extractVars();
	    var newSubst = {};
	    // If any of the newTermsVars appear in oldTermsVars already, we
	    // need to add them to the substitution so that the specification is
	    // valid.
	    for (var v in newTermsVars) {
		if (newTermsVars.hasOwnProperty(v) && oldTermsVars.hasOwnProperty(v)) {
		    oldTermsVars[v].paths.forEach(function(p) { newSubst[p] = v; });
		}
	    }
	    newSubst[xpath] = theTerm.toTermArray();
	    oldTermsVars[theVar].paths.forEach(
                function(p) {
		    terms[termIndex].extract(p, theTerm);});
	    // Since these terms share vars, this var may also appear in the other term.
	    steps[termIndex].push(newSubst);
	    var otherPaths = oppositeTermsVars[theVar];
	    if (otherPaths) {
		newSubst = {};
		for (var w in newTermsVars) {
		    if (newTermsVars.hasOwnProperty(w) && oppositeTermsVars.hasOwnProperty(w)) {
			oppositeTermsVars[w].paths.forEach(function(p) { newSubst[p] = w; });
		    }
		}
		otherPaths.paths.forEach(
                    function(p) {
			newSubst[p] = theTerm.toTermArray();
			terms[1 - termIndex].extract(p, theTerm);});
		steps[1 - termIndex].push(newSubst);
	    }
	    dirty = true;
            return true;
        };
        this.toString = function() {
            return JSON.stringify(steps);
        };
        // Returns the final result of the unification, i.e. a term that is a
        // common specification of all input terms.
        this.term = function(i) {
            return unified[i];
        };
        // steps(i) is a sequence of substSets ({xpath: termArray,...}) for
        // specify()ing to the common unified term from term[i].
        this.steps = function(i) {
            return steps[i].slice();
        };
    }


    // Parse a term from a hetereogeneous array. A legal termArray is either an
    // opaque true key (representing a variable), or an array whose first element is
    // an operator and whose subsequest elements are legal termArray.  The types
    // and arities must all match or we throw up.
    this.parseTerm = function(termArray, asKind) {
        var vars = {};
        function copy(x) { return x.slice ? x.slice() : x; }
        function parse(input, kind) {
            if (input instanceof Array) {
                var op = input.shift();
                if (!(op instanceof Operator)) {
                    throw new Error("Bad operator: " + op);
                }
                if (kind && (kind != op.kind())) {
                    throw "kind mismatch: " + op + ": " + kind + "!= " + op.kind();
                }
                var inputs = [];
                for (var i = 0; i < input.length; i++) {
                    inputs.push(parse(copy(input[i]), op.input(i)));
                }
                return new Tuple(op, inputs);
            }
            if (vars[input]) {
                if (kind && (vars[input].kind() != kind)) {
                    throw "kind mismatch " + input + ":" + kind + " != "
                        + vars[input].kind();
                }
                return vars[input];
            }
            if (!kind) {
                throw new Error("unknown kind " + input);
            }
            return (vars[input] = new Variable(kind));
        }
        return parse(copy(termArray), asKind);
    };
    Tuple.prototype.toTermArray = function() {
        var array = [];
        array.push(this.operator());
        for (var i = 0, n = this.operator().arity(); i < n; i++) {
            array.push(this.input(i).toTermArray());
        }
        return array;
    };
    Tuple.prototype.toSource = function() {
        var array = [];
        array.push(this.operator().toSource());
        for (var i = 0, n = this.operator().arity(); i < n; i++) {
            array.push(this.input(i).toSource());
        }
        return '[' + array.join(', ') + ']';
    };
    var operators = {};
    var theorems = {};
    // ================ Public Methods ================
    this.newKind = function(name) {
        return new Kind(name);
    };
    this.newOperator = function(name, output, inputs) {
        var _inputs = [];
        _inputs.push.apply(_inputs, inputs);
        var op = new Operator(name, output, _inputs);
        operators[name.replace(/[^a-zA-Z]/g, '')] = op;
        return op;
    };
    this.operator = function(name) {
        var op = operators[name.replace(/[^a-zA-Z]/g, '')];
        if (!op) throw new Error("Unknown operator " + name);
        return op;
    };
    this.operators = function(optKindFilter) {
	var ops = [];
	for (var k in operators) if (operators.hasOwnProperty(k)) {
	    if (!optKindFilter || operators[k].kind() == optKindFilter) {
		ops.push(operators[k]);
	    }
	}
	return ops;
    };
    this.addAxiom = function(name, term) {
        theorems[name] = term;
    };
    this.theorem = function(key) {
        return theorems[key];
    };
    // Computes the most general common specification of the given two
    // terms. Returns null if none exists, or a unification result
    // (instructions for specifying the two terms to the same
    // term).
    this.unify = function(term1, term2) {
        var result = new Unification(term1, term2);
	return result.unify() ? result : null;
    };

    // Return the subterm named by path.  An xpath is an array; at
    // each step -1 means to return the operator, 0 means descend
    // into the 0th arg, etc.
    this.xpath = function(term, path) {
        return term.xpath(path).clone();
    };

    // Parses a ghilbert sexp into a term.
    this.termFromSexp = function(sexp) {
        var that = this;
        var i = 0;
        function consumeWhitespace() {
            while (sexp.charAt(i) == ' ') i++;
        }
        function consumeToken() {
            var start = i;
            while (sexp.charAt(i) != ' ' && sexp.charAt(i) != ')') i++;
            return sexp.substring(start, i);
        }
        function consumeBalanced() {
            // Assumes sexp.charAt(i) = "(".  moves i past the matching close-parenthesis. returns
            // the termArray constructed along the way.
            i++;
            var args = [];
            args.push(that.operator(consumeToken()));
            var j = 0;
            while (sexp.charAt(i) != ")") {
                consumeWhitespace();
                if (sexp.charAt(i) == "(") {
                    args.push(consumeBalanced());
                } else {
                    var varName = consumeToken();
                    args.push(varName);
                }
                j++;
            }
            i++;
            return args;
        }
        var termArray = consumeBalanced();
        return this.parseTerm(termArray);
    };

};
