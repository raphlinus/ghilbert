// A Theory maintains some kinds, operators, and theorems.
exports.Theory = function() {
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
        throw new Error("Bad path:" + xpath + " beyond " + this);
    };
    // TODO: protected
    Variable.prototype.unifyTerm = function(term, unification, path) {
        if (!unification) unification = new Unification([this, term]);
        if (!path) path = [];
        if (term.operator) {
            var newTerm = unification.mapVarToTerm(0, path, this, term);
            if (!newTerm) {
                return false;
            }
            return newTerm.unifyTerm(term, unification, path);
        } else {
            unification.mapVarToVar(0, path, this, term);
            return unification;
        }
    };
    // TODO: protected
    Variable.prototype.specify = function(substSet, path) {
        if (!path) path = [];
        if (substSet[path]) return substSet[path];
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
        if (!varMap) varMap = {};
        if (varMap[this]) {
            return varMap[this] === otherTerm;
        }
        varMap[this] = otherTerm;
        return true;
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
    }
    Tuple.prototype = new Term;

    // TODO: protected
    Tuple.prototype.unifyTerm = function(term, unification, path) {
        if (!unification) unification = new Unification([this, term]);
        if (!path) path = [];
        if (!term.operator) {
            term = unification.mapVarToTerm(1, path, term, this);
            if (!term) {
                return false;
            }
        };
        if  (term.operator() === this.operator()) {
            path.push(0);
            var n = this.operator().arity();
            for (var i = 0; i < n; i++) {
                path.pop();
                path.push(i);
                var arg = this.input(i);
                if (!arg.operator) arg = unification.lookupVariable(0, arg);
                var otherArg = term.input(i);
                if (!otherArg.operator) otherArg = unification.lookupVariable(1, otherArg);
                if (!arg.unifyTerm(otherArg, unification, path)) {
                    return false;
                }
            }
            path.pop();
            return unification;
        } else {
            return false;
        }
    };
    // If this tuple equals the other tuple, returns true and populates varMap
    // with the mapping from our vars to their vars.
    Tuple.prototype.equals = function(otherTerm, varMap) {
        if (!varMap) varMap = {};
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

    // Returns a termArray for a new term that is a specification of this
    // term.  Each key in substSet is an xpath, and each value is a legal
    // termArray.  pathPrefix, if present, indicates a subterm to which the
    // paths in substSet are relative.  When a variable is changed, it will
    // be changed everywhere in the term.
    Tuple.prototype.specifyAt = function(substSet, xpath) {
	var varSet = this.extractVars();
	var newSubst = {};
	xpath = xpath ? xpath : [];
	for (var pathStr in substSet) {
	    var path = xpath.concat(pathStr ? pathStr.split(/,/) : []);
	    var sourceVar = this.xpath(path);
	    if (!sourceVar) throw new Error("No var at " + xpath + " in " + this.toString());
	    varSet[sourceVar].paths.forEach(
		function(p) { newSubst[p] = substSet[pathStr];});
	}
	return this.specify(newSubst, []);
    };

    // A Unification object stores (and helps build) the result of unifying one
    // term with another.  Upon a successful call to unify(), the Unification
    // object will hold instructions for specifying the two terms to a common
    // term.
    function Unification(terms) {
        var unified = terms.slice();
        // implementation of a directed acyclic graph.
        function DAG() {
            var connectedFrom = {};
            var connectedTo = {};
            // Attempts to add a connection.  Returns false if this would create a cycle.
            this.connect = function(from, to) {
                if (from === to) return false;
                if (connectedFrom[to] && connectedFrom[to][from]) return false;
                if (!connectedFrom[from]) connectedFrom[from] = {};
                if (!connectedTo[to]) connectedTo[to] = {};
                connectedFrom[from][to] = connectedTo[to][from] = 1;
                for (var f in connectedTo[from]) {
                    if (!this.connect(f, to)) return false;
                }
                for (var t in connectedFrom[to]) {
                    if (!this.connect(from, t)) return false;
                }
                return true;
            };
            this.toString = function() {
                return JSON.stringify(connectedFrom);
            };
        }
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
        }

        var varMapping = new Bimap();
        // steps()[i] starts with all the elements of opSplits[i].
        var opSplits = [[], []];
        // steps()[i] then includes all values of varJoins[i].
        var varJoins = [{}, {}];
        // if a var is turned into a term, the term goes in termMapping, and
        // it is connected in termDag to all the operator's arguments.
        var termMapping = {};
        var termDag = new DAG();
        // term[termIndex] has a variable at path xpath.  We will try to remap
        // its variable class to the given opaque key.  returns true if successful,
        // false if this would violate a distinct-variable assumption or create
        // a cyclic dependency.
        this.mapVarToVar = function(termIndex, xpath, source, newVar) {
            if (termIndex != 0) throw "only map vars forward.";
            source = varMapping.lookup(source) || source;
            var target = newVar;
            target = varMapping.lookup(target) || target;
            if (source === target) {
                return true;
            }
            if (termMapping[source]) {
                return false;
            }
            varMapping.set(source, target);
            for (var v in varMapping.lookdown(source)) {
                varMapping.set(v, target);
            }
            if (termMapping[target]) {
                if (!termDag.connect(source, target)) {
                    return false;
                }
            }

            for (var i = 0; i < 2; i++) {
                if (!varJoins[i][target]) {
                    varJoins[i][target] = {};
                }
		function addVarJoins(allPathsObj) {
                    if (allPathsObj) {
			allPathsObj.paths.forEach(function(path) {
                                                      varJoins[i][target][path] = target;
						  });
                    }
		}
		addVarJoins(unified[i].extractVars()[unified[i].xpath(xpath.slice())]);
		// TODO: I originally stopped here.  But since source was
		// lookup()ed, it could be a var in terms[1].  In that case,
		// unified[i].xpath will not necessarily match it.  Adding a
		// second set of varjoins seems to fix it, but I think this
		// might be missing something.
		addVarJoins(terms[i].extractVars()[source]);

                unified[i] = that.parseTerm(unified[i].specify(varJoins[i][target]),
                                            unified[i].kind());
            }
            return true;
        };
        // term[termIndex] has a variable at path xpath.  We will replace it
        // with a term starting with the same operator as the given term, and
        // having brand new vars as its arguments.  Returns the new term.  But
        // if the term has variables reachable from the variable to be mapped,
        // returns null instead.
        this.mapVarToTerm = function(termIndex, xpath, source, term) {
            var varSet = term.extractVars();
            source = varMapping.lookup(source) || source;
            if (varSet[source]) {
                return null;
            }
            var op = term.operator();
            var termArray = [op];
            var args = [];
            for (var i = 0; i < op.arity(); i++) {
                var v = new Variable(op.input(i));
                if (!termDag.connect(source, v)) {
                    return false;
                }
                args.push(v);
                termArray.push(v);
            }
            var t = new Tuple(op, args);
            termMapping[source] = t;
            var substSet = {};
            var unifiedVarSet = unified[termIndex].extractVars();
            var allPaths = unifiedVarSet[unified[termIndex].xpath(xpath)].paths.forEach(
		function(path) {
                    substSet[path] = termArray;
		});
            if (substSet)
            opSplits[termIndex].push(substSet);
            unified[termIndex] = that.parseTerm(unified[termIndex].specify(substSet),
                                                unified[termIndex].kind());
            return t;
        };
        // If the given variable (from the indexed term) has already been mapped
        // to a term, return that term.  Otherwise, return the variable itself.
        this.lookupVariable = function(termIndex, v) {
            var source = v;
            source = varMapping.lookup(source) || source;
            return termMapping[source] || v;
        };
        this.toString = function() {
            return JSON.stringify(steps);
        };
        // Returns the final result of the unification, i.e. a term that is a
        // common specification of all input terms.
        this.term = function() {
            return unified[0];
        };
        // steps()[i] is a sequence of substSets ({xpath: termArray,...}) for specify()ing the unified term from term[i].
        this.steps = function(i) {
            var steps = opSplits[i].slice();
            for (var k in varJoins[i]) {
                steps.push(varJoins[i][k]);
            }
            return steps;
        };
    }


    // Parse a term from a hetereogeneous array. A legal termArray's first element is
    // an operator; each subsequest element is a nonnegative integer (or other key)
    // representing a variable, or a legal termArray.  The types must
    // all match or we throw up.
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
    };

    var theorems = {    };
    // ================ Public Methods ================
    this.newKind = function(name) {
        return new Kind(name);
    };
    this.newOperator = function(name, output, inputs) {
        var _inputs = [];
        _inputs.push.apply(inputs);
        return new Operator(name, output, inputs);
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
        if (term1 === term2) {
            return new Unification();
        }
        return term1.unifyTerm(term2.clone());
    };

    // Return the subterm named by path.  An xpath is an array; at
    // each step -1 means to return the operator, 0 means descend
    // into the 0th arg, etc.
    this.xpath = function(term, path) {
        return term.xpath(path).clone();
    };
};
