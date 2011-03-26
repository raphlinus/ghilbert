// A Theory maintains some kinds, operators, and theorems.
exports.Theory = function() {
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
        this.numInputs = function() { return inputs.length; };
        this.input = function(i) { return inputs[i]; };
        this.kind = function() { return output; };
    };
    // A Term is either a Variable or a Tuple, and has a Kind.  All Terms are immutable.
    function Term() {
        this.kind = function() { throw "virtual";};
        this.toString = function() { throw "virtual";};
        // Attempts to unify the given term with this term as a
        // template.  On failure, returns null.  On success, returns TODO.
        this.unifyTerm = function(term) { throw "virtual";};
        // Returns a new Term with the same operators and structure,
        // but a disjoint set of fresh variables.  cloneMap will be
        // populated with a mapping from old variables to new ones.
        this.clone = function(cloneMap) { throw "virtual";};
        // Extracts all variables in this term into the given set.
        // The varSet key is opaque, but the value is {varObj, paths}.
        // paths is an array of xpaths to instances of
        // the variable in this term, each prefixed with inPath.
        this.extractVars = function(varSet, inPath) { throw "virtual";};
        // Return the subterm named by path.  An xpath is an array; at
        // each step -1 means to return the operator, 0 means descend
        // into the 0th arg, etc.
        this.xpath = function(/*const*/ path) { throw "virtual"; };
    }
    // A Variable has meaning only within a Tuple, and serves to bind operator inputs
    // of the same kind together.  It can have any Kind.  Each new variable is
    // assigned a unique serial number; they can be compared with ===.
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
                 this.clone = function(cloneMap) {
                     if (cloneMap[this]) return cloneMap[this];
                     return (cloneMap[this] = new Variable(kind));
                 };
                 this.extractVars = function(set, path) {
                     if (!set) set = ({});
                     if (!path) path = [];
                     // If binding is already true, don't mess with it.  But if it's absent, set it to false.
                     if (!set[this]) {
                         set[this] = {
                             varObj: this,
                             paths: [path.slice()]
                         };
                     } else {
                         set[this].paths.push(path.slice());
                     }
                     return set;
                 };
                 this.xpath = function(xpath) {
                     if (xpath.length == 0) return this;
                     throw "Bad path:" + xpath + " beyond " + this;
                 };
             };
         })();
    Variable.prototype = Term;
    
    // A Tuple is an Operator with a list of inputs of appropriate
    // kind.  Its Kind is the kind of its operator.  No
    // outside reference to inputs must be retained.
    function Tuple(operator, inputs) {
        if (!(operator instanceof Operator)) {
            throw "Bad operator " + operator;
        }
        this.kind = function() { return operator.kind(); };
        if (!(inputs instanceof Array)) {
            throw "Bad inputs " + inputs;
        }
        if (operator.numInputs() != inputs.length) {
            throw "Input length mismatch " + operator + " : " + operator.numInputs() +
                " != " + inputs.length;
        }
        for (var i = operator.numInputs() - 1; i >= 0; i--) {
            if (inputs[i].kind() != operator.input(i)) {
                throw "Bad input kind " + i + ": " + operator.input(i) + " != "  +
                    inputs[i].kind();
            }
        }
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
        this.clone = function(cloneMap) {       
            if (!cloneMap) cloneMap = {};
            return new Tuple(operator, inputs.map(
                                 function(t) {return t.clone(cloneMap);}));
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
        this.xpath = function(path) {
            if (path.length == 0) return this;
            var index = path[0];
            if (index == -1) return operator;
            if (index >= inputs.length) throw "Bad path " + path + " at "+ this;
            return inputs[index].xpath(path.slice(1));
        };

    }
    Tuple.prototype = Term;
    
    // Parse a term from a hetereogeneous array. A legal termArray's first element is
    // an operator; each subsequest element is a nonnegative integer (or other key)
    // representing a variable, or a legal termArray.  The types must
    // all match or we throw up.
    function parseTerm(termArray) {
       var vars = {};
        function parse(input, kind) {
            if (input instanceof Array) {
                var op = input.shift();
                if (!(op instanceof Operator)) {
                    throw "Bad operator: " + op;
                }
                if (kind && (kind != op.kind())) {
                    throw "kind mismatch: " + op + ": " + kind + "!= " + op.kind();
                }
                var inputs = [];
                for (var i = 0; i < input.length; i++) {
                    inputs.push(parse(input[i], op.input(i)));
                }
                return new Tuple(op, inputs);
            }
            if (vars[input]) {
                if (kind && (vars[input].kind() != kind)) {
                    throw "kind mismatch " + input + ":" + kind + " != " + vars[input].kind();
                }
                return vars[input];
            }
            if (!kind) {
                throw "unknown kind " + input;
            }
            return (vars[input] = new Variable(kind));
        }
        return parse(termArray);
    }
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
    this.addAxiom = function(name, termArray) {
        return (theorems[name] = parseTerm(termArray));
    };
    this.theorem = function(key) {
        return theorems[key];
    };
};

