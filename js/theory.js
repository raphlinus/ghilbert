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
    }
    // A Variable has meaning only within a Tuple, and serves to bind operator inputs
    // of the same kind together.  It can have any Kind.  Each new variable is
    // assigned a unique serial number.
    var Variable = (function() {
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
        this.toString = function() {
            return "[" + operator.toString() + ", " + inputs.join(", ") + "]";
        };
        this.operator = function() {
            return operator;
        };
        this.input = function(i) {
            return inputs[i];
        };
    }
    Tuple.prototype = Term;
    
    // Parse a term from a hetereogeneous array. A legal termArray's first element is
    // an operator; each subsequest element is a nonnegative integer (or other key)
    // representing a variable, or a legal termArray.  The types must all match or we throw up.
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

