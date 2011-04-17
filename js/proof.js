// A Prover constructs ghilbert proofs on top of a theory and a
// scheme.  It can construct a fresh ProofState from any theorem in
// the theory, or extend an existing one by a number of techniques,
// and can render a complete proof in ghilbert-verifiable format.
// @param ghilbertVarNames a map from kind => [[tvars], [vars]]; these
// must be the same as the available vars in the ghilbert context
// where our proofs will be evaluated.
exports.Prover = function(theory, scheme, ghilbertVarNames) {
    // A VarNamer assigns sequential names from a predetermined set to
    // a sequence of variables.
    function VarNamer(varNames) {
        // Map from kind => [tvarIndex, alphaVarIndex]
        var kindIndices = {};
        // Map from varString => name
        var varMap = {};
        // ================ public methods ================
        this.name = function(varObj, isAlpha) {
            if (varMap[varObj]) return varMap[varObj];
            var kind = varObj.kind();
            if (!kindIndices[kind]) kindIndices[kind] = [0, 0];
            var index = kindIndices[kind][isAlpha ? 1 : 0]++;
            var name = varNames[kind][isAlpha ? 1 : 0][index];
            if (!name) name = "RAN_OUT_OF_" + kind + "_" + isAlpha;
            return (varMap[varObj] = name);
        };
    }
    function cloneMap(map) {
        var out = {};
        for (var k in map) out[k] = map[k];
        return out;
    }
    // A ProofState is an immutable object encapsulating an assertion (a
    // Term of kind wff), and a Ghilbert proof of that assertion's
    // truth. The internal structure of the Ghilbert proof is modeled in
    // private variables so that the proof can be extended into a new
    // ProofState.

    // This constructor must be called with care--all values must be
    // consistent, and no reference must be kept to steps or varMap.
    function ProofState(assertion, steps, varMap) {
        // Compute the binding on the subterm at the named path.  Consumes path.
        function bindingAt(path, rTerm, rBinding) {
            if (!rTerm) {
                rTerm = assertion;
                rBinding = scheme.LEFT();
            }
            if (path.length == 0) return rBinding;
            var argIndex = path.shift();
            return rBinding.compose(path, rTerm.input(argIndex),
                                   scheme.getBinding(rTerm.operator(), argIndex));
        }

        // ================ public methods ================
        // Generate a ghilbert-verifiable proof of the assertion.
        this.proof = function(thmName) {
            var varNamer = new VarNamer(ghilbertVarNames);
            // TODO: collectVariables() to find alpha bindings
            // Stringifier that knows how to handle tuples, variables, and steps.
            function stringify(obj) {
                var out = '';
                if (obj.operator) {
                    // obj is a tuple.  Convert to ghilbert sexp.
                    var op = obj.operator();
                    out += "(";
                    out += op.toString().replace(/[^a-z]/g,'');
                    for (var i = 0, n = op.arity(); i < n; i++) {
                        out += ' ' + stringify(obj.input(i));
                    }
                    out += ")";
                } else if (obj.kind) {
                    // obj is a variable.  resolve it fully, then
                    // convert to a gh var name.
                    var mapped = obj;
                    while (varMap[mapped]) mapped = varMap[mapped];
                    out += varNamer.name(mapped);
                } else {
                    // obj is a theorem name, or other stringifiable object.
                    out += obj.toString();
                }
                return out;
            }
            return "thm (" + thmName
                + " () " // DVs not yet handled.
                + " () " // Hyps not supported.
                + stringify(assertion) +
                "\n" + steps.map(stringify).join(" ") + ")";
        };
        // Generate a ghilbert defthm.  The left child of the root
        // will become the new op, with variables in appearance-order.
        // We will add the operator and its defining-theorem to the
        // theory, and return
        // the ghilbert defthm text.
        this.defthm = function(opName) {
            //TODO
        };
        // the term (of kind wff) representing the assertion of this ProofState.
        this.assertion = function() { return assertion; };
        // Returns an extension of this proofstate obtained by applying the
        // given theorem at the given path.  If the named theorem is a
        // unidirectional arrowing, then templateArg=1 means that the subterm
        // will be the tail of the arrow and must have LEFT binding while
        // templatearg=2 means that the subterm will be at the head of the arrow
        // and must have RIGHT binding.  If the named theorem is a
        // bidirectional arrowing (an equivalence), templateArg is the side to
        // match to the named subterm (which may have LEFT, RIGHT, or EXACT binding).
        // The supplied unification must have the steps we need or we will throw up.
        // TODO: this unification should be generated from here, not outside.
        this.applyArrow = function(path, thmName, templateArg, unification) {
            //TODO: check binding and operator
            var newTerm = assertion;
            var newVarMap = cloneMap(varMap);
            var newSteps = steps.slice();
            unification.steps(0).forEach(
                function(s) {
                    newTerm = theory.parseTerm(newTerm.specifyAt(s, path.slice()));
                }
            );
            var theorem = theory.theorem(thmName);
            unification.steps(1).forEach(
                function(s) {
                    theorem = theory.parseTerm(theorem.specifyAt(s, [templateArg]));
                }
            );
            var equalityMap = {};
            if (!newTerm.xpath(path.slice()).equals(theorem.xpath([templateArg]),
                                                    equalityMap)) {
                throw new Error("Incorrect unification:assertion becomes "
                                + newTerm.xpath(path.slice()).toString()
                                + " but theorem template becomes "
                                + theorem.xpath([templateArg]).toString());
            }
            // Whatever Variables are in our steps list, and also present in our
            // assertion, must be updated in the next state's varMap.
            var varSet = assertion.extractVars();
            for (var k in varSet) if (varSet.hasOwnProperty(k)) {
                var p = varSet[k].paths[0].slice();
                newVarMap[assertion.xpath(p.slice())] =
                    newTerm.xpath(p.slice());
            }
            return new ProofState(newTerm, newSteps, newVarMap);
        };
    }

    // ================ public methods ================
    // Begin a new proof starting with the named theorem.
    this.newProof = function(thmName) {
        var assertion = theory.theorem(thmName);
        var varSet = assertion.extractVars();
        var steps = [];
        var varMap = {};
        for (var k in varSet) if (varSet.hasOwnProperty(k)) {
            steps.push(assertion.xpath(varSet[k].paths[0].slice()));
        }
        steps.push(thmName, "\n");
        return new ProofState(assertion, steps, {});
    };
};