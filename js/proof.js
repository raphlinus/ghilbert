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

    // A ProofState is an immutable object encapsulating an assertion (a
    // Term of kind wff), and a Ghilbert proof of that assertion's
    // truth. The internal structure of the Ghilbert proof is modeled in
    // private variables so that the proof can be extended into a new
    // ProofState.

    // This constructor must be called with care--all values must be
    // consistent, and no reference must be kept to steps.
    function ProofState(assertion, steps) {
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
            function toString(obj) {
                var out = '';
                if (obj.operator) {
                    // obj is a tuple.  Convert to ghilbert sexp.
                    var op = obj.operator();
                    out += "(";
                    out += op.toString().replace(/[^a-z]/g,'');
                    for (var i = 0, n = op.numInputs(); i < n; i++) {
                        out += ' ' + toString(obj.input(i));
                    }
                    out += ")";             
                } else if (obj.kind) {
                    // obj is a variable.  resolve it fully, then
                    // convert to a gh var name.
                    out += varNamer.name(obj);
                } else {
                    // obj is a theorem name, or other stringifiable object.
                    out += obj.toString();
                }
                return out;
            }
            return "thm (" + thmName
                + " () " // DVs not yet handled.
                + " () " // Hyps not supported.
                + toString(assertion) +
                "\n" + steps.map(toString).join(" ") + ")";
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
        this.assertion = function() {
            return assertion;
        };
        // Consider whether the given theorem can be applied at the
        // given xpath.  Returns an array with all the possibilities.
        this.consider = function(path, thmName, thmTerm) {
            var subterm = assertion.xpath(path);
            var binding = bindingAt(path.slice());
            if (thmTerm.operator() === scheme.getArrow(subterm.kind())) {
                var templateArgIndex;
                if (binding.equals(scheme.LEFT())) {
                    templateArgIndex = 0;
                } else if (binding.equals(scheme.RIGHT())) {
                    templateArgIndex = 1;
                } else {
                    return [];
                }
                var template = thmTerm.input(templateArgIndex);
                var unifyResult = template.unifyTerm(subterm);
                if (!unifyResult) {
                    return [];
                }
                return [{
                            argIndex: templateArgIndex,
                            unifyResult: unifyResult,
                            realize: function() {
                                //PICKUP
                                return new ProofState();
                            }
                        }];
            } else if (thmTerm.operator() === scheme.getEquivalence(subterm.kind())) {
                //TODO
                return [];
            } else {
                return [];
           }
        };
    }

    // ================ public methods ================
    // Begin a new proof starting with the named theorem.
    this.newProof = function(thmName) {
        var assertion = theory.theorem(thmName).clone();
        var varSet = assertion.extractVars();
        var steps = [];
        for (var k in varSet) if (varSet.hasOwnProperty(k)) {
            steps.push(varSet[k].varObj);
        }
        steps.push(thmName, "\n");
        return new ProofState(assertion, steps);
    };
};