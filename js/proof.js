// A Prover constructs ghilbert proofs on top of a theory and a
// scheme.  It can construct a fresh ProofState from any theorem in
// the theory, or extend an existing one by a number of techniques,
// and can render a complete proof in ghilbert-verifiable format.
// @param ghilbertVarNames a map from kind => [[tvars], [vars]]; these
// must be the same as the available vars in the ghilbert context
// where our proofs will be evaluated.
exports.Prover = function(theory, scheme, ghilbertVarNames) {
    var DEBUG = true;
    // For now this is identical to the definition in theory.js, but may diverge
    // in the future.  Variables are implementation details and should not be
    // shared across interfaces.  The temptation to conflate them is almost
    // irresistable, but that way lies madness -- I promise!
    var Variable =
        (function() {
             var nextId = 0;
             return function(kind) {
                 var id = nextId++;
                 this.kind = function() {
                     return kind;
                 };
                 this.toString = function() {
                     return kind + ":" + id;
                 };
             };
         })();
    function cloneMap(map) {
        var out = {};
        for (var k in map) out[k] = map[k];
        return out;
    }
    function pathFromString(p) {
        return p ? p.split(/,/).map(Number) : [];
    }
    // A Term, but with each of its var-leaves annotated to one of our own variables.
    function WrappedTerm(term, pathToVarMap) {
        function arrayEquals(a1, a2) {
            if (a1.length != a2.length) return false;
            for (var i = a1.length - 1; i >= 0; i--) {
                if (a1[i] !== a2[i]) return false;
            }
            return true;
        }
        this.term = function(){return term;};
        // If the path leads to a var, return its image under the PTVM.  If the
        // path leads to a term, return a new WrappedTerm whose PTVM is consistent with
        // ours.
        this.xpath = function(path) {
            if (path.length == 0) return this.term();
            if (pathToVarMap[path]) { return pathToVarMap[path]; }
            var outTerm = term.xpath(path.slice());
            var ptvm = {};
            for (var p in pathToVarMap) if (pathToVarMap.hasOwnProperty(p)) {
                p = pathFromString(p);
                if (arrayEquals(p.slice(0, path.length), path)) {
                    ptvm[p.slice(path.length)] = pathToVarMap[p];
                }
            }
            return new WrappedTerm(outTerm, ptvm);
        };
        this.pathToVarMap = function() { return cloneMap(pathToVarMap); };

        // Returns a new WrappedTerm.  The term is computed by lopping off the
        // subterm of our term at path, which must be equal to
        // otherTerm.input(templateArg), and replacing it with
        // otherTerm.input(1-templateArg).  The output term will have a fresh
        // set of variables.  The vars in otherWrappedTerm.input(templateArg)
        // will be mapped to their corresponding vars in our term.  All of the
        // output variables will be mapped-to (in outMap) from variables in our
        // term, if possible, or from variables in otherWappedTerm, if not.
        this.applyArrow = function(path, otherWrappedTerm, templateArg, outMap) {
            // Any of our variables appearing in the subterm-to-be-replaced must
            // be mapped to the corresponding variables in the other term.
            for (var p in pathToVarMap) if (pathToVarMap.hasOwnProperty(p)) {
                p = pathFromString(p);
                if (arrayEquals(p.slice(0, path.length), path)) {
                    var myVar = pathToVarMap[p];
                    var otherPath = p.slice(path.length);
                    otherPath.unshift(templateArg);
                    var otherVar = otherWrappedTerm.xpath(otherPath);
                    outMap[otherVar] = myVar;
                }
            }

            var outTerm = theory.parseTerm(
                this.term().applyArrow(path.slice(), otherWrappedTerm.term(),
                                       templateArg));
            var ptvm = {};
            var varSet = outTerm.extractVars();
            var that = this;
            for (var k in varSet) if (varSet.hasOwnProperty(k)) {
                var v = new Variable(varSet[k].kind);
                varSet[k].paths.forEach(
                    function(p) {
                        ptvm[p] = v;
                        if (arrayEquals(p.slice(0, path.length), path)) {
                            // Variables inside this subterm came from otherTerm
                            var otherPath = p.slice(path.length);
                            otherPath.unshift(1 - templateArg);
                            var oldVar = otherWrappedTerm.xpath(otherPath);
                            // This var might already have been mapped to myVar above.
                            if (outMap[oldVar]) oldVar = outMap[oldVar];
                        } else {
                            // variables outside the subterm came from our term.
                            var oldVar = that.xpath(p);
                        }
                        outMap[oldVar] = v;
                    });
            }
            return new WrappedTerm(outTerm, ptvm);
        };
        // Performs the given substitution and returns a new wrappedTerm.  The
        // returned term may have new variables; if so, the appropriate mappings
        // will be stored in outMap.
        this.specifyAt = function(substSet, xpath, outMap) {
            var newTerm = theory.parseTerm(term.specifyAt(substSet, xpath.slice()));
            var newPtvm = cloneMap(pathToVarMap);
            var termArrayToVarMap = {};
            for (var p in substSet) if (substSet.hasOwnProperty(p)) {
                var termArray = substSet[p];
                p = pathFromString(p);
                var pathToSubst = xpath.concat(p);
                var oldVar = newPtvm[pathToSubst];
                if (!oldVar || !oldVar.kind || oldVar.operator) {
                    throw new Error("Bad substitution! " + pathToSubst);
                }
                if (!(termArray instanceof Array)) {
                    // A variable is being replaced by another variable.
                    // Since this just collapses two paths into the same
                    // variable, no new vars are required.
                    var newVar = termArrayToVarMap[termArray];
                    if (!newVar) {
                        termArrayToVarMap[termArray] = oldVar;
                        newVar = oldVar;
                    } else if (oldVar !== newVar) {
                        outMap[oldVar] = newVar;
                    }
                    newPtvm[pathToSubst] = newVar;
                } else {
                    // A variable is being replaced by a new term.
                    // TODO: we are relying on a guarantee about the substSet:
                    // that when a var is replaced with a termArray, none of the
                    // termArray's leaves have appeared already in the substSet.
                    var subTerm = theory.parseTerm(termArray, oldVar.kind());
                    var subPtvm = {};
                    var subVars = subTerm.extractVars();
                    for (var k in subVars) if (subVars.hasOwnProperty(k)) {
                        var v = new Variable(subVars[k].kind);
                        varSet[k].paths.forEach(
                            function(pp) {
                                subPtvm[pp] = v;
                                newPtvm[pathToSubst.concat(pp)] = v;
                            });
                    }
                    outMap[oldVar] = new WrappedTerm(subTerm, subPtvm);
                    delete newPtvm[pathToSubst];
                }
            }
            return new WrappedTerm(newTerm, newPtvm);
        };
    };
    function termToSexp(wrappedTerm, term, path, outArr) {
        if (!outArr) outArr = [];
        if (wrappedTerm.kind) {
            // Term is a Variable
            if (path && path.length > 0) {
                throw new Error("bad path " + path + " past " + wrappedTerm);
            }
            outArr.push(wrappedTerm.toString());
            return outArr;
        }
        if (!path) path = [];
        if (!term) term = wrappedTerm.term();
        if (term.operator) {
            outArr.push("(", term.operator());
            for (var i = 0; i < term.operator().arity(); i++) {
                path.push(i);
                outArr.push(" ");
                termToSexp(wrappedTerm, term.input(i), path, outArr);
                path.pop();
            }
            outArr.push(")");
        } else {
            var v = wrappedTerm.xpath(path);
            if (!v) throw new Error("Var not found " + path + " in " + wrappedTerm);
            outArr.push(v);
        }
        return outArr;
    }
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
    // consistent, and no reference must be kept to steps or varMap.
    function ProofState(wrappedAssertion, steps, varToTermMap) {
        // wrappedAssertion is a WrappedTerm containing the assertion of this
        // proof.
        // steps in an array, whose elements are "valid" vars, theorem-names, or
        // parentheses and operators used to compose sexps out of valid vars.
        // A "valid" var is exactly one of: (a) a value in the
        // wrappedAssertion's pathToVarMap; (b) a key in the
        // varToTermMap, whose value is a WrappedTerm in valid vars; (c) a dummy var,
        // needed for construction of the current proofstate but not present in
        // the assertion and never needed again for any possible extension.
        //TODO: how to determine alpha-binding of dummy vars?
        function assertValid(v, ptvm, vttm) {
            var found = 0;
            // Check if v is a value in PTVM
            for (var k in ptvm) if (ptvm.hasOwnProperty(k)) {
                if (ptvm[k] === v) {
                    found++;
                    break;
                }
            }
            // Check if v is a key in vttm
            if (vttm[v]) {
                assertVarsValid(vttm[v], ptvm, vttm);
                found++;
            }
            if (found != 1) {
                throw new Error("Not a valid var: " + v + " found=" + found);
            }
        }
        function assertVarsValid(wt, ptvm, vttm) {
            if (wt instanceof Variable) {
                assertValid(wt, ptvm, vttm);
            } else {
                var wtptvm = wt.pathToVarMap();
                for (var p in wtptvm) if (wtptvm.hasOwnProperty(p)) {
                    assertValid(wtptvm[p], ptvm, vttm);
                }
            }
        }
        function assertAllValid(ss, ptvm, vttm) {
            ss.forEach(function(s) {
                           if (!s.arity && (s.toString() !== s)) {
                               assertVarsValid(s, ptvm, vttm);
                           }
                       });
        }
        if (DEBUG) {
            assertAllValid(steps, wrappedAssertion.pathToVarMap(), varToTermMap);
        }
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
                if (obj.term) {
                    // obj is a WrappedTerm
                    return termToSexp(obj).map(stringify).join('');
                } else if (obj.arity) {
                    // obj is an Operator
                    return obj.toString().replace(/[^a-zA-Z]/g, '');
                } else if (obj.kind) {
                    // obj is a variable.  resolve it fully, then
                    // convert to a gh var name.
                    if (varToTermMap[obj]) return stringify(varToTermMap[obj]);
                    var name = varNamer.name(obj);
                    varToTermMap[obj] = name;
                    return name;
                } else {
                    // obj is a theorem name, parens, or operator
                    if (varToTermMap[obj]) return stringify(varToTermMap[obj]);
                    return obj.toString();
                }
            }
            return "thm (" + thmName
                + " () " // DVs not yet handled.
                + " () " // Hyps not supported.
                + stringify(wrappedAssertion) +
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
        this.assertion = function() { return wrappedAssertion.term(); };
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
            var newWrappedAssertion = wrappedAssertion;
            var newVarToTermMap = cloneMap(varToTermMap);
            var newSteps = steps.slice();
            unification.steps(0).forEach(
                function(s) {
                    newWrappedAssertion = newWrappedAssertion.specifyAt(
                        s, path.slice(), newVarToTermMap);
                }
            );

            if (DEBUG) {
                assertAllValid(newSteps, newWrappedAssertion.pathToVarMap(), newVarToTermMap);
            }
            var theorem = theory.theorem(thmName);
            var newTheorem = theorem;
            // For what follows we need newTheorem as a WrappedTerm.  Each var
            // that appears in newTheorem.input(templateArg) will be mapped-to from
            // the corresponding var in the subterm to be replaced.  (This
            // happens below in applyArrow.)
            var varSet = newTheorem.extractVars();
            var ptvm = {};
            for (var kk in varSet) if (varSet.hasOwnProperty(kk)) {
                var vv = new Variable(varSet[kk].kind);
                varSet[kk].paths.forEach(function(pp) { ptvm[pp] = vv; });
            }
            var newWrappedTheorem = new WrappedTerm(newTheorem, ptvm);
            var tmpMap = {};
            unification.steps(1).forEach(
                function(s) {
                    newWrappedTheorem = newWrappedTheorem.specifyAt(
                        s, [templateArg], tmpMap);
                }
            );

            // Each Variable in the original theorem is a mandHyp, but what to
            // put there depends on the final status of newTheorem.
            varSet = theorem.extractVars();
            for (var kkk in varSet) if (varSet.hasOwnProperty(kkk)) {
                var mandHyp = newWrappedTheorem.xpath(varSet[kkk].paths[0].slice());
                // Validity of vars in mandHyp: if a var appears in
                // newTheorem.input(templateArg), then applyArrow will map it in
                // the new VTTM to one of the vars in the old term, which in
                // turn will be mapped to one of the fresh vars in the arrowed
                // result, which will be a value in that result's PTVM.  If a
                // var appears only in the other half of newTheorem, then it
                // will be mapped in the new VTTM directly to one of the fresh
                // valid vars in the arrowed result.
                newSteps.push.apply(newSteps, termToSexp(mandHyp));
            }
            newSteps.push(thmName);
            newWrappedAssertion = newWrappedAssertion.applyArrow(
                path, newWrappedTheorem, templateArg, newVarToTermMap);

            // Climb the tree.
            var myPath = path.slice();
            var headRoot = (templateArg == 1 ? newWrappedAssertion : wrappedAssertion);
            var tailRoot = (templateArg == 0 ? newWrappedAssertion : wrappedAssertion);
            var mpIndex = templateArg;
            while (myPath.length > 0) {
                newSteps.push.apply(newSteps,
                                    termToSexp(headRoot.xpath(myPath.slice())));
                newSteps.push.apply(newSteps,
                                    termToSexp(tailRoot.xpath(myPath.slice())));
                var whichChild = myPath.pop();
                var op = wrappedAssertion.term().xpath(path.slice()).operator();
                for (var i = 0; i < op.arity(); i++) {
                    if (i != whichChild) {
                        myPath.push(i);
                        var mandHyp = newWrappedAssertion.xpath(myPath.slice());
                        myPath.pop();
                        newSteps.push.apply(newSteps, termToSexp(mandHyp));
                    }
                }
                var pushUpTheorem = scheme.getTheorem(op, whichChild);
                if (!pushUpTheorem) throw new Error("pushup: " + op + "." + whichChild);
                newSteps.push(pushUpTheorem);
                if (scheme.getBinding(op, whichChild) == scheme.RIGHT()) {
                    // This arrowing theorem will switch the order of our mandhyps.
                    var tmp = headRoot;
                    headRoot = tailRoot;
                    tailRoot = tmp;
                    mpIndex = 1 - mpIndex;
                }
                newSteps.push(scheme.modusPonens(mpIndex), "\n");
            }
            newSteps.push(scheme.modusPonens(),"\n");
            return new ProofState(newWrappedAssertion, newSteps, newVarToTermMap);
        };
    }

    // ================ public methods ================
    // Begin a new proof starting with the named theorem.
    this.newProof = function(thmName) {
        var assertion = theory.theorem(thmName).clone();
        var varSet = assertion.extractVars();
        var steps = [];
        var pathToVarMap = {};
        for (var k in varSet) if (varSet.hasOwnProperty(k)) {
            var v = new Variable(varSet[k].kind);
            steps.push(v);
            varSet[k].paths.forEach(function(p) {pathToVarMap[p]=v;});
        }
        steps.push(thmName, "\n");
        var wrappedAssertion = new WrappedTerm(assertion, pathToVarMap);
        var varToTermMap = {};
        return new ProofState(wrappedAssertion, steps, varToTermMap);
    };
};
