exports.Ui = function(doc, theory, prover, scheme) {
    // ================ private methods ================
    function removeClass(node, className) {
        node.className = node.className.replace(className,'');
    }
    // ================ private state ================
    var theoremsDiv = doc.getElementById("theorems");
    var treeDiv = doc.getElementById("tree");
    var theorems = [];
    var proofTree;
    var proofTerm;
    var proofState;
    // A Tree is a UI widget representing a term.
    // @param term the term to graph
    // @param isInteractive whether this is an interactive tree.
    function Tree(term, isInteractive) {
        // ================ private methods ================
        // Makes a node hoverable.  Note that it must have no margin, or
        // else hovering will cause DOM movement.  Hovering the node will also
        // attempt to unify the theorems list. no-op if !binding.
        function makeHoverable(node, term, binding, path){
            if (binding) {
                node.addEventListener(
                    'mouseover', function(e) {
                        node.className += " selected";
                        theorems.forEach(function(t) { t.attemptUnify(term, binding, path); });
                        e.stopPropagation();
                    }, false);
                node.addEventListener(
                    'mouseout',
                    function(e) {
                        removeClass(node, ' selected');
                        theorems.forEach(function(t) { t.clearUnification(); });
                        e.stopPropagation();
                    }, false);
                node.addEventListener(
                    'click', function(e) {
                        node.className += " selected";
                        // TODO: will need some way to choose one of two unifications
                        theorems.forEach(function(t) { t.realizeUnification(0); });
                        e.stopPropagation();
                    }, false);
            }
        }

        // Make a tree out of a term.
        // @param term the term to be graphed.
        // @param binding optional; if present we'll decorate with hoverability.
        // @param pathToNodeMap this will populated to provide direct access to the
        // spans inside the tree.  A Path is like an xpath, an array where at each
        // step -1 means the operator span, 0 means the zeroth arg, etc.
        // @param path the path to this node from the root.  Leave blank to start at
        // [].  This array will be modified in-place but left as it was found.
        function makeTree(term, binding, pathToNodeMap, path) {
            if (!pathToNodeMap) pathToNodeMap = {};
            if (!path) path = [];
            var span;
            if (term.operator) {
                var op = term.operator();
                var tupleSpan = doc.createElement("span");
                tupleSpan.className += " tuple";
                tupleSpan.className += " op_" + op.toString().replace(/[^a-z]/g,'');
                makeHoverable(tupleSpan, term, binding, path.slice());
                pathToNodeMap[path] = tupleSpan;
                var opSpan = doc.createElement("span");
                opSpan.className += " operator";
                tupleSpan.appendChild(opSpan);
                opSpan.innerHTML = op.toString();
                path.push(-1);
                pathToNodeMap[path] = opSpan;
                path.pop();
                var argsSpan = doc.createElement("span");
                argsSpan.className = "args";
                tupleSpan.appendChild(argsSpan);
                var n = op.arity();
                for (var i = 0; i < n; i++) {
                    var childBinding = null;
                    if (binding) {
                        var opBinding = scheme.getBinding(op, i);
                        childBinding = binding.compose(opBinding);
                    }
                    path.push(i);
                    var argSpan = makeTree(term.input(i), childBinding, pathToNodeMap, path);
                    path.pop();
                    argSpan.className += " arg";
                    argSpan.className += " argnum" + i;
                    argSpan.className += " argof" + n;
                    argSpan.className += " depth" + path.length;
                    argsSpan.appendChild(argSpan);
                }
                span = tupleSpan;
            } else {
                var vSpan = doc.createElement("span");
                vSpan.className = " variable";
                makeHoverable(vSpan, term, binding, path.slice());
                pathToNodeMap[path] = vSpan;
                var str = term.toString(); //TODO: proper var naming
                vSpan.innerHTML = str[str.length - 1];
                span = vSpan;
            }
            var outerSpan = doc.createElement("span");
            outerSpan.appendChild(span);
            if (binding) outerSpan.className += " binding_" + binding;
            return outerSpan;
        }

        // ================ private state ================
        var wrapperSpan = doc.createElement("span");
        wrapperSpan.className = "wrapper";
        var pathToNodeMap = {};
        var theoremSpan = makeTree(term, isInteractive ? scheme.LEFT() : null,
                                   pathToNodeMap);
        wrapperSpan.appendChild(theoremSpan);
        theoremSpan.className += " theorem";
        // ================ public methods ================
        // The DOM node for a given subterm of the tuple (if path is an array)
        // or the whole tree (if path is null).  Passing undefined is slightly
        // different than [] since there's some toplevel window dressing on the
        // tree outside of the base tuple's node.
        this.node = function(path) {
            if (path instanceof Array) {
                return pathToNodeMap[path];
            } else {
                return wrapperSpan;
            }
        };
    }

    // Create an onclick handler to start a proof over with an axiom.
    function startProof(thmName) {
        return function(e) {
            proofState = prover.newProof(thmName);
            proofTerm = proofState.assertion();
            if (proofTree) treeDiv.removeChild(proofTree.node());
            proofTree = new Tree(proofTerm, true);
            treeDiv.appendChild(proofTree.node());
        };
    }

    // A Theorem is a UI object.  It owns the Tuple representing the theorem
    // itself and the Tree where it's displayed. It can unify the tuple's left and/or
    // right child against an arbitrary term in the proof-tree.
    function Theorem(name, tuple) {
        // ================ private state ================
        var originalTuple = tuple;
        var tree;
        var treeNode;
        var wrapperSpan = doc.createElement("span");
        theoremsDiv.appendChild(wrapperSpan);

        function redraw() {
            tree = new Tree(tuple, false);
            if (treeNode) wrapperSpan.removeChild(treeNode);
            treeNode = tree.node();
            wrapperSpan.appendChild(treeNode);
        }
        redraw();
        treeNode.onclick = startProof(name); // TODO: move to controller

        // Each Future represents a possible unification.  There can be 0, 1, or
        // 2 (in the case of an equivalence, either side could be unified.)
        // This list is populated by attemptUnify.  It is cleared out by
        // clearUnification or by the realization of one of the futures.
        var futures = [];
        // ================ public methods ================

        // Attempt to unify this theorem with the given term at the given
        // binding. On failure: changes the UI to gray-out the theorem.
        // On success: changes the UI to show an outline over the to-be-unified
        // child(ren), and retains the possible unification future(s) for interaction.
        // path is the path to the given term as a subterm of the proof term.
        // TODO: where does this belong?
        this.attemptUnify = function(term, binding, path) {
            var unification;
            if (binding.isUnknown()) {
                // Nothing can unify to an unknown binding.
            } else if (binding.equals(scheme.ALPHA())) {
                // TODO: handle this.
            } if (originalTuple.operator() === scheme.getEquivalence(term.kind())) {
                //TODO: handle this.  We may have to create 2 futures.
            } else if ((originalTuple.operator() === scheme.getArrow(term.kind())) &&
                       !binding.equals(scheme.EXACT())) {
                // binding Must be LEFT or RIGHT, and that determines which
                // child will provide the template for unfication.
                var whichArg; // the subterm we want to unify against
                var node;     // the DOM Node corresponding to that subterm.

                if (binding.equals(scheme.LEFT())) {
                    whichArg = 0;
                    node = tree.node([0]);
                } else if (binding.equals(scheme.RIGHT())) {
                    whichArg = 1;
                    node = tree.node([1]);
                } else {
                    throw new Error("Bad binding! " + binding);
                }
                unification = theory.unify(originalTuple.input(whichArg), term);
                if (unification) {
                    futures.push({node: node, whichArg: whichArg, unification: unification, proofPath:path.slice()});
                    node.className += " selected";
                }
            }
            if (unification) {
                // TODO: construct future
                return futures.slice();
            } else {
                treeNode.className += " disabled";
                return null;
            }
        };

        // Clears the unification attempt.
        this.clearUnification = function(future) {
            removeClass(treeNode, " disabled");
            futures.forEach(function(f) { removeClass(f.node, " selected"); });
            futures.splice(0, futures.length);
            tuple = originalTuple;
        };
        var that = this;
        // If the last call to attemptUnify succeeded, this will perform the
        // specifications on the theorem's term.  TODO: make this more continuationy
        this.realizeUnification = function(which) {
            if (which < futures.length) {
                var unification = futures[which].unification;
                var proofPath = futures[which].proofPath;
                var path = [futures[which].whichArg];
                var steps = unification.steps(0);
                function doStep() {
                    var isChanged;
                    do {
                        var step = steps.shift();
                        var newTuple = theory.parseTerm(tuple.specifyAt(step, path));
                        isChanged = !newTuple.equals(tuple);
                        tuple = newTuple;
                    } while (steps.length > 0 && !isChanged);
                    //TODO: animations here.
                    redraw();
                    tree.node(path.slice()).className += " selected";
                    if (steps.length > 0) {
                        window.setTimeout(doStep, 1000);
                    } else {
                        treeNode.onclick = function() { //TODO: hover
                            that.realizeUnification2(unification, proofPath);
                        };
                    }
                }
                doStep();
            }
        };
        this.realizeUnification2 = function(unification, path) {
            var steps = unification.steps(1);
            function doStep() {
                var isChanged;
                do {
                    var step = steps.shift();
                    var newTuple = theory.parseTerm(proofTerm.specifyAt(step, path));
                    isChanged = !newTuple.equals(proofTerm);
                    proofTerm = newTuple;
                } while (steps.length > 0 && !isChanged);
                //TODO: animations here.
                treeDiv.removeChild(proofTree.node());
                proofTree = new Tree(proofTerm, true);
                treeDiv.appendChild(proofTree.node());
                proofTree.node(path.slice()).className += " selected";
                if (steps.length > 0) {
                    window.setTimeout(doStep, 1000);
                } else {
                    proofState = proofState.PICKUP();
                }
            }
            doStep();
        };
    }

    // ================ public methods ================
    this.addAxiom = function(name) {
        theorems.push(new Theorem(name, theory.theorem(name)));
    };
    // remove all theorems from the ui.
    this.reset = function() {
        theorems.splice(0, theorems.length);
        theoremsDiv.innerHTML = "";
    };

};