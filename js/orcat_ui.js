// Caution: This file is a big ball of hacks.

exports.Ui = function(doc, theory, prover, scheme) {
    function NewNumVarNamer() {
        var num = 0;
        var termToName = {};
        var pathToName = {};
        var namer = function(xpath, term) {
            var name = termToName[term] || pathToName[xpath] || ++num;
            termToName[term] = name;
            pathToName[xpath] = name;
            return name;
        };
        function cloneMap(map) {
            var out = {};
            for (var k in map) out[k] = map[k];
            return out;
        }
        namer.sendPathToPath = function(srcDsts) {
            var newPathToName = cloneMap(pathToName);
            srcDsts.forEach(
                function(srcDst) {
                    if (pathToName[srcDst.src]) {
                        newPathToName[srcDst.dst] = pathToName[srcDst.src];
                    }
                });
            pathToName = newPathToName;
        };
        return namer;
    }
    function pathFromString(p) {
        return p ? p.split(/,/).map(Number) : [];
    }

    // ================ private methods ================
    function removeClass(node, className) {
        while (node.className.match(className)) {
            node.className = node.className.replace(className,'');
        }
    }
    // ================ private state ================
    var theoremsDiv = doc.getElementById("theorems");
    var treeDiv = doc.getElementById("tree");
    var theorems = [];
    var proofTree;
    var proofTerm;
    var goalTerm;
    var Ui = this;
    var proofNamer;
    var hoveredPath;
    var undoIndex = -1;
    var undoStack = [];

    function proofState() {
        return undoStack[undoIndex].proofState;
    }
    function selectedPath() {
        return undoStack[undoIndex].selectedPath;
    }
    function setSelectedPath(path) {
        if (path == null) {
            var oldPath = selectedPath();
            if (oldPath != null) {
                removeClass(proofTree.node(oldPath), ' selected');
                theorems.forEach(function(t) { t.clearUnification(); });
            }
        }
        return undoStack[undoIndex].selectedPath = path;
    }

    // A Tree is a UI widget representing a term.
    // @param term the term to graph
    // @param isInteractive whether this is an interactive tree.
    function Tree(term, isInteractive, varNamer) {
        // ================ private state ================
        if (!varNamer) varNamer = NewNumVarNamer();
        // ================ private methods ================
        // Makes a node hoverable.  Note that it must have no margin, or
        // else hovering will cause DOM movement.  Hovering the node will also
        // attempt to unify the theorems list. no-op if !binding.
        function makeHoverable(node, term, binding, path) {
            if (binding) {
                node.addEventListener(
                    'mouseover', function(e) {
                        e.stopPropagation();
                        if (selectedPath() == null) {
                            node.className += " selected";
                            hoveredPath = path.slice();
                            theorems.forEach(function(t) { t.attemptUnify(term, binding, path); });
                        }
                    }, false);
                node.addEventListener(
                    'mouseout',
                    function(e) {
                        e.stopPropagation();
                        if (selectedPath() == null) {
                            removeClass(node, ' selected');
                            theorems.forEach(function(t) { t.clearUnification(); });
                            hoveredPath = null;
                        }
                    }, false);
                node.addEventListener(
                    'click', function(e) {
                        e.stopPropagation();
                        if (selectedPath() == null) {
                            // TODO: will need some way to choose one of two unifications
                            node.className += " selected";
                            theorems.forEach(function(t) { t.realizeUnification(0); });
                            setSelectedPath(hoveredPath);
                        }
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
        // @param varNamer: takes (path, var) to var name.
        function makeTree(term, binding, pathToNodeMap, varNamer, path) {
            if (!pathToNodeMap) pathToNodeMap = {};
            if (!path) path = [];
            var span;
            if (term.operator) {
                var op = term.operator();
                var tupleSpan = doc.createElement("span");
                tupleSpan.className += " theorem";
                tupleSpan.className += " tuple";
                tupleSpan.className += " op_" + op.toString().replace(/[^a-z]/g,'');
                makeHoverable(tupleSpan, term, binding, path.slice());
                pathToNodeMap[path] = tupleSpan;
                var opSpan = doc.createElement("span");
                opSpan.className += " theorem";
                opSpan.className += " operator";
                tupleSpan.appendChild(opSpan);
                opSpan.innerHTML = op.toString();
                path.push(-1);
                pathToNodeMap[path] = opSpan;
                path.pop();
                var argsSpan = doc.createElement("span");
                argsSpan.className += " theorem";
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
                    var argSpan = makeTree(term.input(i), childBinding, pathToNodeMap, varNamer,
                                           path);
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
                vSpan.className += " theorem";
                vSpan.className += " variable";
                makeHoverable(vSpan, term, binding, path.slice());
                pathToNodeMap[path] = vSpan;
                vSpan.innerHTML = varNamer(path.slice(), term);
                span = vSpan;
            }
            var outerSpan = doc.createElement("span");
            outerSpan.className += " theorem";
            outerSpan.appendChild(span);
            if (binding) outerSpan.className += " binding_" + binding;
            return outerSpan;
        }

        // ================ private state ================
        var wrapperSpan = doc.createElement("span");
        wrapperSpan.className = "wrapper";
        var pathToNodeMap = {};
        var theoremSpan = makeTree(term, isInteractive ? scheme.LEFT() : null,
                                   pathToNodeMap, varNamer);
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
    function autoGoal(match) {
        var label = document.getElementById("autogoal");
        label.style.visibility = match ? "visible" : "hidden";
        label.style.left = match ? 0 : "20em";

    }
    function setProofState(ps, optVarTrans, optVarTransBasePath) {
        undoStack.splice(++undoIndex);
        undoStack[undoIndex] = ({proofState:ps, selectedPath: null});
        reallySetProofState(optVarTrans, optVarTransBasePath);
    }
    function reallySetProofState(optVarTrans, optVarTransBasePath) {
        function visitVarTrans(visitor) {
            if (optVarTrans) {
                for (var k in optVarTrans) if (optVarTrans.hasOwnProperty(k)) {
                    var oldPath = optVarTransBasePath.concat(pathFromString(k));
                    optVarTrans[k].forEach(
                        function(p) {
                            var newPath = optVarTransBasePath.concat(p);
                            visitor(oldPath.slice(), newPath.slice());
                        });
                }
            }
        }
        proofTerm = proofState().assertion();
        var srcDsts = [];
        visitVarTrans(function(oldPath,newPath) {
                          srcDsts.push({src:oldPath, dst:newPath});
                      });
        proofNamer.sendPathToPath(srcDsts);
        var newProofTree = new Tree(proofTerm, true, proofNamer);
        treeDiv.appendChild(newProofTree.node());
        if (proofTree) {
            visitVarTrans(function(oldPath,newPath) {
                              GHT.sendNodeToNode(proofTree.node(oldPath),
                                                 newProofTree.node(newPath));
                          });
            treeDiv.removeChild(proofTree.node());
        }
        proofTree = newProofTree;
        autoGoal(goalTerm && goalTerm.equals(proofTerm));
    }
    // Create an onclick handler to start a proof over with an axiom.
    function startProof(thmName, node) {
        return function(e) {
            proofNamer = NewNumVarNamer();
            setProofState(prover.newProof(thmName));
            GHT.sendNodeToNode(node, proofTree.node());
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
        wrapperSpan.className += " theorem";
        theoremsDiv.appendChild(wrapperSpan);
        var selectedNode;
        var varNamer = NewNumVarNamer();
        function redraw() {
            tree = new Tree(tuple, false, varNamer);
            if (treeNode) wrapperSpan.removeChild(treeNode);
            treeNode = tree.node();
            wrapperSpan.appendChild(treeNode);
        }
        redraw();
        treeNode.onclick = startProof(name, treeNode); // TODO: move to controller

        // Returns a map from paths inside the [templateArg] subterm to paths to
        // the same var outside that subterm.
        function getVarTransitions(term, templateArg) {
            var varSet = term.extractVars();
            var outMap = {};
            for (var k in varSet) if (varSet.hasOwnProperty(k)) {
                var innies = [];
                var outies = [];
                varSet[k].paths.forEach(
                    function(p) {
                        (p[0] == templateArg ? innies : outies).push(p);
                    });
                if (innies.length > 0) {
                    var outiesPerInnies = Math.floor(outies.length / innies.length + .99);
                    var outieIndex = 0;
                    innies.forEach(function(p) {
                                       for (var i = 0; i < outiesPerInnies; i++) {
                                           var o = outies[outieIndex++];
                                           if (o) {
                                               var key = p.slice(1);
                                               if (!outMap[key]) outMap[key] = [];
                                               outMap[key].push(o.slice(1));
                                           }
                                       }
                                   });
                }
            }
            return outMap;
        }
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
        this.attemptUnify = function(term, binding, path) {
            futures = proofState().consider(path.slice(), name);
            if (futures.length == 0) { 
                treeNode.className += " disabled";
            } else {
                removeClass(treeNode, " disabled");
                // TODO: consider multiple futures.
                var f = futures[0];
                f.proofPath = path.slice();
                selectedNode = tree.node([f.templateArg]);
                selectedNode.className += " selected";
            }
        };

        // Clears the unification attempt.
        this.clearUnification = function(future) {
            removeClass(treeNode, " disabled");
            selectedNode = null;
            futures.splice(0, futures.length);
            tuple = originalTuple;
            redraw();
            treeNode.onclick = startProof(name, treeNode); // TODO: move to controller
        };
        var that = this;
        // If the last call to attemptUnify succeeded, this will perform the
        // specifications on the theorem's term.  TODO: make this more continuationy
        this.realizeUnification = function(which) {
            if (which < futures.length) {
                var future = futures[which];
                var proofPath = futures[which].proofPath;
                var templatePath = [future.templateArg];
                var steps = future.unification.steps(1);
                function doStep() {
                    var isChanged;
                    do {
                        var step = steps.shift();
                        var newTuple = theory.parseTerm(
                            tuple.specifyAt(step, templatePath.slice()));
                        isChanged = !newTuple.equals(tuple);
                        tuple = newTuple;
                    } while (steps.length > 0 && !isChanged);
                    //TODO: animations here.
                    redraw();
                    tree.node(templatePath.slice()).className += " selected";
                    if (steps.length > 0) {
                        window.setTimeout(doStep, isChanged ? 500 : 0);
                    } else {
                        treeNode.onclick = function() { //TODO: hover
                            that.realizeUnification2(future);
                        };
                    }
                }
                doStep();
            }
        };
        this.realizeUnification2 = function(future) {
            var steps = future.unification.steps(0);
            function doStep() {
                var isChanged;
                do {
                    var step = steps.shift();
                    var newTuple = theory.parseTerm(proofTerm.specifyAt(
                                                        step, future.proofPath.slice()));
                    isChanged = !newTuple.equals(proofTerm);
                    proofTerm = newTuple;
                } while (steps.length > 0 && !isChanged);
                //TODO: animations here.
                treeDiv.removeChild(proofTree.node());
                proofTree = new Tree(proofTerm, true, proofNamer);
                treeDiv.appendChild(proofTree.node());
                proofTree.node(future.proofPath.slice()).className += " selected";
                if (steps.length > 0) {
                    window.setTimeout(doStep, isChanged ? 500 : 0);
                } else {
                    setProofState(future.execute(),
                                  getVarTransitions(originalTuple, future.templateArg),
                                  future.proofPath.slice());
                    theorems.forEach(function(t) { t.clearUnification(); });
                }
            }
            doStep();
        };
        this.tree = function() {
            return tree;
        };
    }

    // ================ public methods ================
    this.addAxiom = function(name) {
        var thm = new Theorem(name, theory.theorem(name));
        theorems.push(thm);
        return thm;
    };
    // remove all theorems from the ui.
    this.reset = function() {
        theorems.splice(0, theorems.length);
        theoremsDiv.innerHTML = "";
    };
    this.setGoal = function(term) {
        goalTerm = term;
        var goalTree = new Tree(term, false, NewNumVarNamer());
        var goalSpan = doc.getElementById("player.goal");
        goalSpan.removeChild(goalSpan.firstChild);
        goalSpan.appendChild(goalTree.node());
    };

    // ================ doc setup ================
    if (exports.startUi) {
        doc.getElementById("save").onclick = function() {
            autoGoal(false);
            var thmName = Math.random(); // TODO: thm naming
            var ghProof = proofState().proof(thmName); // TODO: support defthm
            var thmTerm = proofState().assertion();  
            theory.addAxiom(thmName, thmTerm);
            var newTree = Ui.addAxiom(thmName).tree();
            GHT.sendNodeToNode(proofTree.node(), newTree.node());

            var packet = {};
            packet.playerName = encodeURIComponent(GHT.playerName);
            packet.thmName = thmName;
            packet.proof = ghProof;
            var source = "exports.theory.addAxiom('FOO', exports.theory.parseTerm(BAR));exports.ui.addAxiom(FOO);\n";
            source = source.replace(/FOO/g, thmName);
            source = source.replace(/BAR/, thmTerm.toSource());
            packet.source = source;
            packet.log = "TODO";
            GHT.submitPacket(packet);
            
        };

        doc.getElementById("back").onclick = function() {
            if (selectedPath() == null) {
                --undoIndex;
                reallySetProofState();
            }
            setSelectedPath(null);
        };
        doc.getElementById("forward").onclick = function() {
            ++undoIndex;
            reallySetProofState();

        };
        GHT.redecorate = function(changed) {
            console.log("XXXX");
        };
    }
};