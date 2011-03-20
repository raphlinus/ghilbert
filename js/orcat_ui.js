exports.Ui = function(doc, theory) {
    var theoremsDiv = doc.getElementById("theorems");
    var treeDiv = doc.getElementById("tree");
    var theoremSpans = {};
    // Make a tree out of a term.
    function makeTree(term, depth) {
        if (!depth) depth = 0;
        if (term.operator) {
            var op = term.operator();
            var tupleSpan = doc.createElement("span");
            tupleSpan.className = "tuple";
            var opSpan = doc.createElement("span");
            opSpan.className = "operator";
            tupleSpan.appendChild(opSpan);
            opSpan.innerHTML = op.toString();
            var argsSpan = doc.createElement("span");
            argsSpan.className = "args";
            tupleSpan.appendChild(argsSpan);
            var n = op.numInputs();
            for (var i = 0; i < n; i++) {
                var argSpan = makeTree(term.input(i), depth + 1);
                argSpan.className = " arg";
                argSpan.className += " argnum" + i;
                argSpan.className += " argof" + n;
                argSpan.className += " depth" + depth;
                argsSpan.appendChild(argSpan);
            }
            return tupleSpan;
        } else {
            var vSpan = doc.createElement("span");
            vSpan.className = "variable";
            vSpan.innerHTML = term.toString().replace(/^.*\./,'');
            return vSpan;
        }
    }
    // Make a tree and decorate it.
    function wrapTree(term) {
        var wrapperSpan = doc.createElement("span");
        wrapperSpan.className = "wrapper";
        var span = makeTree(term);
        wrapperSpan.appendChild(span);
        span.className = "theorem";
        return wrapperSpan;
    }
    this.reset = function() {
        theoremsDiv.innerHTML = "";
    };
    // Create an onclick handler to start a proof over with an axiom.
    function startProof(axiom) {
        return function(e) {
            treeDiv.innerHTML = "";
            var wrapperSpan = wrapTree(axiom);
            treeDiv.appendChild(wrapperSpan);
        };
    }
    this.addAxiom = function(name, termArray) {
        var axiom = theory.addAxiom(name, termArray);
        var wrapperSpan = wrapTree(axiom);
        theoremSpans[name] = wrapperSpan;
        wrapperSpan.onclick = startProof(axiom);
        theoremsDiv.appendChild(wrapperSpan);
      };
};