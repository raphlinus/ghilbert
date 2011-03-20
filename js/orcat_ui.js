exports.Ui = function(doc, theory, scheme) {
    var theoremsDiv = doc.getElementById("theorems");
    var treeDiv = doc.getElementById("tree");
    var theorems = [];

    // Makes a node hoverable.  Note that it must have no margin, or
    // else it will cause DOM movement.  Hovering the node will also
    // change the class of the theorems list. no-op if !binding.
    function makeHoverable(node, term, binding){
	if (binding) {
            node.addEventListener(
		'mouseover', function(e) {
                    node.className += " selected";
		    //TODO: Attempt unfication
                    e.stopPropagation();
		}, false);
            node.addEventListener(
		'mouseout',
		function(e) {
                    node.className = node.className.replace(/ selected/g,'');
		    //TODO: Clear unfication
                    e.stopPropagation();
		}, false);
	}
    }

    // Make a tree out of a term.  binding is optional; if present
    // we'll decorate with hoverability.
    function makeTree(term, binding, depth) {
        if (!depth) depth = 0;
        var span;
        if (term.operator) {
            var op = term.operator();
            var tupleSpan = doc.createElement("span");
            tupleSpan.className += " tuple";
            tupleSpan.className += " op_" + op.toString().replace(/[^a-z]/g,'');
            makeHoverable(tupleSpan, term, binding);
            var opSpan = doc.createElement("span");
            opSpan.className += " operator";
            tupleSpan.appendChild(opSpan);
            opSpan.innerHTML = op.toString();
            var argsSpan = doc.createElement("span");
            argsSpan.className = "args";
            tupleSpan.appendChild(argsSpan);
            var n = op.numInputs();
            for (var i = 0; i < n; i++) {
		var childBinding = null;
		if (binding) {
		    var opBinding = scheme.getBinding(op, i);
		    childBinding = binding.compose(opBinding);
		}
                var argSpan = makeTree(term.input(i), childBinding, depth + 1);
                argSpan.className += " arg";
                argSpan.className += " argnum" + i;
                argSpan.className += " argof" + n;
                argSpan.className += " depth" + depth;
                argsSpan.appendChild(argSpan);
            }
            span = tupleSpan;
        } else {
            var vSpan = doc.createElement("span");
            vSpan.className = " variable";
            makeHoverable(vSpan, term, binding);
            vSpan.innerHTML = term.toString().replace(/^.*\./,'');
            span = vSpan;
        }
        var outerSpan = doc.createElement("span");
        outerSpan.appendChild(span);
	if (binding) outerSpan.className += " binding_" + binding;
        return outerSpan;
    }
    
    // Make a tree and decorate it.
    function wrapTree(term, useBinding) {
        var wrapperSpan = doc.createElement("span");
        wrapperSpan.className = "wrapper";
        var span = makeTree(term, useBinding ? scheme.LEFT() : null);
        wrapperSpan.appendChild(span);
        span.className += " theorem";
        return wrapperSpan;
    }
    this.reset = function() {
        theoremsDiv.innerHTML = "";
    };
    // Create an onclick handler to start a proof over with an axiom.
    function startProof(axiom) {
        return function(e) {
            treeDiv.innerHTML = "";
            var wrapperSpan = wrapTree(axiom, true);
            treeDiv.appendChild(wrapperSpan);
        };
    }
    this.addAxiom = function(name, termArray) {
        var axiom = theory.addAxiom(name, termArray);
        var wrapperSpan = wrapTree(axiom);
        theorems.push({name: name,
		       span: wrapperSpan,
		       term: axiom});
        wrapperSpan.onclick = startProof(axiom);
        theoremsDiv.appendChild(wrapperSpan);
      };
};