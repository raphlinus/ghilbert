var GHT = { };
GHT.forEach = function(obj, func, running) {
    for (k in obj) {
        if (obj.hasOwnProperty(k)) {
            running = func(k, obj[k], running);
        }
    }
    return running;
};
// Like JSON.stringify, but handles NaN correctly.  does not handle null.
GHT.stringify = function(x) {
    return JSON.stringify(x).replace(/null/, 'NaN');
};
// A Term is an Operator, a Variable, or a Tuple of Terms (the first
// of which is an Operator)
function Term() {
    this.clone = function(mapping) {
        return this;
    };
    this.equals = function(other, mapping) {
        return this == other;
    };
    this.extractVars = function(set) {
        if (!set) set = ({});
        return set;
    };
    this.unify = function(other, mapping, map) {
        if (this != other) {
            throw "Unify error: expected " + this + " but found " + other;
        }
    };
    this.substitute = function(mapping) {
      return this;  
    };
}
function Operator(key, name, type, inputs, bindings) {
    this.toString = function() {return key;};
    this.inputs = inputs;
    this.bindings = bindings;
    this.key = key;
    this.getType = function() {
        return type;
    };
    this.toSource = function() {
        return "O(" + GHT.stringify(key) + ")";
    };
    this.toString = function(varMap) {
        return key;
    };
    this.newTerm = function() {
        var args = [this];
        for (var i = 0; i < this.inputs.length; i++) {
            args.push(new Variable(this.inputs[i]));
        }
        return T(args);
    };
    this.getName = function() {
        return name;
    };
}
function O(s) {
    return GHT.Operators[s];
}
Operator.prototype = new Term();
function Variable(type, num) {
    if (num) {
        this.index = num;
    } else {
        if (!Variable.lastUsed) Variable.lastUsed = 1;
        this.index = Variable.lastUsed++;
    }

    this.toString = function(varMap) {
        if (varMap) {
            if (varMap[this]) {
                return varMap[this].toString(varMap);
            } else {
                var newVar = varMap[null](this);
                varMap[this] = newVar;
                return newVar;
            }
        } else {
            return  (this.getType() +","+ this.index);
        }
    };

    this.clone = function(mapping) {
        if (!mapping[this]) mapping[this] = new Variable(this.getType());
        return mapping[this];
    };
    this.equals = function(other, mapping, reverse) {
        if (mapping[this] || reverse[other]) {
            return (mapping[this] == other);
        } else {
            mapping[this] = other;
            reverse[other] = this;
            return true;
        }
    };
    this.extractVars = function(set) {
        if (!set) set = ({});
        // If it's already true, don't mess with it.  But if it's absent, set it to false.
        set[this] |= false;
        return set;
    };
    this.unify = function(other, mapping, map) {
        if (this == other) {
            return;
        } else if (mapping[this]) {
            mapping[this].unify(other, mapping, map);
        } else {
            map(this, other);
        }
    };
    this.substitute = function(mapping) {
      return mapping[this] ? mapping[this].substitute(mapping) : this;
    };
    this.getType = function() {
        return type;
    };
    this.toSource = function() {
        return "TV(" + GHT.stringify(type) + ", " + this.index + ")";
    };

}
Variable.prototype = new Term();
function VariableFromString(str) {
    var a = str.split(",");
    return new Variable(a[0], a[1]);
}
function V(num) {
    return new Variable('wff',num);
}

function TV(type, num) {
    return new Variable(type, num);
}
function Tuple(terms) {
    this.terms = terms;
    this.toString = function(varMap) {
        return "(" + this.terms.map(function(t) {return t.toString(varMap);}).join(' ')
            + ")";
    };

    this.clone = function(mapping) {
        if (!mapping) mapping = ({});
        var newTerms = this.terms.map(function(t) { return t.clone(mapping);});
        return T(newTerms);
    };
    this.equals = function(other, mapping, reverse) {
        if (!mapping) mapping = ({});
        if (!reverse) reverse = ({});
        if (!(other instanceof Tuple)) return false;
        if (this.terms.length != other.terms.length) return false;
        for (var i = 0; i < this.terms.length; i++) {
            if (!this.terms[i].equals(other.terms[i], mapping, reverse)) {
                return false;
            }
        }
        return true;
    };
    // Return a set of variables into the given set, and return it.  Vars map to true
    // iff they are ever used as binders.
    this.extractVars = function(set) {
        if (!set) set = ({});
        for (var i = 0; i < terms.length - 1; i++) {
            if (isNaN(this.terms[0].bindings[i])) {
                set[this.terms[i + 1]] = true;
            } else {
                this.terms[i + 1].extractVars(set);
            }
            
        }
        return set;
    };
    this.unify = function(other, mapping, map) {
        if (this == other) {
            return;
        } else if (mapping[other]) {
            this.unify(mapping[other], mapping, map);
        } else if (other instanceof Variable) {
            map(other, this);
        } else if (!(other instanceof Tuple)
                   || (this.terms.length != other.terms.length)) {
            throw "Unify error: " + this + " cannot match " + other;
        } else {
            for (var i = 0; i < this.terms.length; i++) {
                this.terms[i].unify(other.terms[i], mapping, map);
            }
        }
    };
    this.substitute = function(mapping) {
        return T(this.terms.map(function(t) { return t.substitute(mapping);}));
    };
    this.getType = function() {
        return this.terms[0].getType();
    };
    this.toSource = function() {
        return "T(" + this.terms.map(
            function (x) { return x .toSource();}).join(",") + ")";
    };
}
Tuple.prototype = new Term();
function T(termArray) {
    if (termArray instanceof Array) {
        return new Tuple(termArray);
    } else {
        var terms = [];
        for (var t = 0; t < arguments.length; t++) {
            terms.push(arguments[t]);
        }
        return new Tuple(terms);
    }
}
function hash(str) {
    var sum = 0;
    for (var i = 0; i < str.length; i++) {
        sum = (sum * 13 + str.charCodeAt(i)) % 1000;
    }
    return sum;
}
/*
var Implies = new Operator('->', "\u2192", 'wff', ['wff', 'wff'], [-1, 1]);
var Not = new Operator('-.', "\u00ac", 'wff', ['wff'], [-1]);
var True = new Operator('t', "t", 'wff', [], []);
GHT.Operators['->'] = Implies;
GHT.Operators['-.'] = Not; 
GHT.Operators['t'] =  True;

var P, Q, R, S, U;


var thms = {
    "ax-1": T(Implies, P = V(), T(Implies, Q = V(), P)),
    "ax-2": T(Implies, T(Implies, P = V(), T(Implies, Q = V(), R = V())),
            T(Implies, T(Implies, P, Q), T(Implies, P, R))),
    "ax-3": T(Implies, T(Implies, T(Not, P = V()), T(Not, Q = V())), T(Implies, Q, P)),
    _axmp: T(Implies, T(Not, T(Implies, P = V(), T(Not, T(Implies, P, Q = V())))), Q),
    _axand: T(Implies, P=V(), T(Not, T(Implies, P, T(Not, T(True)))))
};

thms.toSource = function() {
    var out = "{";
    for (x in this) {
        if (this[x].toSource) {
            out += GHT.stringify(x) + ":" + this[x].toSource() + ",";
        }
    }
    out += "}";
    return out;
};
*/

/**
 * Asserts that the example term can be an instance of the template term, subject to
 * the (optionally) given variable mappings.  Throws an exception if
 * this is not the case.
 * @param mapping an optional mapping from variables (in template and
 * example) to terms (in template and example).
 * @param connected stores information about termination of the DAG
 * of variable dependency defined by the mapping.  Used to detect cycles.
 * @return a complete mapping from the variables present in form1 to
 * the corresponding subterms of form2.
 */
function unify(template, example, mapping, connected) {
    if (!mapping) mapping = ({});
    if (!connected) {
        connected = {to: {}, from:{}};
    }
    // Map the given variable to the given term.  Updates mapping and
    // connected, checking for a dependency cycle and throwing up if
    // found.
    function map(variable, term) {
        //require('sys').puts("Mapping " + variable + " to " + term);
        if (!connected.from[variable]) connected.from[variable] = ({});
        var varSet = term.extractVars();
        for (var v in varSet) {
            if (v == variable) {
                throw "Cyclic dependency detected: mapping " + variable + " to "
                    + term + " through var " + v;
            }
            if (!connected.to[v]) {
                connected.to[v] = { };
                connected.to[v][variable] = true;
            }
            if (!connected.from[variable][v]) {
                connected.from[variable][v] = true;
                for (var t in connected.from[v]) {
                    if (t == variable) {
                        throw "Cyclic dependency detected: mapping " + variable + " to "
                            + term + " through var " + v;
                    }
                    connected.from[variable][t] = true;
                    connected.to[t][variable] = true;
                }
            }
            for (var f in connected.to[variable]) {
                for (var t in connected.from[variable]) {
                    if (t == f) {
                        throw "Cyclic dependency detected: mapping " + variable + " to "
                            + term + " at var " + t;
                    }
                    connected.from[f][t] = true;
                    connected.to[t][f] = true;
                }
            }
        }
        mapping[variable] = term;
    }
    template.unify(example, mapping, map);
    return mapping;
}

function OperatorFromSexp(sexp, expectedType) {
    if (!GHT.Operators[sexp]) {
        // Attempt to make it on the fly
        var term = window.verifyctx.terms[sexp];
        if (!term) throw "Unknown operator " + sexp;
        var type = term[0];
        var inputs = term[1];
        var bindings = term[2].map(function(x) {
                                       // TODO: bogus
                                       if (x === null) return 0; // exact ?
                                       if (x.length === 0) return NaN; // binding ?
                                       if (x.length === 1) return NaN; // TODO:WTF is with [/] ?
                                       return 0; // *shrug*
                                   });
        GHT.Operators[sexp] = new Operator(sexp, GH.sexptounicode([sexp, '','','','','']),
                                           type, inputs, bindings);
    }
    var op = GHT.Operators[sexp];
    if (op.getType() !== expectedType) {
        throw "Wrong type: wanted " + expectedType + " got " + op.getType();
    }
    return op;
}
// Convert a ghilbert-style sexp into one of our Term objects.
// References window.direct.vg to look up type information.
function TermFromSexp(sexp, expectedType) {
    // Is it a Tuple?
    if (sexp instanceof Array) {
        var op = OperatorFromSexp(sexp[0], expectedType);
        var args = [op];
        for (var i = 0; i < op.inputs.length; i++) {
            args.push(TermFromSexp(sexp[1 + i], op.inputs[i]));
        }
        return T(args);
    } 
    // It must be a variable.
    return new Variable(expectedType, hash(sexp));
}

GHT.log = [];
GHT.bindings = {
    "-1":  "terminal",    // "This, or things which arrow this."
    "0":   "exact",       // "This term, or things term-equivalent to this."
    "1":   "initial",     // "This, or things which this arrows."
    "NaN": "binding"      // "This is a binding variable."
};
function OpList(){}
OpList.prototype = new Object();
OpList.prototype.toSource = function() {
    var s = "{";
    for (x in this) {
        var op = this[x];                
        if (op.toSource) {
            s += GHT.stringify(x);
            s += ": new Operator(";
            s += [op.key, op.getName(), op.getType(), op.inputs, op.bindings].map(
                GHT.stringify).join(",");            
            s += "),";
        }

    }
    s += "}";
    return s;
};
GHT.Operators = new OpList();

// Destructively replace the term at path {@param path} in the term
// {@param before} with the term {@param after}.  Returns the
// resultant term.
GHT.swap = function(before, path, after) {
    if (path.length) {
        var index = path.shift();
        before.terms.splice(index, 1, GHT.swap(before.terms[index], path, after));
        return before;
    } else {
        return after;
    }
};
GHT.newMenu = function(title, x, y) {
    var popup = document.getElementById("popup");
    popup.style.display="block";
    popup.style.position="absolute";
    if (x) {
        popup.style.left = x;
        popup.style.top = y;
    }
    popup.innerHTML = title + "<br/>";
    var ul = document.createElement("ul");
    popup.appendChild(ul);
    GHT.dismiss = function() {
        popup.style.display = 'none';
    };
    GHT.theMenu = {
        addOption: function(text, func) {
            var key = text;
            while (this.options[key]) key += '~';
            var li  = document.createElement("li");
            li.innerHTML = text;
            ul.appendChild(li);
            this.options[key] = function(e) {
                GHT.theStep += "GHT.theMenu.options[" + JSON.stringify(key) + "]();";
                return func(e);
            };
            li.onclick = this.options[key];
        },
        options: {
        }
    };
    return GHT.theMenu;
};

// @param builderMaker a function that will be passed the path and builderMakerArg.
// It should return a function suitable for putting in the undoStack:
// that is, one that takes a proofObj and returns the modified proofObj.
// TODO: make this OO
GHT.makeSwap = function(path, newTerm, builderMaker, builderMakerArg) {
    return function() {
        GHT.dismiss();
        var cloneMap = {};
        var theClone = GHT.theTerm.clone(cloneMap);
        GHT.setTerm(GHT.swap(theClone, path.slice(0), newTerm),
                   builderMaker(path.splice(0), builderMakerArg), cloneMap);
    };
};

GHT.extract = function(term, path) {
    if (path.length) {
        return GHT.extract(term.terms[path.shift()], path);
    } else {
        return term;
    }
};

GHT.showTerminals = function(path) {
    return function() {
        var menu = GHT.newMenu("Terminals");
        for (var name in GHT.thms) {
            menu.addOption(name, GHT.makeSwap(path.slice(0), GHT.thms[name],
                                              ProofObj.TerminalMaker, name));
        }
    };
};

GHT.showInitials = function(path) {
    //TODO
};
GHT.showEquivalents = function(path) {
    return function() {
        var menu = GHT.newMenu("Equivalents");
        var term = GHT.extract(GHT.theTerm, path.slice(0)); 
        GHT.makeThmMenu(menu, term, path, GHT.getEquivalence(term.getType()), 1);
        GHT.makeThmMenu(menu, term, path, GHT.getEquivalence(term.getType()), 2);
    };
};

// Returns a function that, when called: sifts through the thm list
// for terminals of the form [op, arg1, arg2], and
// attempts to unify arg{@param whichArg} to the given term.  For each
// success, adds a menu option to perform this substitution.
// @param menu a menu to which we'll add options
// @param term the term to serve as an example
// @param path the path to {@param term}.
// @param op the operator which must be the first term of the tuple.
// @param whichArg 1 or 2 -- which arg of op do you want the term to unify with?
GHT.makeThmMenu = function(menu, term, path, op, whichArg) {
    var cloneMap = {};
    var example = term.clone({});
    for (var name in GHT.thms) {
        var thm = GHT.thms[name];
        if (thm.terms[0] === op) {
            var template = thm.terms[whichArg];
            var otherArg = 3 - whichArg; // switch 2 and 1
            var result = thm.terms[otherArg];
            var unifyMap;
            try {
                unifyMap = unify(template, example);
            } catch (x) {
                //console.log("Could not unify "+ name + ':' + x);
                continue;
            }
            result = result.substitute(unifyMap);
            menu.addOption(name, GHT.makeSwap(path, result, ProofObj.TheoremMaker,
                                              [name, whichArg]));
        }
    }
};
GHT.showArrowers = function(path) {
    return function() {
        var menu = GHT.newMenu("Arrowers");
        var term = GHT.extract(GHT.theTerm, path.slice(0)); 
        GHT.makeThmMenu(menu, term, path, GHT.getArrow(term.getType()), 2);
    };
};
GHT.showArrowees = function(path, term) {
    return function() {
        var menu = GHT.newMenu("Arrowees");
        GHT.makeThmMenu(menu, term, path, GHT.getArrow(term.getType()), 1);
    };
};
GHT.showAssertTerminal = function(path) {
    //TODO
};
GHT.showTermBuilder = function(path, type, binding) {
    return function(event) {
        if (!event) event={ };
        var menu = GHT.newMenu(GHT.bindings[binding] + " " + type,
                               event.pageX, event.pageY);
        var theVar = GHT.extract(GHT.theTerm, path.slice(0));
        function doSub(term, isBinding) {
            return function() {
                var mapping = {};
                mapping[theVar] = term;
                if (isBinding) {
                    // Rebinding a binding variable only affects the parent term.
                    var parent = GHT.extract(GHT.theTerm, path.slice(0, path.length - 1));
                    parent = parent.substitute(mapping);
                    GHT.makeSwap(path.slice(0, path.length - 1), parent,
                                 ProofObj.TodoMaker, "rebind to " + term.toString)();
                } else {
                    // Substituting a nonbinding variable affects the whole shebang.
                    GHT.dismiss();
                    GHT.setTerm(GHT.theTerm.substitute(mapping),
                                ProofObj.TodoMaker(path.splice(0),
                                                   "termsub to " + term.toString()), mapping);
                }
            };
        }
        var isBinding = GHT.theVars[theVar];
        if (!isBinding) {
            // Not a binding variable; we can build a term
            GHT.forEach(GHT.Operators, function(k, op) {
                            if (op.getType() === type) {
                                menu.addOption(op.getName(), doSub(op.newTerm(), false));
                            }
                        });
        }
        GHT.forEach(GHT.theVars, function(varStr, unused) {
                        var myVar = VariableFromString(varStr);
                        if (myVar.getType() === type) {
                            menu.addOption(GHT.theVarMap[varStr], doSub(myVar, isBinding));
                        }
                    });
    };

};
GHT.makeDoSubst = function(path) {
    return function() {
        GHT.dismiss();
        var tuple = GHT.extract(GHT.theTerm, path.slice(0));
        if (!(tuple instanceof Tuple)
            || (tuple.terms[0] !== GHT.Operators['[/]']))  throw "Can't subst " + tuple;
        var newTerm = tuple.terms[1];
        var forVar = tuple.terms[2];
        var inTerm = tuple.terms[3];
        var mapping = { };
        mapping[forVar] = newTerm;
        var answer = inTerm.substitute(mapping);
        //console.log("[/] answer is " + answer); 
        GHT.makeSwap(path, answer, ProofObj.TodoMaker, "perform [/]")();
    };
};
GHT.makeTable = function(term, path, binding, varMap) {
    //console.log("making table for " + term);

    var type;
    // Set onclick and mouseover listeners
    function decorate(td) {
        var key = JSON.stringify(path);
        td.onclick = function(event) {
            if (!event) event = {};
            GHT.theStep = "GHT.theOnclicks['" + key + "']();";
            var menu = GHT.newMenu(GHT.bindings[binding] + " " + type,
                                   event.pageX, event.pageY);
            if (binding === 1) {
                menu.addOption("equivalents", GHT.showEquivalents(path));
                menu.addOption("terminals", GHT.showTerminals(path));
                menu.addOption("arrowees", GHT.showArrowees(path, term));
            } else if (binding === 0) {
                menu.addOption("equivalents", GHT.showEquivalents(path));
            } else if (binding === -1) {
                menu.addOption("equivalents", GHT.showEquivalents(path));
                menu.addOption("arrowers", GHT.showArrowers(path));
                menu.addOption("initials", GHT.showInitials(path));
                //TODO: menu.addOption("assert terminal", GHT.showAssertTerminal(path));
            } 
            if (isNaN(binding)) {
                menu.addOption("rebind", GHT.showTermBuilder(path, type, binding));
            } else if (term instanceof Variable) {
                menu.addOption("term substitute", GHT.showTermBuilder(path, type, binding));
            }
            if (term.terms && (term.terms[0] === GHT.Operators['[/]'])) {
                menu.addOption("perform substitution", GHT.makeDoSubst(path));
            }
        };
        GHT.theOnclicks[key] = td.onclick;
    }

    if (term instanceof Variable) {
        var span = document.createElement('span');
        type = term.getType();
        span.className += "var type_" + type;
        span.className += " binding_" + GHT.bindings[binding];
        span.innerHTML = varMap[term];
        decorate(span);
        return span;
    }
    var table = document.createElement('table');
    if (!(term instanceof Tuple)) {
        throw "Bad term " + term;
    }
    var op = term.terms[0];
    if (!(op instanceof Operator)) throw "Tuple starting with non-op " + op;

    type = op.getType();
    table.className += " type_" + type;
    table.className += " binding_" + GHT.bindings[binding];
    table.cols = op.inputs.length;
    var tr = document.createElement('tr');
    table.appendChild(tr);
    var td = document.createElement('td');
    decorate(td);
    tr.appendChild(td);
    td.colSpan = op.inputs.length;
    td.className += 'operator';
    td.innerHTML = op.getName().replace("<","&lt;");
    tr = document.createElement('tr');
    table.appendChild(tr);
    for (var i = 1; i < term.terms.length; i++) {
        var pathClone = path.slice(0);
        pathClone.push(i);
        td = document.createElement('td');
        tr.appendChild(td);
        td.appendChild(GHT.makeTable(term.terms[i], pathClone,
                                     binding * op.bindings[i - 1], varMap));
    };
    return table;

};
// A ProofObj represents an in-progress draft of a ghilbert proof.
function ProofObj(thmName) {
    var that = this;
    // Concatenates all varMaps and caps it off with a var map made from finalTerm.
    // Each map must be disjoint!
    function makeVarMap(finalTerm) {
        that.varMaps.push(GHT.makeVarMap(finalTerm.extractVars(), GHT.ghilbertVarNames));
        var unionMap = {};
        that.varMaps.forEach(
            function(map) {
                for (var k in map) {
                    unionMap[k] = map[k];
                }
            });
        that.varMaps.pop();
        var outMap = {};
        for (var k in unionMap) {
            var v = k;
            do {
                v = unionMap[v];
            } while (unionMap[v]);
            outMap[k] = v;
        }
        return outMap;
    }
    this.finish = function() {
        if (this.stack.length != 1) {
            throw "ProofObj must have exactly 1 term on the stack at end of the proof: " + this.stack.length;
        }
        var finalTerm = this.stack.pop();
        var theVarMap = makeVarMap(finalTerm);
        GHT.finalVarMap = theVarMap; //XXX
        this.conclusion[0] = finalTerm.toString(theVarMap);
        
        var str = "";
        function flatten(array) {
            if (array instanceof Array) {
                array.map(flatten);
            } else {
                str += array.toString(theVarMap);
            }
        }
        flatten(["thm (", thmName, " (", this.dvs, ") () ", this.conclusion, "\n",
                 this.steps]);
        return str + ")";
    };
    this.dvs = [];
    this.conclusion = [];
    this.steps = [];
    this.varMaps = [];
    this.stack = [];
}
ProofObj.TodoMaker = function(path, label) {
    return function(proofObj) {
        proofObj.steps.push("#TODO at " + JSON.stringify(path) + ": " + label + "\n");
        return proofObj;
    };
};
ProofObj.TheoremMaker = function(path, argList) {
    var thmName = argList[0];
    var whichArg = argList[1];
    return function(proofObj) {
        var step = [];
        var topOfStack = proofObj.stack.pop();
        var example = GHT.extract(topOfStack, path.slice(0));
        var thm = GHT.thms[thmName].clone({});
        var template = thm.terms[whichArg];
        var unifyMap = unify(template, example);
        var result = thm.terms[3 - whichArg].substitute(unifyMap);
        for (var varStr in thm.extractVars()) {
            step.push(VariableFromString(varStr), "  ");
        }
        proofObj.varMaps.push(unifyMap);
        step.push(thmName, "\n");
        topOfStack = GHT.swap(topOfStack, path.slice(0), result);

        // Travel up the path to the root term, applying stock inferences along the way
        var myPath = path.slice(0);
        while (myPath.length > 0) {
            var whichChild = myPath.pop();
            var term = GHT.extract(topOfStack, myPath.slice(0));
            var op = term.terms[0];
            for (var i = 1; i < op.inputs.length + 1; i++) {
                if (i != whichChild) {
                    step.push(term.terms[i], "  ");
                }
            }
            step.push(GHT.Inferences[op][whichChild - 1],"    ");
        }
        step.push("ax-mp\n");
        proofObj.steps.push(step);

        proofObj.stack.push(topOfStack);
        return proofObj;
    };
};
GHT.Inferences = {  // TODO: autodetect these
    "-.": ["con3i"],
    "->": ["imim1i", "imim2i"]
};
ProofObj.TerminalMaker = function(path, name) {
    var builder = function(proofObj) {
        if (path.length == 0) {
            // Starting proof over with this thm on the stack
            var step = [];
            var thm = GHT.thms[name].clone({});
            for (var varStr in thm.extractVars()) {
                step.push(VariableFromString(varStr));
                step.push("  ");
            }
            step.push(name);
            step.push("\n");
            proofObj.steps = [step];
            proofObj.stack = [thm];
        } else {
            proofObj.steps.push("#TODO at " + JSON.stringify(path) + ": " + label + "\n");
        }
        return proofObj;
    };
    return builder;
};
GHT.makeProof = function(name) {
    var proofObj = new ProofObj(name);
    var n = GHT.getVersion();
    for (var i = 1; i <= n; i++) {
        console.log(GHT.undoStack[i].step);
        proofObj = GHT.undoStack[i].builder(proofObj);
        //XXX proofObj.varMaps.push.apply(proofObj.varMaps, GHT.undoStack[i].varMaps);
    }
    GHT.theProofObj = proofObj;
    try {
        return proofObj.finish(GHT.theTerm);
    } catch (x) {
        return "Can't finish proof: " + x;
    }
};
document.getElementById("save").onclick = function() {
    var name = document.getElementById("name").value;
    GHT.thms[name] = GHT.theTerm;    
    console.log("#### Save as " + name);
};
GHT.undoStack = [];
GHT.goodVarNames = {
     'wff':[["\u03c6", "\u03c7", "\u03c8", "\u03c9",  
             "\u03b1", "\u03b2", "\u03b3", "\u03b4", "\u03b5"]],
     'set':[["S", "T", "U", "V", "W", "X", "Y", "Z"]],
     'num':[["A", "B", "C", "D", "E", "F", "G",
             "H", "I", "J", "K", "L", "M", "N"],
            ["x", "y", "z", "a", "b", "c",
             "d", "e", "f", "g", "h", "i"]]
};
GHT.ghilbertVarNames = {
     'wff':[["ph", "ps", "ch", "th", "ta", "et", "si", "zi"]],
     'set':[["S", "T", "U", "V"]],
     'num':[["A", "B", "C", "A'", "B'", "C'"],
            ["v", "w", "x", "y", "z",
             "v'", "w'", "x'", "y'", "z'"]]
};
// Input: a map from vars to isBinding, and one of GHT.*VarNames
// Output: an object that maps varString to returns a human-readable string.
// HACK: If you don't find yourself in the varMap, use varMap[null](this) instead.  
// TODO: make this whole thing a function instead so we can lazily
// bind dummy vars. But how to know if they are binding??
GHT.makeVarMap = function(vars, varNames) {
    var typeIndices = {
        wff: [0, 0], set: [0, 0], num: [0, 0]
    };
    var varMap = GHT.forEach(vars,
        function(varStr, isBinding, varMap) {
            if (varMap[varStr]) return varMap;
            var type = VariableFromString(varStr).getType();
            var index = typeIndices[type][isBinding ? 1 : 0]++;
            var name = varNames[type][isBinding ? 1 : 0][index];
            if (!name) name = varStr;
            varMap[varStr] = name;
            return varMap;
        }, {});
    varMap[null] = function(varObj) {
        var type = varObj.getType();
        var isBinding = 0;// XXX assume nonbinding
        var index = typeIndices[type][isBinding ? 1 : 0]++;
        var name = varNames[type][isBinding ? 1 : 0][index];
        if (!name) name = "RAN_OUT_OF_" + type + "_" + isBinding;
        return name;
    };
    return varMap;
};
GHT.setTerm = function(term, builder, mapping) {
    var vers = GHT.getVersion();
    vers++;
    if (!builder) builder = ProofObj.TodoMaker(["?"], "?!");
    var cloneMap = {};
    var termClone = term.clone(cloneMap);
    GHT.undoStack[vers] = {term: termClone,
                           step: GHT.theStep,
                           builder: builder,
                           varMaps: [mapping, cloneMap]
                          };
    GHT.setVersion(vers);
    // This changes the window.location hash, which will call back into actuallySetTerm.
};
GHT.actuallySetTerm = function(term) {
    console.log("Setting term: " + term.toString());
    var div = document.getElementById("tree");
    try {
        if (GHT.theTable) div.removeChild(GHT.theTable);
    } catch (x) {
        console.log("No table?");
    }
    GHT.theTerm = term;
    GHT.theVars = term.extractVars();
    GHT.theVarMap = GHT.makeVarMap(GHT.theVars, GHT.goodVarNames);
    GHT.theOnclicks = { };
    GHT.theTable =  GHT.makeTable(term, [], 1, GHT.theVarMap);
    div.appendChild(GHT.theTable);

    document.getElementById('proof').innerHTML = GHT.makeProof("wip").replace(/</g, '&lt;');
};
GHT.getVersion = function() {
    var match = window.location.toString().match(/#(.*)/);
    if (match) return Number(match[1]);
    return -1;
};
GHT.setVersion = function(version) {
    window.location = window.location.toString().replace(/#?\d*$/, '#' + version);
};
GHT.getEquivalence = function(type) {
    // TODO: autodetect these
    switch(type) {
    case 'wff':return GHT.Operators['<->'];
    case 'set':return GHT.Operators['=_'];
    case 'num':return GHT.Operators['='];
    }
    return null;
};
GHT.getArrow = function(type) {
    // TODO: autodetect these
    switch(type) {
    case 'wff':return GHT.Operators['->'];
    case 'set':return GHT.Operators['C_'];
    case 'num':return GHT.Operators['<='];
    }
    return null;
};

function loadFromServer() {
    var url = '/peano/peano_thms.gh';
    var uc = new GH.XhrUrlCtx('/', url);
    var v = new GH.VerifyCtx(uc, run);
    run(uc, '/proofs_upto/999', v);
    window.verifyctx = v;
    function init(ctx) {
        for (var symName in ctx.syms) {
            var sym = ctx.syms[symName];
            switch (sym[0]) {
            case 'tvar':
            case 'var':
                continue;
            }
            if (sym[2].length > 0) {
                // We don't need no stinkin' inferences
                continue;
            }
            //  TODO: handle dvar list
            GHT.thms[symName] = TermFromSexp(sym[3], 'wff');
        }
    }
    init(window.verifyctx);
}

GHT.setVersion(0); 
window.onload = function() {
    GHT.setTerm(GHT.thms['ax-1'], ProofObj.TodoMaker([], "start with ax-1"),{});
    GHT.actuallySetTerm(GHT.thms['ax-1']);
    window.setTimeout(
        function() {
            window.addEventListener(
                'hashchange', function() {
                    var version = GHT.getVersion();
                    GHT.actuallySetTerm(GHT.undoStack[version].term);
                }, true);
        }, 10);
    window.setTimeout(doStep, 50);
};
//loadFromServer();
GHT.autoSteps = [
    "GHT.theOnclicks['[]']()","GHT.theMenu.options['terminals']()","GHT.theMenu.options['ax-1']();",
    "GHT.theOnclicks['[]']()","GHT.theMenu.options['arrowees']()","GHT.theMenu.options['_axand']();",
    "GHT.theOnclicks['[1,2,1]']()","GHT.theMenu.options['arrowees']()","GHT.theMenu.options['ax-2']();",
    "GHT.theOnclicks['[]']()","GHT.theMenu.options['arrowees']()","GHT.theMenu.options['_axmp']();"
];
function doStep() {
    var step = GHT.autoSteps.shift();
    if (step) eval(step);
    if (GHT.autoSteps.length) {
        window.setTimeout(doStep, 10);
    }

}
