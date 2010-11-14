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
    this.toString = function() {return name;};
    this.inputs = inputs;
    this.bindings = bindings;
    this.key = key;
    this.getType = function() {
        return type;
    };
    this.toSource = function() {
        return "O(" + GHT.stringify(key) + ")";
    };
    this.newTerm = function() {
        var args = [this];
        for (var i = 0; i < this.inputs.length; i++) {
            args.push(new Variable(this.inputs[i]));
        }
        return T(args);
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

    this.toString = function() {
        return this.getType() +","+ this.index;
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
    this.toString = function() {
        return "[" + this.terms.map(function(t) {return t.toString();}).join(' ')
            + "]";
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

var Implies = new Operator('->', "\u2192", 'wff', ['wff', 'wff'], [-1, 1]);
var Not = new Operator('-.', "\u00ac", 'wff', ['wff'], [-1]);
var True = new Operator('t', "t", 'wff', [], []);

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
                connected.to[v] = { variable: true };
            }
            if (!connected.from[variable][v]) {
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
            s += [op.key, op.toString(), op.getType(), op.inputs, op.bindings].map(
                GHT.stringify).join(",");            
            s += "),";
        }

    }
    s += "}";
    return s;
};
GHT.Operators = new OpList();
GHT.Operators['->'] = Implies;
GHT.Operators['-.'] = Not; 
GHT.Operators['t'] =  True;

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
    return {
        addOption: function(text, func) {
            var li  = document.createElement("li");
            li.innerHTML = text;
            li.onclick = func;
            ul.appendChild(li);
        }
    };
};
GHT.makeSwap = function(path, term, name) {
    return function() {
        GHT.setTerm(GHT.swap(GHT.theTerm, path.slice(0), term.clone({})));
        GHT.dismiss();
        console.log("#### Applied " + name + " at " + path);
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
        for (name in GHT.thms) {
            menu.addOption(name, GHT.makeSwap(path.slice(0), GHT.thms[name], "T:" + name));
        }
    };
};

GHT.showInitials = function(path) {
    //TODO
};
GHT.showEquivalents = function(path) {
    return function() {
        var menu = GHT.newMenu("Equivalents");
        var type = GHT.extract(GHT.theTerm, path.slice(0)).getType();
        for (name in GHT.thms) {
            var thm = GHT.thms[name];
            if ((thm instanceof Tuple) && (thm.terms[0] == GHT.getEquivalence(type))) {
                var antecedent = thm.terms[1];
                var result = thm.terms[2];
                try {
                    var answer = GHT.theTerm.clone({});
                    var example = GHT.extract(answer, path.slice(0));

                    //console.log(" Result: " + answer + " to be swapped at " +  path);
                    var mapping = unify(result, example);
                    answer = GHT.swap(answer, path.slice(0), antecedent).substitute(mapping);
                    menu.addOption(name, GHT.makeSwap([], answer, "A<" + name + " at " + path));
                } catch (x) {
                    //console.log("Can't unify " + name + ":" + x);
                }
                try {
                    var answer = GHT.theTerm.clone({});
                    var example = GHT.extract(answer, path.slice(0));

                    //console.log(" Result: " + answer + " to be swapped at " +  path);
                    var mapping = unify(antecedent, example);
                    answer = GHT.swap(answer, path.slice(0), result).substitute(mapping);
                    menu.addOption(name, GHT.makeSwap([], answer, "A>" + name + " at " + path));
                } catch (x) {
                    //console.log("Can't unify " + name + ":" + x);
                }

            }
        }
    };
};
GHT.showArrowers = function(path) {
    return function() {
        var menu = GHT.newMenu("Arrowers");
        var type = GHT.extract(GHT.theTerm, path.slice(0)).getType();
        for (name in GHT.thms) {
            var thm = GHT.thms[name];
            if ((thm instanceof Tuple) &&
                (thm.terms[0] == GHT.getArrow(type))) {
                var antecedent = thm.terms[1];
                var result = thm.terms[2];
                try {
                    var answer = GHT.theTerm.clone({});
                    var example = GHT.extract(answer, path.slice(0));

                    //console.log(" Result: " + answer + " to be swapped at " +  path);
                    var mapping = unify(result, example);
                    answer = GHT.swap(answer, path.slice(0), antecedent).substitute(mapping);
                    menu.addOption(name, GHT.makeSwap([], answer, "A<" + name + " at " + path));
                } catch (x) {
                    //console.log("Can't unify " + name + ":" + x);
                }
            }
        }
    };
};
GHT.showArrowees = function(path) {
    return function() {
        var menu = GHT.newMenu("Arrowees");
        var type = GHT.extract(GHT.theTerm, path.slice(0)).getType();
        for (name in GHT.thms) {
            var thm = GHT.thms[name];
            if ((thm instanceof Tuple) && 
                (thm.terms[0] == GHT.getArrow(type))) {
                var antecedent = thm.terms[1];
                var result = thm.terms[2];
                try {
                    var answer = GHT.theTerm.clone({});
                    var example = GHT.extract(answer, path.slice(0));

                    //console.log(" Result: " + answer + " to be swapped at " +  path);
                    var mapping = unify(antecedent, example);
                    answer = GHT.swap(answer, path.slice(0), result).substitute(mapping);
                    menu.addOption(name, GHT.makeSwap([], answer, "A>" + name + " at " + path));
                } catch (x) {
                    //console.log("Can't unify " + name + ":" + x);
                }
            }
        }
    };
};
GHT.showAssertTerminal = function(path) {
    //TODO
};
GHT.showTermBuilder = function(path, type, binding) {
    return function(event) {
        var menu = GHT.newMenu(GHT.bindings[binding] + " " + type,
                               event.pageX, event.pageY);
        var theVar = GHT.extract(GHT.theTerm, path.slice(0));
        function doSub(term, isBinding) {
            return function() {
                GHT.dismiss();
                var mapping = {};
                mapping[theVar] = term;
                if (isBinding) {
                    // Rebinding a binding variable only affects the parent term.
                    var parent = GHT.extract(GHT.theTerm, path.slice(0, path.length - 1));
                    parent = parent.substitute(mapping);
                    GHT.setTerm(GHT.swap(GHT.theTerm, path.slice(0, path.length - 1), parent));
                    console.log("#### Rebound to " + term.toString() + " at " + path);
                } else {
                    // Substituting a nonbinding variable affects the whole shebang.
                    GHT.setTerm(GHT.theTerm.substitute(mapping));
                    console.log("#### Substituted " + term.toString() + " at " + path);
                }
            };
        }
        var isBinding = GHT.theVars[theVar];
        if (!isBinding) {
            // Not a binding variable; we can build a term
            GHT.forEach(GHT.Operators, function(k, op) {
                            if (op.getType() === type) {
                                menu.addOption(op.toString(), doSub(op.newTerm(), false));
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
        GHT.setTerm(GHT.swap(GHT.theTerm, path.slice(0), answer));
        console.log("#### Performed [/] substitution at " + path);
    };
};
GHT.makeTable = function(term, path, binding, varMap) {
    //console.log("making table for " + term);

    var type;
    // Set onclick and mouseover listeners
    function decorate(td) {
        td.onclick = function(event) {
            var menu = GHT.newMenu(GHT.bindings[binding] + " " + type,
                                   event.pageX, event.pageY);
            if (binding === 1) {
                menu.addOption("equivalents", GHT.showEquivalents(path));
                menu.addOption("terminals", GHT.showTerminals(path));
                menu.addOption("arrowees", GHT.showArrowees(path));
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
    td.innerHTML = op.toString().replace("<","&lt;");
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
document.getElementById("save").onclick = function() {
    var name = document.getElementById("name").value;
    console.log("#### Save as " + name);
    GHT.thms[name] = GHT.theTerm;
};
GHT.undoStack = [];
// Input: map from varString to isBinding
// Output: map from varString to human-readable string
GHT.makeVarMap = function(vars) {
    var varNames = {
     'wff':[["\u03c6", "\u03c7", "\u03c8", "\u03c9",  
             "\u03b1", "\u03b2", "\u03b3", "\u03b4", "\u03b5"]],
     'set':[["S", "T", "U", "V", "W", "X", "Y", "Z"]],
     'num':[["A", "B", "C", "D", "E", "F", "G",
             "H", "I", "J", "K", "L", "M", "N"],
            ["x", "y", "z", "a", "b", "c",
             "d", "e", "f", "g", "h", "i"]]
    };
    return GHT.forEach(vars,
        function(varStr, isBinding, varMap) {
            if (varMap[varStr]) return varMap;
            var type = VariableFromString(varStr).getType();
            var name = varNames[type][isBinding ? 1 : 0].shift();
            if (!name) name = varStr;
            varMap[varStr] = name;
            return varMap;
        }, {});
};
GHT.setTerm = function(term) {
    var vers = GHT.getVersion();
    vers++;
    GHT.undoStack[vers] = term.clone();
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
    GHT.theVarMap = GHT.makeVarMap(GHT.theVars);
    GHT.theTable =  GHT.makeTable(term, [], 1, GHT.theVarMap);
    div.appendChild(GHT.theTable);
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

window.addEventListener('hashchange', function() {
                            var version = GHT.getVersion();
                            console.log("#### Version: " + version);
                            GHT.actuallySetTerm(GHT.undoStack[version]);
                        }, true);
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


GHT.setTerm(thms['ax-1']);
//loadFromServer();