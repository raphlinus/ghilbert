var GHT;
if (!GHT) {
    GHT = {};
}
GHT.reverseLookup = function(map, value) {
    for (var key in map) {
        if (value.toString() == map[key].toString()) {
            return key;
        }
    }
    throw "Value " + value + " not found in map " + JSON.stringify(map);
};

GHT.forEach = function(obj, func, running) {
    for (var k in obj) {
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
    this.extract = function(path) {
        if (path.length == 0) {
            return this;
        }
        throw "Invalid path " + path + " for term " + this;
    };
    // Finds the first instance of the given leaf in this term.  Puts the path
    // in outPath and returns whether it was found.
    this.find = function(leaf, outPath) {
        return this.toString() === leaf.toString();
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
        if (varMap && varMap['__niceOperators__']) { //TODO: HACK
            return name;
        }
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
    if (!num) {
        if (!Variable.lastUsed) Variable.lastUsed = 1;
        num = Variable.lastUsed++;
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
            return  (this.getType() +","+ num);
        }
    };

    this.clone = function(mapping) {
        if (mapping == "=") return new Variable(type, num); //HACK
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
        return "TV(" + GHT.stringify(type) + ", " + num + ")";
    };

};
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
    this.extract = function(path) {
        if (path.length == 0) {
            return this;
        }
        return this.terms[path.shift()].extract(path);
    };
    // NB: returns this, not the spliced term.
    this.splice = function(path, newTerm) {
        if (path.length == 0) {
            return newTerm;
        } else if (path.length == 1) {
            this.terms.splice(path[0], 1, newTerm);
        } else {
            this.terms[path.shift()].splice(path, newTerm);
        }
        return this;
    };
    this.find = function(leaf, outPath) {
        for (var i = 1; i < this.terms.length; i++) {
            if (this.terms[i].find(leaf, outPath)) {
                outPath.unshift(i);
                return true;
            }
        }
        return false;
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
    for (var x in this) {
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
    for (var x in this) {
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

GHT.newMenu = function(title, x, y) {
    var popup = document.getElementById("popup");
    popup.style.display="block";
    popup.style.position="absolute";
    if (x) {
        popup.style.left = x;
        popup.style.top = y;
    }
    popup.innerHTML = title + "<br/>";
    var table = document.createElement("table");
    popup.appendChild(table);
    GHT.dismiss = function() {
        popup.style.display = 'none';
    };
    GHT.theMenu = {
        addOption: function(text, func, preview) {
            if (GHT.disableOptions[text]) { return; }
            var key = text;
            while (this.options[key]) key += '~';
            var tr  = document.createElement("tr");
            var td =  document.createElement("td");
            tr.appendChild(td);
            td.innerHTML = text;
            td =  document.createElement("td");
            tr.appendChild(td);
            if (preview) {
                var varMap = GHT.makeVarMap(GHT.theVars, GHT.goodVarNames);
                varMap.__niceOperators__ = 1; // HACK
                td.innerHTML = preview.toString(varMap);
            }
            table.appendChild(tr);
            this.options[key] = function(e) {
                GHT.theStep += "GHT.theMenu.options['" + key + "']();";
                return func(e);
            };
            tr.onclick = this.options[key];
            
        },
        options: {
        },
        executeIfSingleton: function() {
            var len = 0;
            var opt = null;
            for (var key in this.options) {
                if (opt) {
                    return;
                }
                opt = this.options[key];
            }
            opt();
        }
    };
    return GHT.theMenu;
};

GHT.showTerminals = function(path, scheme) {
    return function(event) {
        var menu = GHT.newMenu("Terminals", event.pageX, event.pageY);
        for (var name in GHT.thms) {
            menu.addOption(name, GHT.makeApplyFunction(path, 'Terminal', name, scheme),
                           GHT.thms[name]);
        }
    };
};

GHT.showInitials = function(path) {
    //TODO
};
GHT.showEquivalents = function(path) {
    return function() {
        var menu = GHT.newMenu("Equivalents");
        var term = GHT.theTerm.extract(path.slice(0));
        GHT.makeThmMenu(menu, term, path, GHT.getEquivalence(term.getType()), 1, GHT.EquivalenceScheme);
        GHT.makeThmMenu(menu, term, path, GHT.getEquivalence(term.getType()), 2, GHT.EquivalenceScheme);
    };
};
GHT.showGenerify = function() {
    return function() {
        GHT.dismiss();
        GHT.setProof(GHT.getProof().generify());
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
GHT.makeThmMenu = function(menu, term, path, op, whichArg, scheme) {
    var example = term;
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
            menu.addOption(name, GHT.makeApplyFunction(path, 'Arrow', name, whichArg, scheme),
                          result);
        }
    }
};
GHT.makeApplyFunction = function (path, whatToApply, arg1, arg2, arg3) {
    return function() {
        GHT.dismiss();
        GHT.setProof(GHT.getProof()['apply' + whatToApply](path, arg1, arg2, arg3));
    };
};
GHT.showArrowers = function(path) {
    return function() {
        var menu = GHT.newMenu("Arrowers");
        var term = GHT.theTerm.extract(path.slice(0));
        GHT.makeThmMenu(menu, term, path, GHT.getArrow(term.getType()), 2, GHT.ArrowScheme);
    };
};
GHT.showArrowees = function(path) {
    return function() {
        var menu = GHT.newMenu("Arrowees");
        var term = GHT.theTerm.extract(path.slice(0));
        GHT.makeThmMenu(menu, term, path, GHT.getArrow(term.getType()), 1, GHT.ArrowScheme);
    };
};
// Presents a list of terminals which match the given term (assumed to have terminal binding).
// When selected, performs the unification and detaches the given term.

GHT.showAssertTerminal = function(path) {
    return function() {
        var menu = GHT.newMenu("Matching Terminals");
        var term = GHT.theTerm.extract(path.slice(0));
        // TODO: share code with makeThmMenu?
        //= function(menu, term, path, op, whichArg, scheme) {
        var example = term;
        for (var name in GHT.thms) {
            var template = GHT.thms[name];
            var unifyMap;
            try {
                unifyMap = unify(template, example);
            } catch (x) {
                //console.log("Could not unify "+ name + ':' + x);
                continue;
            }
            menu.addOption(name, GHT.makeApplyFunction(path, 'Detach', name));
        }
    };
};

GHT.showTermBuilder = function(path, type, binding) {
    return function(event) {
        if (!event) event={ };
        var menu = GHT.newMenu(GHT.bindings[binding] + " " + type,
                               event.pageX, event.pageY);
        var cloneMap = {};
        var rootTerm = GHT.getProof().getTerm(cloneMap);
        var oldVar = rootTerm.extract(path.slice(0));
        var theVars = rootTerm.extractVars();
        function doSub(term, isBinding) {
            return function() {
                // TODO: should clone return a bimap?
                var origVar = GHT.reverseLookup(cloneMap, oldVar);
                // If the substituand is a variable (i.e. the user is trying to
                // manually collide two variables), we'll need to reverse-map it
                // or it won't work.
                try {
                    term = VariableFromString(GHT.reverseLookup(cloneMap, term));
                } catch (x) {
                    // Otherwise, no problem.
                }
                var mapping = {};
                mapping[oldVar] = term;
                if (isBinding) {
                    // Rebinding a binding variable only affects the parent term.
                    var parent = GHT.theTerm.extract(path.slice(0, path.length - 1));
                    parent = parent.substitute(mapping);
                    throw "TODO: GHT.makeSwap(path.slice(0, path.length - 1), parent,"
                    + ' ProofObj.TodoMaker, "rebind to " + term.toString)(); ';
                } else {
                    // Substituting a nonbinding variable affects the whole shebang.
                    GHT.dismiss();
                    GHT.setProof(GHT.getProof().applyVarSub(origVar, term));
                }
            };
        }
        var isBinding = theVars[oldVar];
        if (!isBinding) {
            // Not a binding variable; we can build a term
            GHT.forEach(GHT.Operators, function(k, op) {
                            if (op.getType() === type) {
                                menu.addOption(op.getName(), doSub(op.newTerm(), false));
                            }
                        });
        }
        var theVarMap = GHT.makeVarMap(theVars, GHT.goodVarNames);
        GHT.forEach(theVars, function(varStr) {
                        var myVar = VariableFromString(varStr);
                        if (myVar.getType() === type) {
                            menu.addOption(theVarMap[varStr], doSub(myVar, isBinding));
                        }
                    });
    };

};
GHT.makeDoSubst = function(path) {
    return function() {
        GHT.dismiss();
        GHT.setProof(GHT.getProof().applySubst(path));
    };
};
GHT.getPos = function(node) {
    var x = 0;
    var y = 0;
    do {
        y += node.offsetTop;
        x += node.offsetLeft;
    } while ((node = node.offsetParent));
    return [x,y];
}
GHT.makeTable = function(term, path, binding, varMap) {
    //console.log("making table for " + term);

    var type;
    // Set onclick and mouseover listeners
    function decorate(td) {
        var key = JSON.stringify(path);
        td.onclick = function(event) {
            if (!event) event = {};
            GHT.theStep = "GHT.theOnclicks['" + key + "']();";
            var pos = GHT.getPos(td);
            var menu = GHT.newMenu(GHT.bindings[binding] + " " + type,
                                   pos[0] + td.offsetWidth, pos[1]);
            if (path.length == 0){
                menu.addOption("generify", GHT.showGenerify());
            }
            if (binding === 1) {
                menu.addOption("equivalents", GHT.showEquivalents(path));
                menu.addOption("terminals", GHT.showTerminals(path, GHT.ArrowScheme));
                menu.addOption("arrowees", GHT.showArrowees(path));
            } else if (binding === 0) {
                menu.addOption("equivalents", GHT.showEquivalents(path));
            } else if (binding === -1) {
                menu.addOption("equivalents", GHT.showEquivalents(path));
                menu.addOption("arrowers", GHT.showArrowers(path));
                menu.addOption("initials", GHT.showInitials(path));
                //TOOD: menu.addOption("assert terminal", GHT.showAssertTerminal(path));
            }
            if (isNaN(binding)) {
                menu.addOption("rebind", GHT.showTermBuilder(path, type, binding));
            } else if (term instanceof Variable) {
                menu.addOption("term substitute", GHT.showTermBuilder(path, type, binding));
            }
            if (term.terms && (term.terms[0] === GHT.Operators['[/]'])) {
                menu.addOption("perform substitution", GHT.makeDoSubst(path));
            }
            menu.executeIfSingleton();
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

// Returns a map which is the transitive closure of the union of the two maps.  They must be
// disjoint, contain no false values, and create no cycles.
GHT.combineMaps = function(map1, map2) {
    var unionMap = {};
    var key;
    for (key in map1) {
        unionMap[key] = map1[key];
    }
    for (key in map2) {
        if (unionMap[key]) {
            throw "Duplicate key: " + key + " remapped from " + unionMap[key] + " to " + map2[key];
        }
        unionMap[key] = map2[key];
    }
    var outMap = {};
    for (key in unionMap) {
        var v = key;
        do {
            v = unionMap[v];
        } while (unionMap[v]);
        outMap[key] = v;
    }
    return outMap;
};

// A ProofObj is an immutable object encapsulating a Term and a Ghilbert proof of that term's truth.
// The internal structure of the Ghilbert proof is modeled in private variables so that the proof
// can be extended into a new ProofObj.  External clients may call proofObj.getTerm() to get a
// mutable clone of the Term, proofObj.getProof() to get the complete ghilbert proof, or
// proofObj.toString() to get a diagnostic dump of the proof's structure.  To ensure validity,
// external code cannot construct ProofObjs directly but must invoke newProof from a ProofFactory.
GHT.ProofFactory = function() {
    var GHILBERT_VAR_NAMES = {
        'wff':[["ph", "ps", "ch", "th", "ta", "et", "si", "zi"]],
        'set':[["S", "T", "U", "V"]],
        'num':[["A", "B", "C", "A'", "B'", "C'"],
               ["v", "w", "x", "y", "z",
                "v'", "w'", "x'", "y'", "z'"]]
    };

    // This Constructor is private since it must be called with care.  The values passed in must all
    // be consistent.  mTerm may be null, but the resulting dummy proofObj must be immediately
    // extended with applyTerminal([], ...).  The constructed proofObj takes ownership of the passed
    // parameters, and will never change them.  In order to preserve immutability, no other
    // reference should be kept to them or their components (except by other ProofObjs which will
    // also never change them.)
    //TODO: consider making terms immutable to make this easier.
    function ProofObj(mTerm, mDvs, mSteps, mVarMap) {
        // Public accessors
        this.getTerm = function(mapping) {
            return mTerm.clone(mapping);
        };
        this.getProof = function(thmName) {
            var theVarMap = GHT.combineMaps(mVarMap, GHT.makeVarMap(mTerm.extractVars(), GHILBERT_VAR_NAMES));
            var str = "";
            function flatten(array) {
                if (array instanceof Array) {
                    array.map(flatten);
                } else {
                    str += array.toString(theVarMap);
                }
            }
            flatten(["thm (", thmName, " (", mDvs, ") () ", mTerm.toString(theVarMap), "\n", mSteps]);
            return str + ")";
        };
        this.toString = function() {
            return JSON.stringify({ steps: mSteps,
                                    term: mTerm.toString(),
                                    varMap: JSON.stringify(mVarMap)
                                  });
        };

        // Public extenders.  Each returns a new ProofObj.

        // Extend by replacing the subterm at {@param path}, which must have
        // initial binding, with the terminal named by {@param name}.
        // @param scheme an Arrow Scheme which must contain proven
        // inferences for all relevant steps in the chain.
        this.applyTerminal = function(path, name, scheme) {
            // TODO: check binding here
            var newStep = [];
            var terminalTerm = GHT.thms[name].clone({});
            for (var varStr in terminalTerm.extractVars()) {
                newStep.push(VariableFromString(varStr));
                newStep.push("  ");
            }
            newStep.push(name);
            if (path.length == 0) {
                // Starting proof over -- clear out the proofObj
                var newDvs = []; // TODO: copy over from terminalTerm
                var newVarMap = { };
                newStep.push("\n");
                return new ProofObj(terminalTerm, newDvs, [newStep], newVarMap);
            } else {
                newStep.push("    ");
                var termToReplace = mTerm.extract(path.slice(0));
                newStep.push(termToReplace, "  ",
                             GHT.Terminators[termToReplace.getType()], "    ");
                //TODO: share code with applyArrow
                var cloneMap = {};
                var newTerm = mTerm.clone(cloneMap);
                var newVarMap = GHT.combineMaps(mVarMap, cloneMap);
                newTerm = newTerm.splice(path.slice(0), terminalTerm);
                var myPath = path.slice(0);
                while (myPath.length > 0) {
                    var whichChild = myPath.pop();
                    var term = newTerm.extract(myPath.slice(0));
                    var op = term.terms[0];
                    for (var i = 1; i < op.inputs.length + 1; i++) {
                        if (i != whichChild) {
                            newStep.push(term.terms[i], "  ");
                        }
                    }
                    try {
                        newStep.push(scheme[op][whichChild - 1],"    ");
                    } catch (x) {
                        throw "Step failed: op=" + op + " child=" + whichChild + ": " + x;
                    }
                }
                newStep.push(scheme.mp[0], "\n");
                var newSteps = mSteps.slice(0);
                newSteps.push(newStep);
                var newDvs = mDvs.slice(0); // TODO: copy over from terminalTerm
                return new ProofObj(newTerm, newDvs, newSteps, newVarMap);
            }
        };

        // Extend by replacing the subterm at {@param path} according to an
        // arrowing theorem named by {@param name}.  If the named theorem is a unidirectional
        // arrowing, then templateArg=1 means that the subterm will be
        // the tail of the arrow and must have initial binding while templatearg=2 means that the
        // subterm will be at the head of the arrow and must have terminal binding.  If the named
        // theorem is a bidirectional arrowing (an equivalence), templateArg is the side to match to
        // the named subterm (which may have any binding).
        // @param scheme an Arrow Scheme which must contain proven inferences
        // for all relevant steps in the chain.

        this.applyArrow = function(path, name, templateArg, scheme) {
            // TODO: check binding here
            var newStep = [];
            var cloneMap = {};
            var newTerm = mTerm.clone(cloneMap);
            var newVarMap = GHT.combineMaps(mVarMap, cloneMap);

            var example = newTerm.extract(path.slice(0));
            var thm = GHT.thms[name].clone({});
            var template = thm.terms[templateArg];
            // TODO: eliminate this second unification
            var unifyMap = unify(template, example);
            var result = thm.terms[3 - templateArg].substitute(unifyMap);
            for (var varStr in thm.extractVars()) {
                newStep.push(VariableFromString(varStr), "  ");
            }
            newVarMap = GHT.combineMaps(newVarMap, unifyMap);
            newStep.push(name, "\n");
            newTerm = newTerm.substitute(unifyMap);
            newTerm = newTerm.splice(path.slice(0), result);

            // Travel up the path to the root term, applying stock inferences along the way
            var myPath = path.slice(0);
            while (myPath.length > 0) {
                var whichChild = myPath.pop();
                var term = newTerm.extract(myPath.slice(0));
                var op = term.terms[0];
                for (var i = 1; i < op.inputs.length + 1; i++) {
                    if (i != whichChild) {
                        newStep.push(term.terms[i], "  ");
                    }
                }
                var pushUpThm;
                try {
                    pushUpThm = scheme[op][whichChild - 1];
                } catch (x) {
                    throw "Step failed: op=" + op + " child=" + whichChild + ": " + x;
                }
                //TODO(HACK)
                pushUpThm = pushUpThm.replace(/d$/,'i');
                newStep.push(pushUpThm,"    ");
            }
            newStep.push(scheme.mp[templateArg - 1], "\n");
            var newSteps = mSteps.slice(0);
            newSteps.push(newStep);
            var newDvs = mDvs.slice(0); // TODO: copy over from thm
            return new ProofObj(newTerm, newDvs, newSteps, newVarMap);
        };
        // Extend the proof by globally substituting a term for a variable.  The variable must not be
        // binding and this substitution must not violate existing DV constraints.  This rewrites the
        // history of the proof so that the variable, when it was introduced, now becomes the chosen
        // term.  Note that variable should be one of the variables in this proof's private term, not
        // the term returned from getTerm() -- you'll need to hang on to the cloneMap and do a reverse
        // lookup.
        this.applyVarSub = function(variable, replacement) {
            //TODO: check DVs here
            var mapping = {};
            mapping[variable] = replacement;
            var newTerm = mTerm.substitute(mapping);
            var newVarMap = GHT.combineMaps(mVarMap, mapping);
            var newSteps = mSteps.slice(0);
            var newDvs = mDvs;  // TODO: propagate DVs forward through replacement
            return new ProofObj(newTerm, newDvs, newSteps, newVarMap);
        };

        // Extend by applying the substitution law sbcie at the given path.
        this.applySubst = function(path) {
             // TODO: This special knowledge of [/] is ugly.  Should substitution
            // be part of ghilbert directly?  Or should we be able to learn to
            // manipulate all [/]-like operators?

            // Our goal is to prove (-> (= x A) (<-> ph ps)) so we can use sbcie.
            // For each instance of the substituted-for variable, we need to
            // propagate an equality up to the root of the substitution-term.
            var cloneMap = {};
            var mTermClone = mTerm.clone(cloneMap);
            var subTerm = mTermClone.extract(path.slice(0));
            if (subTerm.terms[0].toString() !== '[/]') {
                throw "Term not actually [/] at path " + JSON.stringify(path);
            }
            var newTerm = subTerm.terms[1];
            var subForVar = subTerm.terms[2];
            var subIn = subTerm.terms[3];
            // This is a nasty hack -- we always assume we can't
            // re-use variables.  This violates the assumption.  This
            // is only legit because we have ownership of subInClone
            // and ensure neither it nor any of its descendants will
            // ever be used inside any other term -- only in the proof steps.
            // subIn itself is destined to be mutated, but we need an
            // undisturbed copy to generate the steps.
            var subInClone = subIn.clone("=");
            var subType = subForVar.getType();
            var path2 = [];
            var step = [];
            var subMapping = {};
            subMapping[subForVar] = newTerm;
            var outerFirst = true;
            while (subIn.find(subForVar, path2)) {
                // TODO(pickup): questions...
                // 1) should we be using inferences or deductions to push up the stack?
                //    deductions are cleaner, but what about eubii and (A. x = y)?
                var path2Copy = path2.slice(0);
                var innerFirst = true;
                var leftEq = subForVar;
                var rightEq = newTerm;
                while (path2.length > 0) {
                    var whichChild = path2.pop();
                    var opTerm = subInClone.extract(path2.slice(0));
                    var op = opTerm.terms[0];
                    var equivThm;
                    try {
                        equivThm = GHT.EquivalenceScheme[op][whichChild - 1];
                    } catch (x) {
                        throw "No equivalence thm found for op " + op + " child " + whichChild;
                    }
                    // TODO: Ugly, ugly, hack.  We're using the '..d' form for
                    // some of these.  Need to figure out what to do with
                    // unquantified variables.
                    var isDForm = equivThm.match(/d$/);
                    if (!isDForm) {
                        step.push(leftEq, "  ", rightEq, "  ");
                    }
                    for (var i = 1; i < op.inputs.length + 1; i++) {
                        if (i != whichChild) {
                            step.push(opTerm.terms[i], "  ");
                        }
                    }
                    step.push(equivThm, "    ");
                    if (!innerFirst && !isDForm) {
                        // The stack now has:
                        // (-> (= A x) ($EQ0 $1 $2)
                        // (-> ($EQ0 $1 $2) ($EQ3 $4 $5)
                        // We want to combine these using syl.
                        step.push("syl", "    ");
                    }
                    rightEq = subIn.extract(path2.slice(0));
                    leftEq = subInClone.extract(path2.slice(0));

                    innerFirst = false;
                }
                if (!outerFirst) {
                    throw "TODO: Substiution more than once not supported.";
                    // TODO: need to also consider the case that
                    // subVar is in newTerm
                    // The stack now has:
                    // (-> (= A x) (EQ(op.type) ph ps))
                    // (-> (= A x) (EQ(op.type) ps ch))
                    // We want to combine the last two terms using the transitivity of EQ.
                    var equivThm;
                    try {
                        equivThm = GHT.EquivalenceThms[op.getType()].tr;
                    } catch (x) {
                        throw "No transitivity thm found for op " + op;
                    }
                    step.push(equivThm, "    ");
                }
                subIn = subIn.splice(path2Copy, newTerm);
                path2 = [];
                outerFirst = false;
            }
            step.push("sbcie", "    ");
            newTerm = mTermClone.splice(path.slice(0), subIn);
            // Push it up the stack
            //TODO: share code with applyArrow
            var myPath = path.slice(0);
            while (myPath.length > 0) {
                var whichChild = myPath.pop();
                var term = newTerm.extract(myPath.slice(0));
                var op = term.terms[0];
                for (var i = 1; i < op.inputs.length + 1; i++) {
                    if (i != whichChild) {
                        step.push(term.terms[i], "  ");
                    }
                }
                try {
                    step.push(GHT.EquivalenceScheme[op][whichChild - 1],"    ");
                } catch (x) {
                    throw "Step failed: op=" + op + " child=" + whichChild + ": " + x;
                }
            }
            step.push(GHT.EquivalenceScheme.mp[0], "\n");
            step.push("\n");
            var newVarMap = GHT.combineMaps(mVarMap, cloneMap);
            var newSteps = mSteps.slice(0);
            newSteps.push(step);
            var newDvs = mDvs;  // TODO: propagate DVs
            return new ProofObj(newTerm, newDvs, newSteps, newVarMap);

        };

        // Extend by performing alpha-substitution for the given variable at the given path.
        this.applyAlpha = function(path, newVar) {
             // TODO: Should share more code with applySubst, and (like it) should be less hacky.
            throw "TODO: applyAlpha";
        };
        // Extend by applying the axiom "gen", adding a universal quantification over a new variable.
        this.generify = function() {
            //TODO: check DVs here
            var cloneMap = {};
            var newTerm = mTerm.clone(cloneMap);
            var newVarMap = GHT.combineMaps(mVarMap, cloneMap);
            var newSteps = mSteps.slice(0);
            var newVar = new Variable('num');
            newTerm = new Tuple([GHT.Operators['A.'], newVar, newTerm]);
            newSteps.push([newVar, '  ', "gen\n"]);
            var newDvs = mDvs;
            return new ProofObj(newTerm, newDvs, newSteps, newVarMap);
        };
        // Extend by unifying the subterm at {@param path}, assumed to
        // have terminal binding (TODO: check this), with the named
        // theorem.  We then eliminate the subterm, and all its parent
        // terms until we find one that is not terminally-bound.
        // @param scheme an Arrow Scheme which must contain proven inferences
        this.applyDetach = function(path, name, scheme) {
            // Compute the tree of bindings from the root down to the subterm.
            var bindingAncestry = [1];
            var termAncestry = [];
            var ancestor = mTerm;
            path.forEach(function(step) {
                termAncestry.push(ancestor);
                var op = ancestor.terms[0];
                bindingAncestry.push(op.bindings[step]);
                ancestor = ancestor.terms[step];
            });
            var lastBinding = bindingAncestry[bindingAncestry.length - 1];
            if (lastBinding != -1) {
                throw "Expected terminal binding, got " + lastBinding
                    + ": path=" + path.join(",") + " term=" + mTerm.toString();
            }
            var cloneMap = {};
            var newTerm = mTerm.clone(cloneMap);
            var newVarMap = GHT.combineMaps(mVarMap, cloneMap);
            var newSteps = mSteps.slice(0);
            var example = newTerm.extract(path.slice(0));
            var template = GHT.thms[name].clone({});
            // TODO: eliminate this second unification
            var unifyMap = unify(template, example);
            newTerm = newTerm.substitute(unifyMap);
            newVarMap = GHT.combineMaps(newVarMap, unifyMap);
            var parent = termAncestry.pop();
            var child;
            while (-1 === bindingAncestry.pop()) {  // guaranteed to run at least once
                child = parent;
                parent = termAncestry.pop();
            }
            //PICKUP
            newTerm = newTerm.splice(path.slice(0), result);
        };

    };


    this.newProof = function(startingThmName) {
        var dummy = new ProofObj(null, [], [], {});
        return dummy.applyTerminal([], startingThmName);
    };
    ProofObj.prototype = new Object();
};
// Inferences used to propagate an arrowing up the tree.
// Inferences[op][n] should be an inference that transforms "x arrow
// y" into "op(..x..) arrow op(..y..)".  The direction of the arrow
// may get be reversed if the op.binding[n] is -1.
// TODO: HACK: Also, each scheme must have an 'mp' property mapping to the
// appropriate modus-ponens inference.
GHT.ArrowScheme = {  // TODO: autodetect these
    "mp": ["ax-mp", "ax-mp"], //TODO: what does this second ax-mp really mean? why does that work?
    "-.": ["con3i"],
    "->": ["imim1i", "imim2i"],
    //TODO(pickup): these aren't right
    "<->": ["imbi1i", "imbi2i"],
    "/\\": ["anim1i", "anim2i"],
    "=": ["eqeq1", "eqeq2"],
    "E.": ["exalpha", "19.22i"],
    "A.": ["alpha", "19.20i"]
    //,
};
GHT.EquivalenceScheme = {
    "mp": ["mpbi", "mpbir"],
    "e.": ["eleq1i", "eleq2i"],
    "E!": ["eualpha", "eubii"],
    "A.": ["alpha", "albii"],
    "/\\": ["anbi1i", "anbi2i"],
    "->": ["imbi1i", "imbi2i"],
    "<->": ["bibi1i", "bibi2i"],
    "=": ["eqeq1", "eqeq2"],
    "-.": ["notbii"],
    "E.": ["exalpha", "exbid"] //TODO:HACK
};
GHT.EquivalenceThms = {
    "num": {refl: "eqid", tr: "TODO:eqtr", sym: "TODO:eqsym"},
    "set": {refl: "seqid", tr: "TODO:seqtr", sym: "TODO:seqsym"},
    "wff": {refl: "biid", tr: "TODO:bitr", sym: "TODO:bisym"}
};

// Inferences used to assert the terminality of a terminal
GHT.Terminators = {
    "wff": "a1i"
};
document.getElementById("save").onclick = function() {
    var name = document.getElementById("thmName").value;
    GHT.thms[name] = GHT.theTerm;
    var theLog = "";
    var vers = GHT.getVersion();
    for (var i = 1; i <= vers; i++){
        theLog += GHT.undoStack[i].step + "\n";
    }
    theLog += "#### Save as " + name + " : "+ GHT.theTerm.toSource() + "\n";
    console.log(theLog);
};

GHT.undoStack = [];
GHT.goodVarNames = {
    'wff'://[["\u03c6", "\u03c7", "\u03c8", "\u03c9", "\u03b1", "\u03b2", "\u03b3", "\u03b4", "\u03b5"]],
    [["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M"]],
    'set':[["Z", "Y", "X", "W", "V", "U", "T", "S", "R", "Q", "P", "O", "N"]],
    'num':[["a", "b", "c", "d", "e", "f", "g",
            "h", "i", "j", "k", "l", "m"],
           ["z", "y", "x", "w", "v", "u", "t",
            "s", "r", "q", "p", "o", "n"]]
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
        var isBinding = type == 'num' ? 1 : 0;// TODO: XXX HACK PICKUP assume nums are binding, others not
        var index = typeIndices[type][isBinding ? 1 : 0]++;
        var name = varNames[type][isBinding ? 1 : 0][index];
        if (!name) name = "RAN_OUT_OF_" + type + "_" + isBinding;
        return name;
    };
    return varMap;
};
GHT.getProof = function() {
    return GHT.theProof;
};

GHT.setProof = function(proof) {
    var vers = GHT.getVersion();
    vers++;
    GHT.undoStack[vers] = {proof: proof,
                           step: GHT.theStep
                          };
    GHT.setVersion(vers);
    // This changes the window.location hash, which will call back into actuallySetProof.
};
GHT.actuallySetProof = function(proof) {
    //console.log("Setting proof: " + proof.toString());
    var div = document.getElementById("tree");
    try {
        if (GHT.theTable) div.removeChild(GHT.theTable);
    } catch (x) {
        console.log("No table?");
    }
    var cloneMap = {};
    var term = proof.getTerm(cloneMap);
    GHT.theProof = proof;
    GHT.theTerm = term;
    GHT.theVars = term.extractVars();
    GHT.theVarMap = GHT.makeVarMap(GHT.theVars, GHT.goodVarNames);
    GHT.theOnclicks = { };
    GHT.theTable =  GHT.makeTable(term, [], 1, GHT.theVarMap);
    div.appendChild(GHT.theTable);

    document.getElementById('proof').innerHTML = proof.getProof("wip").replace(/</g, '&lt;');
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
GHT.grep = function(obj, keys) {
    var newObj = {};
    keys.forEach(function(key) {newObj[key] = obj[key];});
    return newObj;
};
//loadFromServer();
GHT.autoSteps = [
/*
  // Proves id
    "GHT.theOnclicks['[]']()","GHT.theMenu.options['terminals']()","GHT.theMenu.options['ax-1']();",
    "GHT.theOnclicks['[]']()","GHT.theMenu.options['arrowees']()","GHT.theMenu.options['_axand']();",
    "GHT.theOnclicks['[1,2,1]']()","GHT.theMenu.options['arrowees']()","GHT.theMenu.options['ax-2']();",
    "GHT.theOnclicks['[]']()","GHT.theMenu.options['arrowees']()","GHT.theMenu.options['_axmp']();"
*/

  // Proves imim2
/*
    "GHT.theOnclicks['[]']();GHT.theMenu.options['terminals']();GHT.theMenu.options['ax-2']();",
    "GHT.theOnclicks['[1]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['ax-1']();",
*/
/*
    // Proves imim1
    "GHT.theOnclicks['[]']();GHT.theMenu.options['terminals']();GHT.theMenu.options['ax-1']();",
    "GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['_axand']();",
    "GHT.theOnclicks['[1,2,1]']();GHT.theMenu.options['terminals']();GHT.theMenu.options['imim2']();",
    "GHT.theOnclicks['[1,2,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['ax-1']();",
    "GHT.theOnclicks['[1,2,1,2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['ax-2']();",
    "GHT.theOnclicks['[1,2,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['ax-2']();",
    "GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['_axmp']();",
*/
/* Proves exalpha2 
"GHT.theOnclicks['[]']();GHT.theMenu.options['terminals']();GHT.theMenu.options['df-ex']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['bi2']();",
"GHT.theOnclicks['[1,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['alphasub']();",
"GHT.theOnclicks['[1,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['df-subst']();",
"GHT.theOnclicks['[1,1,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['df-ex']();",
"GHT.theOnclicks['[1,1,2,2,2,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['iman']();",
"GHT.theOnclicks['[1,1,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['annim']();",
"GHT.theOnclicks['[1,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['df-ex']();",
"GHT.theOnclicks['[1,1,2,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['notnot~']();",
"GHT.theOnclicks['[1,1,2,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['19.21']();",
"GHT.theOnclicks['[1,1,2,1,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['impexp']();",
"GHT.theOnclicks['[1,1,2,1,2,2,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['eqcom~']();",
"GHT.theOnclicks['[1,1,2,1,2,2,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['ax-eqtr']();",
"GHT.theOnclicks['[1,1,2,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['19.5']();",
"GHT.theOnclicks['[1,1,2,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['19.3']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['df-ex']();",
/* proves funlambda       
"GHT.theOnclicks['[]']();GHT.theMenu.options['terminals']();GHT.theMenu.options['df-fun']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['bi2']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['term substitute']();GHT.theMenu.options['(lambda     )']();",
"GHT.theOnclicks['[1,1,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['df-lambda']();",
"GHT.theOnclicks['[1,2,2,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['df-lambda']();",
"GHT.theOnclicks['[1,2,2,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['ax-elab']();",
"GHT.theOnclicks['[1,1,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['ax-elab']();",
"GHT.theOnclicks['[1,1,2,2]']();GHT.theMenu.options['perform substitution']();",
"GHT.theOnclicks['[1,2,2,1]']();GHT.theMenu.options['perform substitution']();",
"GHT.theOnclicks['[1,2,2,1,2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['_axand']();",
"GHT.theOnclicks['[1,2,2,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['df-an']();",
"GHT.theOnclicks['[1,2,2,1,2,2]']();GHT.theMenu.options['terminals']();GHT.theMenu.options['tyex']();",
"GHT.theOnclicks['[1,2,2,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['ancom~']();",
"GHT.theOnclicks['[1,2,2,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['19.41']();",
"GHT.theOnclicks['[1,2,2,1,2,2,1,2]']();GHT.theMenu.options['term substitute']();GHT.theMenu.options['A']();",
"GHT.theOnclicks['[1,2,2,1,2,2,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['opeq2']();",
"GHT.theOnclicks['[1,2,2,1,2,2,1,1,1]']();GHT.theMenu.options['term substitute']();GHT.theMenu.options['z']();",
"GHT.theOnclicks['[1,2,2,1,2,2,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['eqcom']();",
"GHT.theOnclicks['[1,2,2,1,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['eqcom~']();",
"GHT.theOnclicks['[1,2,2,1,2,2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['ax-eqtr']();",
"GHT.theOnclicks['[1,2,2,1,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['eqcom~']();",
"GHT.theOnclicks['[1,2,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['exalpha2']();",
"GHT.theOnclicks['[1,2,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['imex']();",
"GHT.theOnclicks['[1,2,2,2,2,2,2,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['opeq1']();",
"GHT.theOnclicks['[1,2,2,2,2,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['bi1']();",
"GHT.theOnclicks['[1,2,2,2,2,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['eqeq1']();",
"GHT.theOnclicks['[1,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['19.3']();",
"GHT.theOnclicks['[1,2,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['eqcom~']();",
"GHT.theOnclicks['[1,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['idd']();",
"GHT.theOnclicks['[1,1,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['opth']();",
"GHT.theOnclicks['[1,1,2,2,2,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['eqcom']();",
"GHT.theOnclicks['[1,1]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['pm3.35']();",
"GHT.theOnclicks['[1,1,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['ax-alim']();",
"GHT.theOnclicks['[1,1,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['df-eu']();",
"GHT.theOnclicks['[1,1,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['eximp1']();",
"GHT.theOnclicks['[1,1,2,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['ax-alim']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['dfbi2']();",
"GHT.theOnclicks['[1,1,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['pm4.76']();",
"GHT.theOnclicks['[1,1,2,2,2,2,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['impexp~']();",
"GHT.theOnclicks['[1,1,2,2,2,2,1,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['19.29']();",
"GHT.theOnclicks['[1,1,2,2,2,2,1,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['anass~']();",
"GHT.theOnclicks['[1,1,2,2,2,2,1,1,2,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[1,1,2,2,2,2,1,1,2,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['pm3.35']();",
"GHT.theOnclicks['[1,1,2,2,2,2,1,1,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['eqcom']();",
"GHT.theOnclicks['[1,1,2,2,2,2,1,1,2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['ax-eqtr']();",
"GHT.theOnclicks['[1,1,2,2,2,2,1,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['ex-nf']();",
"GHT.theOnclicks['[1,1,2,2,2,2,1,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['eqcom']();",
"GHT.theOnclicks['[1,1,2,2,2,2,1]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['bi2']();",
"GHT.theOnclicks['[1,1,2,2,2,2,1]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['eqeq2']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['bi2.04~']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['eximp1']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['pm5.31']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2,2,2,1,2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['eqeq2']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2,2,2,1,2,1,1]']();GHT.theMenu.options['term substitute']();GHT.theMenu.options['z']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['pm5.33']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2,2,2,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['pm3.35']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2,2,2,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['bi2']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['pm2.27']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['19.41']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['ancom~']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['pm5.31']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['bi2']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['eqeq2']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['eqcom']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[1,1,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['anass']();",
"GHT.theOnclicks['[1,1,2,2,2,2,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['anidm']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['pm3.35']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2,1]']();GHT.theMenu.options['terminals']();GHT.theMenu.options['tyex']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['idd']();",
"GHT.theOnclicks['[1,1,2,2,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['anidm']();",
"GHT.theOnclicks['[1,1,2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['19.3']();",
"GHT.theOnclicks['[1,1,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['19.41']();",
"GHT.theOnclicks['[1,1,2,2,1]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['pm3.35']();",
"GHT.theOnclicks['[1,1,2,2,1,2,1]']();GHT.theMenu.options['terminals']();GHT.theMenu.options['tyex']();",
"GHT.theOnclicks['[1,1,2,2,1,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['idd']();",
"GHT.theOnclicks['[1,1,2,2,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['anidm']();",
"GHT.theOnclicks['[1,1,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['anidm']();",
"GHT.theOnclicks['[1,1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['19.3']();",
"GHT.theOnclicks['[1,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['anidm']();",
"GHT.theOnclicks['[1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['19.3']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['anidm']();",
"GHT.theOnclicks['[1,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['19.3']();",
"GHT.theOnclicks['[1,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['19.3']();",
*/

];

function doStep() {
    var step = GHT.autoSteps.shift();
    if (step) eval(step);
    if (GHT.autoSteps.length) {
        window.setTimeout(doStep, 10);
    }

}
window.onload = function() {
    GHT.disableOptions = {};
    
    if (true) {    // ================ BEGINNER MODE ================
        GHT.allThms = GHT.thms;
        GHT.allOperators = GHT.Operators;
        GHT.thms = GHT.grep(GHT.allThms,
                            ["ax-1","ax-2","ax-3"
                             //,"idd","id","imim2","imim1","tied", "tie","pm2.43"
                             //,"pm2.21","con3","notnot1","notnot2","pm2.18"
                            ]);
        GHT.Operators = GHT.grep(GHT.allOperators, ["->","-."]);
        GHT.disableOptions = {'generify':1, 'equivalents':1,'initials':1, 'term substitute':1,
                              'terminals':1};
    }
    var start = (new GHT.ProofFactory()).newProof("ax-1");
    GHT.setProof(start);
    GHT.actuallySetProof(start);
    window.setTimeout(
        function() {
            window.addEventListener(
                'hashchange', function() {
                    GHT.dismiss();
                    var version = GHT.getVersion();
                    GHT.actuallySetProof(GHT.undoStack[version].proof);
                }, true);
        }, 10);
    window.setTimeout(doStep, 10);
};

document.getElementById("reset").onclick = GHT.showTerminals([], null);
