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
    return null;
    //throw "Value " + value + " not found in map " + JSON.stringify(map);
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
    // Returns a map from variables to {isBinding, paths}.  isBinding
    // will be true if the var is ever used as a binding variable
    // within this term (e.g the x in (E. x ph)).  paths is an array
    // of paths to the variable from this term.
    this.extractVars = function(set, path) {
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
    this.toString = function(varMapper) {
        if (varMapper && varMapper.__niceOperators__) { //TODO: HACK
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
    var op = GHT.Operators[s];
    if (op) return op;
    //HACK to allow goals to prompt defthms
    return new Operator(s, s, 'wff', ['wff', 'wff', 'wff'], [Infinity, Infinity, Infinity]);
}
Operator.prototype = new Term();
// Transitional function to bridge from the old varMap object to the new varMapper function.
// TODO: get rid of this
GHT.makeWrappingMapper = function(varMap) {
    var mapper = function(inVar, addIfNull) {
        // Wrapping mappers don't support addIfNull.
        return varMap[inVar];
    };
    mapper.reverse = function(x) {
        return GHT.reverseLookup(varMap, x);
    };
    return mapper;
};
function Variable(type, num) {
    if (!num) {
        if (!Variable.lastUsed) Variable.lastUsed = 1;
        num = Variable.lastUsed++;
    }

    this.toString = function(varMapper, isBinding) {
        if (varMapper) {
            return varMapper(this, true, isBinding).toString(varMapper);  // TODO: untested!
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
    this.extractVars = function(set, path) {
        if (!set) set = ({});
        if (!path) path = [];
        // If binding is already true, don't mess with it.  But if it's absent, set it to false.
        if (!set[this]) {
            set[this] = {
                isBinding:false,
                paths:[path.slice()]
            };
        } else {
            set[this].paths.push(path.slice());
        }
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
        return "TV(" + GHT.stringify(type) + ", -" + Math.abs(num) + ")";
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
    this.toString = function(varMapper) {
        var str = [];
        for (var i = 0; i < this.terms.length; i++) {
            var isBinding = false;
            if (i > 0 && isNaN(this.terms[0].bindings[i - 1])) {
                isBinding = true; // TODO: untested!
            }
            str.push(this.terms[i].toString(varMapper, isBinding));
        }
        return "(" + str.join(' ') + ")";
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
    this.extractVars = function(set, path) {
        if (!set) set = ({});
        if (!path) path = [];
        path = path.slice();
        path.push(0);
        for (var i = 1; i < terms.length; i++) {
            path.splice(path.length - 1, 1, i);
            this.terms[i].extractVars(set, path);
            if (isNaN(this.terms[0].bindings[i - 1])) {
                set[this.terms[i]].isBinding = true;
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


GHT.bindings = {
    "-1":        "terminal",   // "This, or things which arrow this."
    "0":         "exact",      // "This term, or things term-equivalent to this."
    "1":         "initial",    // "This, or things which this arrows."
    "NaN":       "binding",    // "This is a binding variable."
    "Infinity":  "unknown",    // "Unknown! No tree ops below this point."
    "-Infinity": "unknown"     // "Unknown! No tree ops below this point."
};
GHT.composeBindings = function(inBinding, opBinding) {
    // Special case to prevent Infinity * 0 = NaN
    if (opBinding == Infinity) return Infinity;
    if (opBinding == -Infinity) return -Infinity;
    if (inBinding == Infinity) return Infinity;
    if (inBinding == -Infinity) return -Infinity;
    return inBinding * opBinding;
};
GHT.Operators = {};
GHT.dismiss = function(notip) {
    if (GHT.dismiss.popup) {
        //YYY GHT.dismiss.popup.style.display = 'none';
        //YYY delete GHT.dismiss.popup;
    }
    if (!notip) { // HACK
        GHT.Tip.clear();
        GHT.Tip.showRandom();
    }
};
// turn a function into an onmouseout function that handles event bubbling.
// Stolen from http://www.quirksmode.org/js/events_mouse.html#mouseenter
GHT.makeOnMouseOut=function(element, callback) {
  element.onmouseout = function(e) {
    if (!e) e = window.event;
    var tg = (window.event) ? e.srcElement : e.target;
    //if (tg != element) return false;
    var reltg = (e.relatedTarget) ? e.relatedTarget : e.toElement;
    while (reltg) {
      // If the target is a child of the element, this is a bubble-up.
      if (reltg == element) return false;
      reltg = reltg.parentNode;
    }
    // Mouseout took place when mouse actually left layer
    return callback(e);
  };
};
GHT.newMenu = function(title, x, y) {
    var COLUMNS = 5;
    var WIDTH = "100px";
    var HEIGHT = WIDTH;
    var popup = document.getElementById("popup");
    popup.innerHTML = "";
    var i = 0;
    GHT.theMenu = {
        addOption: function(text, func, preview, previewBinding) {
            if (GHT.DisabledOptions[text]) { return; }
            var key = text;
            while (this.options[key]) key += '~';
            var td =  document.createElement("span");
            td.className = "td";
            popup.appendChild(td);
            if (preview) {
                var theVarMapper = GHT.StableMapper.mapper(GHT.theCloneMap);
                theVarMapper.__niceOperators__ = 1; // HACK for previews to look nice
                // goal-check the preview.  TODO: should check at the
                // root, not the current node.
                var previewString = preview.toString(GHT.makeVarMapper({}, GHT.goalVarNames));
                if (previewString === GHT.theGoalString) {
                    td.className += " goalmatch";
                }
                var leafs = [];
                var tree = GHT.makeTable(false, preview, [], previewBinding, theVarMapper, null, leafs);
                var fontsize = "" + (600 / leafs.length) + "%";
                tree.style.fontSize = fontsize;
                tree.id = i++;
                td.appendChild(tree);
            } else {
                td.innerHTML = text;
            }
            this.options[key] = function(e) {
                GHT.theStep += "GHT.theMenu.options['" + key + "']();";
                func(e);
            };
            this.options[key].func = func;
            td.onclick = this.options[key];

        },
        options: {
        },
        executeIfSingleton: function() {
            var opt = null;
            for (var key in this.options) {
                if (opt) {
                    return;
                }
                opt = this.options[key];
            }
            opt.func();
        }
    };
    return GHT.theMenu;
};

GHT.showTerminals = function(path, scheme, callback) {
    return function(event) {
        var menu = GHT.newMenu("Terminal", event.pageX, event.pageY);
        for (var name in GHT.Thms) {
            menu.addOption(name,
                           GHT.makeApplyFunction(path, 'Terminal', name, scheme, null, callback),
                           GHT.Thms[name], 1);
        }
    };
};

GHT.showInitials = function(path) {
    //TODO
};
GHT.showEquivalents = function(path) {
    return function() {
        var menu = GHT.newMenu("Equivalent");
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
GHT.makeThmMenu = function(menu, term, path, op, whichArg, scheme, binding) {
    var example = term;
    for (var name in GHT.Thms) {
        var thm = GHT.Thms[name];
        if (thm.terms[0] === op) {
            var template = thm.terms[whichArg];
            var otherArg = 3 - whichArg; // switch 2 and 1
            var unifyMap;
            try {
                unifyMap = unify(template, example);
            } catch (x) {
                //console.log("Could not unify "+ name + ':' + x);
                continue;
            }
            var result = thm; //YYY thm.terms[otherArg];
            result = result.substitute(unifyMap);
            menu.addOption(name, GHT.makeApplyFunction(path, 'Arrow', name, whichArg, scheme),
                           result, 1);
        }
    }
};
GHT.makeApplyFunction = function (path, whatToApply, arg1, arg2, arg3, callback) {
    return function() {
        GHT.dismiss();
        GHT.setProof(GHT.getProof()['apply' + whatToApply](path, arg1, arg2, arg3));
        if (callback) callback();
    };
};
GHT.showArrowers = function(path, binding) {
    return function() {
        var menu = GHT.newMenu("Arrower");
        var term = GHT.theTerm.extract(path.slice(0));
        GHT.makeThmMenu(menu, term, path, GHT.getArrow(term.getType()), 2, GHT.ArrowScheme, binding);
    };
};
GHT.showArrowees = function(path, binding) {
    return function() {
        var menu = GHT.newMenu("Arrowee");
        var term = GHT.theTerm.extract(path.slice(0));
        GHT.makeThmMenu(menu, term, path, GHT.getArrow(term.getType()), 1, GHT.ArrowScheme, binding);
    };
};
// Presents a list of terminals which match the given term (assumed to have terminal binding).
// When selected, performs the unification and detaches the given term.

GHT.showAssertTerminal = function(path) {
    return function() {
        var menu = GHT.newMenu("Matching Terminal");
        var term = GHT.theTerm.extract(path.slice(0));
        // TODO: share code with makeThmMenu?
        //= function(menu, term, path, op, whichArg, scheme) {
        var example = term;
        for (var name in GHT.Thms) {
            var template = GHT.Thms[name];
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
        var isBinding = theVars[oldVar].isBinding;
        if (!isBinding) {
            // Not a binding variable; we can build a term
            GHT.forEach(GHT.Operators, function(k, op) {
                            if (op.getType() === type) {
                                menu.addOption(op.getName(), doSub(op.newTerm(), false));
                            }
                        });
        }
        var theVarMapper = GHT.makeVarMapper(theVars, GHT.goodVarNames);
        GHT.forEach(theVars, function(varStr) {
                        var myVar = VariableFromString(varStr);
                        if (myVar.getType() === type) {
                            menu.addOption(theVarMapper(varStr), doSub(myVar, isBinding));
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
};
// @param pathToNodeMap: if present, this will be populated and can be
// used to map term-paths to DOM nodes.  TODO: this likely causes memory leaks.
GHT.makeTable = function(isInteractive, term, path, binding, varMapper,
                         pathToNodeMap, leafs) {
    var type;
    // Set onclick and mouseover listeners
    function decorate(td) {
        if (!isInteractive) return;
        var key = JSON.stringify(path);
        if (true) { // experimental auto-menu-open
            var timeoutId;
            td.onmouseover = function() {
                window.clearTimeout(timeoutId);
                timeoutId = window.setTimeout(td.onclick, 400);
            };
            td.onmouseout = function() {
                window.clearTimeout(timeoutId);
            };
        }
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
                menu.addOption("arrowees", GHT.showArrowees(path, binding));
            } else if (binding === 0) {
                menu.addOption("equivalents", GHT.showEquivalents(path));
            } else if (binding === -1) {
                menu.addOption("equivalents", GHT.showEquivalents(path));
                menu.addOption("arrowers", GHT.showArrowers(path, binding));
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
        span.className += "tree var type_" + type;
        span.className += " binding_" + GHT.bindings[binding];
        if (isInteractive) { span.className += " i"; }
        span.innerHTML = varMapper(term, true, isNaN(binding)); // TODO: untested!
        if (pathToNodeMap) {
            pathToNodeMap[path] = span;
        }
        decorate(span);
        if (leafs) leafs.push(span);
        return span;
    }
    if (!(term instanceof Tuple)) {
        throw "Bad term " + term;
    }
    var wrapper = document.createElement('span');
    if (pathToNodeMap) {
        pathToNodeMap[path] = wrapper;
    }

    wrapper.className = 'tree wrapper';
    if (isInteractive) { wrapper.className += " i"; }
    var op = term.terms[0];
    if (!(op instanceof Operator)) throw "Tuple starting with non-op " + op;
    type = op.getType();
    var opSpan = document.createElement('span');
    if (pathToNodeMap) {
        path.push(0);
        pathToNodeMap[path] = wrapper;
        path.pop();
    }
    wrapper.appendChild(opSpan);
    opSpan.className += "tree operator type_" + type;
    opSpan.className += " binding_" + GHT.bindings[binding];
    if (isInteractive) { opSpan.className += " i"; }
    opSpan.appendChild(document.createTextNode(op.getName().replace("<","&lt;")));
    decorate(opSpan);
    var argsSpan = document.createElement('span');
    argsSpan.className = "tree args";
    if (isInteractive) { argsSpan.className += " i"; }
    wrapper.appendChild(argsSpan);
    for (var i = 1; i < term.terms.length; i++) {
        var pathClone = path.slice(0);
        pathClone.push(i);
        var arg = (GHT.makeTable(isInteractive, term.terms[i], pathClone,
                                 GHT.composeBindings(binding, op.bindings[i - 1]),
                                 varMapper, pathToNodeMap, leafs));
        if (i == 1) {
            arg.className += " first";
        }
        arg.className += " arg";
        argsSpan.appendChild(arg);
    };
    return wrapper;

};
// Returns a map which is the transitive closure of the union of the two maps.  They must be
// disjoint, contain no false values, and create no cycles.
GHT.combineMappers = function(mapper1, mapper2) {
    var memoizer = {};
    var memoized = {};
    var reverseMemoizer = {};
    var reverseMemoized = {};
    var mapper = function(inVar, addIfNull) {
        if (memoized[inVar]) {
            var outVar = memoizer[inVar];
            if (outVar || !addIfNull) {
                return outVar;
            }
        }
        var outVar = mapper1(inVar, addIfNull) || mapper2(inVar, addIfNull);
        var answer = null;
        while (outVar) {
            answer = outVar;
            outVar = mapper1(outVar) || mapper2(outVar);
        }
        memoized[inVar] = true;
        memoizer[inVar] = answer;
        return answer;
    };
    mapper.reverse = function(inVar) {
        if (reverseMemoized[inVar]) {
            return reverseMemoizer[inVar];
        }
        var outVar = mapper1.reverse(inVar) || mapper2.reverse(inVar);
        var answer = null;
        while (outVar) {
            answer = outVar;
            outVar = mapper1.reverse(outVar) || mapper2.reverse(outVar);
        }
        reverseMemoized[inVar] = true;
        reverseMemoizer[inVar] = answer;
        return answer;
    };
    return mapper;
};

// A ProofObj is an immutable object encapsulating a Term and a Ghilbert proof of that term's truth.
// The internal structure of the Ghilbert proof is modeled in private variables so that the proof
// can be extended into a new ProofObj.  External clients may call proofObj.getTerm() to get a
// mutable clone of the Term, proofObj.getProof() to get the complete ghilbert proof, or
// proofObj.toString() to get a diagnostic dump of the proof's structure.  To ensure validity,
// external code cannot construct ProofObjs directly but must invoke newProof from a ProofFactory.
GHT.ProofFactory = function() {
    var GHILBERT_VAR_NAMES = {
        'wff':[["A", "B", "C", "D", "E", "F", "G", "H"]],
        'set':[["S", "T", "U", "V"]],
        'num':[["a", "b", "c", "d", "e", "f", "g", "h"],
               ["z", "y", "x", "w", "v",
                "z'", "y'", "x'", "w'", "v'"]]
    };

    // This Constructor is private since it must be called with care.  The values passed in must all
    // be consistent.  mTerm may be null, but the resulting dummy proofObj must be immediately
    // extended with applyTerminal([], ...).  The constructed proofObj takes ownership of the passed
    // parameters, and will never change them.  In order to preserve immutability, no other
    // reference should be kept to them or their components (except by other ProofObjs which will
    // also never change them.)
    //TODO: consider making terms immutable to make this easier.
    function ProofObj(mTerm, mDvs, mSteps, mVarMapper) {
        if (!mVarMapper) throw "No varmapper!";
        // Public accessors
        this.getTerm = function(mapping) {
            return mTerm.clone(mapping);
        };
        // Given a variable, reverse map it as far as possible and return the original.
        this.reverseMap = function(varObj) {
            return mVarMapper.reverse(varObj);
        };
        // Given a map of var names (e.g. *_VAR_NAMES), return a mapping from
        // our internal vars to the given names._
        this.getVarMapper = function(varNames, reset) {
            return GHT.combineMappers(mVarMapper,
                                      GHT.makeVarMapper(mTerm.extractVars(), varNames, reset));
        };
        function flatten(array, mapper, delimiter) {
            function flattenInner(arr) {
                if (!arr) {
                    return "*NULL*";
                } else if (arr instanceof Array) {
                    return arr.map(flattenInner).join(delimiter ? delimiter : "");
                } else {
                    return arr.toString(mapper);
                }
            }
            return flattenInner(array);
        }

        // Produce a complete ghilbert proof, with the given theorem name.
        this.getProof = function(thmName) {
            return flatten(["thm (", thmName,
                            " (", mDvs, ") () ",
                            mTerm,
                            "\n", mSteps, ")"],
                           this.getVarMapper(GHILBERT_VAR_NAMES, true));
        };
        // Produce ghilbert defthm.  We assume the left child of the root will become the new op,
        // with variables in appearence-order.  Returns [term, proof, newOperatorSource].
        this.defthm = function(opName) {
            var varList = [], typeList = [], bindingList = [];
            var cloneMap = {};
            var newTerm = mTerm.clone(cloneMap);
            var newVarMapper = GHT.combineMappers(mVarMapper, GHT.makeWrappingMapper(cloneMap));
            var newTermVars = newTerm.extractVars();
            GHT.forEach(
                newTermVars,
                function(k) {
                    var vv = VariableFromString(k);
                    varList.push(vv);
                    typeList.push(vv.getType());
                    var binding =
                        newTermVars[k].isBinding ? NaN : Infinity;
                    bindingList.push(binding); // TODO: can we autodetect bindings here?
                });
            var outType = newTerm.terms[1].getType();
            var newOp = new Operator(opName, opName, outType, typeList, bindingList);
            var newOpSource = "GHT.Operators['" + opName + "'] = new Operator('"
                + opName + "','" + opName + "','" + outType +
                "',['" + typeList.join("','") + "'],[" + bindingList.join(",") + "]);\n";
            GHT.Operators[opName] = newOp;
            varList.unshift(newOp);
            newTerm.terms[1] = new Tuple(varList);
            var mapper = GHT.combineMappers(
                newVarMapper,
                GHT.makeVarMapper(newTerm.extractVars(),
                                  GHILBERT_VAR_NAMES, true));

            varList = flatten(varList.slice(1), mapper, " ");
            var proof = flatten(["defthm (df-", opName,
                                 " ", outType,
                                 " (", opName, " ", varList, ") ",
                                 " (", mDvs, ") () ",
                                 newTerm, "\n", mSteps, ")"],
                                mapper);
            return [newTerm, proof, newOpSource];
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
            var terminalTerm = GHT.Thms[name].clone({});
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
                return new ProofObj(terminalTerm, newDvs, [newStep], GHT.makeWrappingMapper(newVarMap));
            } else {
                newStep.push("    ");
                var termToReplace = mTerm.extract(path.slice(0));
                newStep.push(termToReplace, "  ",
                             GHT.Terminators[termToReplace.getType()], "    ");
                //TODO: share code with applyArrow
                var cloneMap = {};
                var newTerm = mTerm.clone(cloneMap);
                var newVarMapper = GHT.combineMappers(mVarMapper, GHT.makeWrappingMapper(cloneMap));
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
                return new ProofObj(newTerm, newDvs, newSteps, newVarMapper);
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
            var newVarMapper = GHT.combineMappers(mVarMapper, GHT.makeWrappingMapper(cloneMap));

            var example = newTerm.extract(path.slice(0));
            var thm = GHT.Thms[name].clone({});
            var template = thm.terms[templateArg];
            // TODO: eliminate this second unification
            var unifyMap = unify(template, example);
            var result = thm.terms[3 - templateArg].substitute(unifyMap);
            for (var varStr in thm.extractVars()) {
                newStep.push(VariableFromString(varStr), "  ");
            }
            newVarMapper = GHT.combineMappers(newVarMapper, GHT.makeWrappingMapper(unifyMap));
            newStep.push(name, "\n");
            newTerm = newTerm.substitute(unifyMap);
            newTerm = newTerm.splice(path.slice(0), result);
            // Travel up the path to the root term, applying stock inferences along the way
            var myPath = path.slice(0);
            var headRoot = (templateArg == 2 ? newTerm : mTerm);
            var tailRoot = (templateArg == 1 ? newTerm : mTerm);
            var mpIndex = templateArg - 1;
            while (myPath.length > 0) {
                newStep.push([headRoot.extract(myPath.slice(0)), "  ",
                              tailRoot.extract(myPath.slice(0)), "  "]);
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
                newStep.push(pushUpThm, "    ", "ax-mp", "\n    ");
                if (op.bindings[whichChild - 1] == -1) {
                    // This arrowing theorem will switch the order of our mandhyps.
                    var tmp = headRoot;
                    headRoot = tailRoot;
                    tailRoot = tmp;
                    mpIndex = 1 - mpIndex;
                }
            }
            newStep.push(scheme.mp[mpIndex], "\n");
            var newSteps = mSteps.slice(0);
            newSteps.push(newStep);
            var newDvs = mDvs.slice(0); // TODO: copy over from thm
            var newProof = new ProofObj(newTerm, newDvs, newSteps, newVarMapper);
            newProof.parentProof = this;
            // Set up animation hints.  animations is an array of {src, dsts}.
            // src is the path to a term that should be a source in the animation.
            // dsts is an array of paths to which the source should be animated.
            newProof.animations = [];
            var beforeVars = thm.terms[templateArg].extractVars();
            var afterVars = thm.terms[3 - templateArg].extractVars();
            GHT.forEach(
                beforeVars,
                function(varStr, result) {
                    // Only the first occurence of the var on
                    // in the template is an animation source.
                    var srcPath = path.slice();
                    srcPath.push.apply(srcPath, result.paths[0]);
                    var dsts = [];
                    // Each of the occurences in the result is a destination.
                    if (afterVars[varStr]) {
                        afterVars[varStr].paths.forEach(
                            function(afterPath) {
                                var dstPath = path.slice();
                                dstPath.push.apply(dstPath, afterPath);
                                dsts.push(dstPath);
                            });
                        newProof.animations.push({src:srcPath, dsts:dsts});
                    }
                });
            return newProof;
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
            var newVarMapper = GHT.combineMappers(mVarMapper, GHT.makeWrappingMapper(mapping));
            var newSteps = mSteps.slice(0);
            var newDvs = mDvs;  // TODO: propagate DVs forward through replacement
            return new ProofObj(newTerm, newDvs, newSteps, newVarMapper);
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
                        // TODO(pickup): This needs to be recast to
                        // use deductions instead of inferences, as applyArrow has.
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
            var newVarMap = GHT.combineMappers(mVarMapper, GHT.makeWrappingMapper(cloneMap));
            var newSteps = mSteps.slice(0);
            newSteps.push(step);
            var newDvs = mDvs;  // TODO: propagate DVs
            return new ProofObj(newTerm, newDvs, newSteps, newVarMapper);

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
            var newVarMapper = GHT.combineMappers(mVarMapper, GHT.makeWrappingMapper(cloneMap));
            var newSteps = mSteps.slice(0);
            var newVar = new Variable('num');
            newTerm = new Tuple([GHT.Operators['A.'], newVar, newTerm]);
            newSteps.push([newVar, '  ', "gen\n"]);
            var newDvs = mDvs;
            return new ProofObj(newTerm, newDvs, newSteps, newVarMapper);
        };
        // Extend by unifying the subterm at {@param path}, assumed to
        // have terminal binding (TODO: check this), with the named
        // theorem.  We then eliminate the subterm, and all its parent
        // terms until we find one that is not terminally-bound.
        // @param scheme an Arrow Scheme which must contain proven inferences
        // TODO: this is currently not functional
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
            var newVarMapper = GHT.combineMapper(mVarMapper, GHT.makeWrappingMapper(cloneMap));
            var newSteps = mSteps.slice(0);
            var example = newTerm.extract(path.slice(0));
            var template = GHT.Thms[name].clone({});
            // TODO: eliminate this second unification
            var unifyMap = unify(template, example);
            newTerm = newTerm.substitute(unifyMap);
            newVarMapper = GHT.combineMapper(newVarMapper, GHT.makeWrappingMapper(unifyMap));
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
        console.log("newProof: " + startingThmName);
        var dummy = new ProofObj(null, [], [], GHT.makeWrappingMapper({}));
        return dummy.applyTerminal([], startingThmName);
    };
    ProofObj.prototype = new Object();
};

GHT.undoStack = [];
GHT.goodVarNames = {
    'wff': [["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M"]],
    'set': [["Z", "Y", "X", "W", "V", "U", "T", "S", "R", "Q", "P", "O", "N"]],
    'num': [["a", "b", "c", "d", "e", "f", "g",
             "h", "i", "j", "k", "l", "m"],
            ["z", "y", "x", "w", "v", "u", "t",
             "s", "r", "q", "p", "o", "n"]]
};
GHT.goalVarNames = {
    'wff': [["1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13"]],
    'set': [["!", "@", "#", "$", "%", "&amp;", "*", "(", ")", "-", "="]],
    'num': [["&alpha;", "&beta;", "&gamma;", "&delta;", "&epsilon;", "&zeta;", "&eta;",
             "&theta;", "&iota;", "&kappa;", "&lambda;", "&mu;"],
            ["&omega;", "&chi;", "&xi;", "&phi;", "&upsilon;", "&tau;",
             "&sigma;", "&rho;", "&pi;", "&omicron;", "&psi;", "&nu;"]]
};
// Input: a map from vars to isBinding, and one of GHT.*VarNames
// Output: a function that takes a varString and returns a human-readable string.
// If you want yourself added to the varMapper when not found, pass a second true argument.
GHT.makeVarMapper = function(vars, varNames) {
    var typeIndices = {
        wff: [0, 0], set: [0, 0], num: [0, 0]
    };
    var varMap = GHT.forEach(vars,
        function(varStr, result, varMap) {
            if (varMap[varStr]) return varMap;
            var type = VariableFromString(varStr).getType();
            var index = typeIndices[type][result.isBinding ? 1 : 0]++;
            var name = varNames[type][result.isBinding ? 1 : 0][index];
            if (!name) name = "RAN_OUT_OF_" + type + "_" + result.isBinding;
            if (name.toString() === varStr.toString()) throw "loop!";
            varMap[varStr] = name;
            return varMap;
        }, {});
    function addNewVar(varObj, isBinding) {
        var type = varObj.getType();
        var index = typeIndices[type][isBinding ? 1 : 0]++;
        if (type == 'wff') isBinding = false; // HACK: for the case of 0 * Infinity = NaN
        var name = varNames[type][isBinding ? 1 : 0][index];
        if (!name) name = "RAN_OUT_OF_" + type + "_" + isBinding;
        varMap[varObj] = name;
        if (name.toString() === varObj.toString()) throw "loop!";
        return name;
    };
    return function(inVar, addIfNull, isBinding) {
        if (varMap[inVar]) {
            return varMap[inVar];
        } else if (addIfNull) {
            return addNewVar(inVar, isBinding);
        } else {
            return null;
        }
    };
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

GHT.getPos = function(node) {
    var x = 0;
    var y = 0;
    do {
        y += node.offsetTop;
        x += node.offsetLeft;
    } while ((node = node.offsetParent));
    return [x,y];
};
// Makes a deep clone of @param oldNode, positions it on top of the original,
// then animates it to the position of @param newNode.  When the clone gets
// there, it will be removed.
GHT.sendNodeToNode = function(oldNode, newNode) {
    var clone = oldNode.cloneNode(true);
    // Hide the destination until the animator gets there
    newNode.style.visibility = "hidden";
    var parent = document.body;
    parent.appendChild(clone);
    clone.style.position = "absolute";
    var oldNodeCoords = GHT.getPos(oldNode);
    clone.style.left = oldNodeCoords[0];
    clone.style.top = oldNodeCoords[1];
    clone.style.width = oldNode.offsetWidth;
    clone.style.height = oldNode.offsetHeight;
    var newNodeCoords = GHT.getPos(newNode);
    clone.className += " animated";
    clone.style.left = newNodeCoords[0];
    clone.style.top = newNodeCoords[1];
    clone.style.width = newNode.offsetWidth;
    clone.style.height = newNode.offsetHeight;

    GHT.onTransitionEnd(clone, function() {
                            parent.removeChild(clone);
                            newNode.style.visibility = "visible";
                       });
};
GHT.onTransitionEnd = function(node, callback, forceDelay) {
    var transitions = forceDelay ||
        RegExp(" AppleWebKit/").test(navigator.userAgent) ||
        RegExp("Firefox/4").test(navigator.userAgent) ||
        RegExp("Fennec").test(navigator.userAgent);
    // TODO: perhaps this should use webkitTransitionEnd, but that seemed to be buggy, and
    // would leave other browsers stuck with the extra children.
//Mozilla/5.0 (X11; U; Linux x86_64; en-US; rv:1.9.2.13) Gecko/20101206 Ubuntu/10.04 (lucid) Firefox/3.6.13
    var timeout = transitions
        ? 1000 // HACK: this must be synced with CSS -webkit-transition-duration
        : 0; //XXX
    window.setTimeout(callback, timeout);

};
/*
GHT.redecorate = function(changed) {
 XXX
    document.getElementById("defthm").style.display = GHT.DisabledOptions.nodefthm ?
        "inline" : "none";
    GHT.autoGoal(GHT.theProof);
    var div = document.getElementById("tree");
    var oldTable = GHT.theTable;
    var oldPathToNodeMap = GHT.thePathToNodeMap;
    var newPathToNodeMap = {};
    var newTable =  GHT.makeTable(true, GHT.theTerm, [], 1,
                                  GHT.StableMapper.mapper(), newPathToNodeMap, []);
    GHT.theTable = newTable;
    GHT.thePathToNodeMap = newPathToNodeMap;

    if (oldTable) {
        // oldTable has position relative, and keeps the div from collapsing.
        // newTable can be absolute until oldTable disappears.
        newTable.style.position = 'absolute';
        newTable.style.top = 0;
        newTable.style.left = 0;
    }
    GHT.StableMapper.end();
    div.appendChild(newTable);
    newTable.style.opacity = 0;
    try {
        if (oldTable) {
            // Figure out if animations apply, and whether they should go in forward or reverse.
            var animations = null;
            var srcMap, dstMap, forward;
            if (changed) {
              if ((GHT.theProof.parentProof == GHT.thePreviousProof)
                  && GHT.theProof.animations) {
                animations = GHT.theProof.animations;
                srcMap = oldPathToNodeMap;
                dstMap = newPathToNodeMap;
                forward = true;
              } else if ((GHT.thePreviousProof.parentProof == GHT.theProof)
                  && GHT.thePreviousProof.animations) {
                animations = GHT.thePreviousProof.animations;
                dstMap = oldPathToNodeMap;
                srcMap = newPathToNodeMap;
                forward = false;
              }
            }
            if (animations) {
                animations.forEach(
                    function(animation) {
                        var srcNode = srcMap[animation.src];
                        if (srcNode) {
                            animation.dsts.forEach(
                                function(dstPath) {
                                    var dstNode = dstMap[dstPath];
                                    if (dstNode) {
                                        if (forward) {
                                            GHT.sendNodeToNode(srcNode, dstNode);
                                        } else {
                                            GHT.sendNodeToNode(dstNode, srcNode);
                                            dstNode.style.visibility = "hidden";
                                        }
                                    }
                                });
                            if (forward) {
                                // Hide the original since the clones are animating away
                                srcNode.style.visibility = "hidden";
                            }
                        }
                    });
            }
            oldTable.style.opacity = 0;
            GHT.onTransitionEnd(oldTable, function(e) {
                                    newTable.style.position = 'relative';
                                    div.removeChild(oldTable); });
        }
    } catch (x) {
        console.log(x);
    }
    window.setTimeout( function() { newTable.style.opacity = 100;}, 0);
};
*/
GHT.actuallySetProof = function(proof) {
    //console.log("Setting proof: " + proof.toString());
    var cloneMap = {};
    var term = proof.getTerm(cloneMap);
    GHT.dismiss(true);
    GHT.thePreviousProof = GHT.theProof;
    GHT.theProof = proof;
    GHT.theTerm = term;
    GHT.theCloneMap = cloneMap;
    GHT.theVars = term.extractVars();
    GHT.theOnclicks = { };
    GHT.redecorate(true);
    GHT.autoGoal(proof);
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

// The stableMapper is a special varMapper that allows display names
// to stay stable from one proof object to the next.  It also tracks
// which variables are unused in the final product, so that they can
// be recycled when all other variable names are used up.
GHT.StableMapper = {
    end: function() {
        //TODO: support variable recycling
    },
    mapper:function() {
        var varNames = {
            available: {
                'wff': [["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M"]],
                'set': [["Z", "Y", "X", "W", "V", "U", "T", "S", "R", "Q", "P", "O", "N"]],
                'num': [["a", "b", "c", "d", "e", "f", "g",
                         "h", "i", "j", "k", "l", "m"],
                        ["z", "y", "x", "w", "v", "u", "t",
                         "s", "r", "q", "p", "o", "n"]]
            },
            used:  {
                'wff': [[]],
                'set': [[]],
                'num': [[], []]
            }
        };
        var vers = GHT.getVersion();
        var runningVarMap = {};
        for (var i = GHT.theFirstStep; i <= vers; i++){
            var cloneMap;
            var term;
            if (i == vers) {
                // We need to match the one used in redecorate.  TODO(hack).
                cloneMap = GHT.theCloneMap;
                term = GHT.theTerm;
            } else {
                cloneMap = {};
                term = GHT.undoStack[i].proof.getTerm(cloneMap);
            }
            var vars = term.extractVars();
            runningVarMap = GHT.forEach(
                vars,
                function(newVarStr, result, varMap) {
                    var origVarStr = GHT.reverseLookup(cloneMap, newVarStr);
                    var varStr = GHT.undoStack[i].proof.reverseMap(origVarStr) || origVarStr;
                    if (varMap[varStr]) {
                        varMap[newVarStr] = varMap[varStr];
                        varMap[origVarStr] = varMap[varStr];
                        return varMap;
                    }
                    var type = VariableFromString(varStr).getType();
                    var name = varNames.available[type][result.isBinding ? 1 : 0].shift();
                    if (name) {
                        varNames.used[type][result.isBinding ? 1 : 0].push(name);
                    } else {
                        name = varStr;
                    }
                    varMap[varStr] = name;
                    varMap[origVarStr] = name;
                    varMap[newVarStr] = name;
                    return varMap;
                }, runningVarMap);

        }

        // These are used for new variables introduced in previews.
        var temporaries = {};
        return function(inVar, addIfNull, isBinding) {
            var result = runningVarMap[inVar] || temporaries[inVar];
            if (!result && addIfNull) {
                // addIfNull is only needed in previews.  The result
                // only lasts as long as this mapper.
                var type = inVar.getType();
                result = varNames.available[type][isBinding ? 1 : 0].shift();
                temporaries[inVar] = result;
            }
            return result;
        };
    }
};

GHT.termFromSexp = function(sexp) {
    var i = 0;
    function consumeWhitespace() {
        while (sexp.charAt(i) == ' ') i++;
    }
    function consumeToken() {
        var start = i;
        while (sexp.charAt(i) != ' ' && sexp.charAt(i) != ')') i++;
        return sexp.substring(start, i);
    }
    function consumeBalanced() {
        // Assumes sexp.charAt(i) = "(".  moves i past the matching close-parenthesis. returns
        // the term constructed along they way.
        i++;
        var args = [];
        args.push(O(consumeToken()));
        var j = 0;
        while (sexp.charAt(i) != ")") {
            consumeWhitespace();
            if (sexp.charAt(i) == "(") {
                args.push(consumeBalanced());
            } else {
                var varName = consumeToken();
                var type = args[0].inputs[j];
                var num = 0;
                for (var k = 0; k < varName.length; k++) {
                    num += varName.charCodeAt(k);
                    num *= 256;
                }
                args.push(TV(type, num));
            }
            j++;
        }
        i++;
        return T(args);
    }
    return consumeBalanced();
};

// Automatic goal assistance.  Check the given proof for matching the
// current goal, and if it does, give the user a hint that it's time to save.
GHT.autoGoal = function(proof) {
    if (!GHT.theGoal) return;
    var ghProof = proof.getProof("thmName");
    var match = ghProof.match(
        "\\(\\) " + GHT.theGoal.replace(/\\/g, "\\\\").replace(/\(/g,"\\(").replace(/\)/g,"\\)"));
    var label =document.getElementById("autogoal");
    label.style.visibility = match ? "visible" : "hidden";
    label.style.left = match ? 0 : "20em";
    if (match) {
        var name = "myTerminal";
        var i = 0;
        while (GHT.Thms[name + i]) i++;
        document.getElementById("theorem.name").value = name + i;
    }
};

GHT.setVersion(0);
window.onload = function() {
/*
    var start = (new GHT.ProofFactory()).newProof("ax-1");
    GHT.setProof(start);
    GHT.actuallySetProof(start);
*/
            window.addEventListener(
                'hashchange', function() {
                    var version = GHT.getVersion();
                    if (GHT.undoStack[version]) {
                        GHT.actuallySetProof(GHT.undoStack[version].proof);
                    }
                }, true);
};
/*
document.getElementById("reset").onclick = function(e) {
    function callback() {
        GHT.theFirstStep = GHT.getVersion();
    }
    GHT.theStep = "GHT.showTerminals([], null, setfirst)({pageX:0,pageY:0});";
    GHT.showTerminals([], null, callback)(e);
};
*/
GHT.theFirstStep = 1;
