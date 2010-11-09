var GHT = { };
// A Term is an Operator, a Variable, or a Tuple of Terms.
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
function Operator(name, type, inputs, bindings) {
    this.toString = function() {return name;};
    this.inputs = inputs;
    this.bindings = bindings;
    this.getType = function() {
        return type;
    };
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
        return "$" + this.index;
    };
    this.clone = function(mapping) {
        if (!mapping[this]) mapping[this] = new Variable();
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
        set[this] = true;
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
}
Variable.prototype = new Term();
function BindingVariable(type, num) {
    this.type = type;
    if (num) {
        this.index = num;
    } else {
        if (!Variable.lastUsed) Variable.lastUsed = 1;
        this.index = Variable.lastUsed++;
    }
    this.getType = function() {
        return type;
    };
}
BindingVariable.prototype = new Variable();

function V(num) {
    return new Variable('wff',num);
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
    this.extractVars = function(set) {
        if (!set) set = ({});
        this.terms.forEach(function(t) {t.extractVars(set);});
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

var Implies = new Operator("\u2192", 'wff', ['wff', 'wff'], [-1, 1]);
var Not = new Operator("\u00ac", 'wff', ['wff'], [-1]);
var True = new Operator("t", 'wff', [], []);
GHT.Operators = {
    '->': Implies,
    '-.': Not,
    't': True
};

var P, Q, R, S, U;
var thms = {
    ax1: T(Implies, P = V(), T(Implies, Q = V(), P)),
    ax2: T(Implies, T(Implies, P = V(), T(Implies, Q = V(), R = V())),
            T(Implies, T(Implies, P, Q), T(Implies, P, R))),
    ax3: T(Implies, T(Implies, T(Not, P = V()), T(Not, Q = V())), T(Implies, Q, P)),
    axmp: T(Implies, T(Not, T(Implies, P = V(), T(Not, T(Implies, P, Q = V())))), Q),
    axand: T(Implies, P=V(), T(Not, T(Implies, P, T(Not, T(True)))))
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


// Convert a ghilbert-style sexp into one of our Term objects.
// References window.direct.vg to look up type information.
function TermFromSexp(sexp) {
    // Is it a Tuple?
    if (sexp instanceof Array) {
        return T(sexp.map(TermFromSexp));
    } 
    // Is it a Variable?
    var sym = window.direct.vg.syms[sexp];
    if (sym) {
        switch (sym[0]) {
        case 'var':
            return new BindingVariable(sym[1], hash(sexp));
        case 'tvar':
            return new Variable(sym[1], hash(sexp));
        }
    }
    // Is it an Operator?
    var term = window.direct.vg.terms[sexp];
    if (term) {
        if (!Operators[sexp]) {
            // Attemp to make it on the fly
            var type = term[0];
            var inputs = term[1];
            var bindings = term[2].map(function(x) {
                                           // TODO: bogus
                                           if (x === null) return 0; // exact ?
                                           if (x.length === 0) return NaN; // binding ?
                                           if (x.length === 1) return NaN; // WTF is with [/] ?
                                           return 0; // *shrug*
                                       });
            Operators[sexp] = new Operator(GH.sexptounicode(sexp), type, inputs, bindings);
        }
        return Operators[sexp];
    }
    // What the hell is it?!
    throw "Unknown sexp: " + sexp;
}

GHT.log = [];
GHT.arrows = {
    'wff': '->',
    'num': '<=',
    'set': 'C_'
};
GHT.bindings = {
    "-1": "terminal", // "This, or things which arrow this."
    "0": "exact",     // "This term, or things term-equivalent to this."
    "1": "initial",   // "This, or things which this arrows."
    "NaN": "none"     // "This is a binding variable."
};
GHT.operators = {
    '->': {inputs: ['wff', 'wff'],
           bindings: [-1, 1],
           output: 'wff',
           display: '\u2192'
          },
    '-.': {inputs: ['wff'],
           bindings: [-1],
           output: 'wff',
           display: '\u00ac'
          },
    'A.': {inputs: ['tvar', 'wff'],
           bindings: [NaN, 1],
           output: 'wff',
           display: 'A.' //TODO
          },
    'E.': {inputs: ['tvar', 'wff'],
           bindings: [NaN, 1],
           output: 'wff',
           display: 'E.' //TODO
          },
    '/\\': {inputs: ['wff', 'wff'],
           bindings: [1, 1],
           output: 'wff',
           display: '/\\' //TODO
          },
    '<': {inputs: ['num', 'num'],
           bindings: [-1, 1],
           output: 'num',
           display: '&lt;' //TODO
          },
    'e.': {inputs: ['num', 'set'],
           bindings: [0, 1],
           output: 'wff',
           display: 'e.' //TODO
          },
    'relprim': {inputs: ['num', 'num'],
           bindings: [NaN, NaN],
           output: 'wff',
           display: 'relprim' //TODO
          },
    'S': {inputs: ['num'],
           bindings: [1],
           output: 'num',
           display: 'S' //TODO
          },
    '|': {inputs: ['num', 'num'],
           bindings: [0, 0],
           output: 'wff',
           display: '|' //TODO
          },
    'true': {inputs: [],
             bindings: [],
             output: 'wff',
             display:'t'
          },
    '0':  {inputs: [],
           bindings: [],
           output: 'num',
           display:'0'
          }
};
GHT.vars = {
    'ph': {type: 'wff',
           display:'\u03c6'        
          },
    'ps': {type: 'wff',
           display:'\u03c8'        
          },
    'ch': {type: 'wff',
           display:'\u03c7'        
          },
    'A': {type: 'var',
           display:'A'
          },
    'B': {type: 'var',
           display:'B'
          },
    'x': {type: 'tvar',
           display:'x'
          },
    'y': {type: 'tvar',
           display:'y'
          },
    'z': {type: 'tvar',
           display:'z'
          },
    'S': {type: 'set',
           display:'S'
          },
    'T': {type: 'set',
           display:'T'
          }
};
GHT.terminals = {
    wff: {
        "true" :{
            sexp: ['true']
        },
        "ax-1": {
         sexp: ['->', 'ph', ['->', 'ps', 'ph']]
        },
        "ax-2": {
         sexp: ['->', ['->', 'ph', ['->', 'ps', 'ch']],
                ['->', ['->', 'ph', 'ps'],['->', 'ph', 'ch']]]
        },
        "ax-3": {
         sexp: ['->', ['->', ['-.', 'ph'],['-.', 'ps']],['->', 'ps', 'ph']]
        },
        "ax-mp_": {
         sexp: ['->', ['-.', ['->', 'ph', ['-.', ['->', 'ph', 'ps']]]],'ps']
        },
        "ax-antrue": {
         sexp: ['->', 'ph', ['-.', ['->', 'ph', ['-.', 'true']]]]
        },
        "relprimex.3": {
                        sexp:["->", ["->", ["A.", "x", ["A.", "y", ["->", ["/\\", ["e.", "x", "S"], ["e.", "y", "T"]], ["relprim", "x", "y"]]]], ["E.", "z", ["/\\", ["A.", "y", ["->", ["/\\", ["<", ["S", ["S", "y"]], "A"], ["e.", ["S", ["S", "y"]], "S"]], ["|", ["S", ["S", "y"]], "z"]]], ["A.", "y", ["->", ["e.", ["S", ["S", "y"]], "T"], ["-.", ["|", ["S", ["S", "y"]], "z"]]]]]]], ["->", ["A.", "x", ["A.", "y", ["->", ["/\\", ["e.", "x", "S"], ["e.", "y", "T"]], ["relprim", "x", "y"]]]], ["E.", "z", ["/\\", ["A.", "y", ["->", ["/\\", ["<", ["S", ["S", "y"]], ["S", "A"]], ["e.", ["S", ["S", "y"]], "S"]], ["|", ["S", ["S", "y"]], "z"]]], ["A.", "y", ["->", ["e.", ["S", ["S", "y"]], "T"], ["-.", ["|", ["S", ["S", "y"]], "z"]]]]]]]]
                       }
    }
};


GHT.initials = {
/*
    'wff': {
         'false' : {
             display:'nil'
         }
     }
*/
    'num': {
        sexp: ['0']
    }
};
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
        for (name in thms) {
            menu.addOption(name, GHT.makeSwap(path.slice(0), thms[name], "T:" + name));
        }
    };
};

GHT.showInitials = function(path) {
};
GHT.showArrowers = function(path) {
    return function() {
        var menu = GHT.newMenu("Arrowers");
        for (name in thms) {
            var thm = thms[name];
            if ((thm instanceof Tuple) && (thm.terms[0] == Implies)) {
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
        for (name in thms) {
            var thm = thms[name];
            if ((thm instanceof Tuple) && (thm.terms[0] == Implies)) {
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
GHT.showVars = function(path) {
};
GHT.showTermBuilder = function(path, type) {
    return function() {
        GHT.dismiss();
        var termString = prompt("Type a term string, e.g. T(Implies, P = V(), T(Implies, Q = V(), P))");
        var term;
        try {
            term = eval(termString);
            if (!(term instanceof Term)) {
                throw "Not a term: " + term;
            }
            if (term.getType() !== type) {
                throw "Bad type: wanted " + type + " but got " + term.getType();
            }
        } catch (x) {
            alert(x);
            return;
        }
        var theVar = GHT.extract(GHT.theTerm, path.slice(0));
        var mapping = {};
        mapping[theVar] = term;
        GHT.setTerm(GHT.theTerm.substitute(mapping));
        console.log("#### Substituted " + termString + " at " + path);
    };
};
GHT.makeTable = function(term, path, binding) {
    var table = document.createElement('table');
    var type;
    function setOnClick(td) {
        td.onclick = function(event) {
            var menu = GHT.newMenu(GHT.bindings[binding] + " " + type,
                                   event.pageX, event.pageY);
            if (binding === 1) {
                menu.addOption("terminals", GHT.showTerminals(path));
                menu.addOption("arrowees", GHT.showArrowees(path));
            } else if (binding === 0) {
                menu.addOption("equivalents", GHT.showEquivalents(path));
            } else if (binding === -1) {
                menu.addOption("initials", GHT.showInitials(path));
                menu.addOption("arrowers", GHT.showArrowers(path));
            } 
            if (isNaN(binding)) {
                menu.addOption("rebind", GHT.showVars(type, path));
            } else if (term instanceof Variable) {
                menu.addOption("term substitute", GHT.showTermBuilder(path, type));
            }            
        };
    }

    if (term instanceof Variable) {
        var td = document.createElement('td');
        type = term.getType();
        td.className = "type_" + type;
        td.innerHTML = term.toString();
        setOnClick(td);
        return td;
    }
    if (! (term instanceof Tuple)) {
        throw "Bad term " + term;
    }
    var op = term.terms[0];
    type = op.output;
    table.className += "type_" + type;
    table.className += "binding_" + GHT.bindings[binding];
    table.cols = op.inputs.length;
    var tr = document.createElement('tr');
    table.appendChild(tr);
    var td = document.createElement('td');
    setOnClick(td);
    tr.appendChild(td);
    td.colSpan = op.inputs.length;
    td.className = 'operator';
    td.innerHTML = op.toString();
    tr = document.createElement('tr');
    table.appendChild(tr);
    for (var i = 1; i < term.terms.length; i++) {
        var pathClone = path.slice(0);
        pathClone.push(i);
        tr.appendChild(GHT.makeTable(term.terms[i], pathClone, binding * op.bindings[i - 1]));
    };
    return table;

};
document.getElementById("save").onclick = function() {
    var name = document.getElementById("name").value;
    console.log("#### Save as " + name);
    thms[name] = GHT.theTerm;
};
GHT.setTerm = function(term) {
    var div = document.getElementById("tree");
    if (GHT.theTable) div.removeChild(GHT.theTable);
    GHT.theTerm = term;
    GHT.theTable =  GHT.makeTable(term, [], 1);
    div.appendChild(GHT.theTable);
};
GHT.setTerm(thms.ax1);
