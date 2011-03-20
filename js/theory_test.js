var sys = require('sys');
try {
    var OCO = require("./theory");
    var document = {};
    var theory = new OCO.Theory(document);
    sys.puts("theory: " + theory);
    var wff = theory.newKind("wff");
    sys.puts("wff: " + wff);
    var implies = theory.newOperator("&rarr;", wff, [wff, wff]);
    sys.puts("implies: " + implies);
    var ax1 = theory.addAxiom("Complicate", [implies, 0, [implies, 1, 0]]);
    sys.puts("ax1: " + ax1);
    var ax2 = theory.addAxiom("Distribute", [implies, [implies, 0, [implies, 1, 2]],
                                             [implies, [implies, 0, 1], [implies, 0, 2]]]);
    sys.puts("ax2: " + ax2);
    
} catch (x) {
    sys.puts("ERROR: " + x);
    throw(x);
}
