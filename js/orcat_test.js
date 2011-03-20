var sys = require('sys');

function expectEq(a, b, msg) {
    if (a !== b) throw msg;
}
function expect(t, msg) {
    if (!t) throw msg;
}

try {
    var ORCAT = require("./theory");
    var theory = new ORCAT.Theory();
    sys.puts("theory: " + theory);
    var wff = theory.newKind("wff");
    sys.puts("wff: " + wff);
    var implies = theory.newOperator("&rarr;", wff, [wff, wff]);
    sys.puts("implies: " + implies);
    var ax1 = theory.addAxiom("Complicate", [implies, 0, [implies, 1, 0]]);
    sys.puts("ax1: " + ax1);
    var ax2 = theory.addAxiom(
	"Distribute", [implies, [implies, 0, [implies, 1, 2]],
                       [implies, [implies, 0, 1], [implies, 0, 2]]]);
    sys.puts("ax2: " + ax2);
  
    ORCAT.Scheme = require("./scheme").Scheme;
    var scheme = new ORCAT.Scheme(implies, "ax-mp");
    // TODO: can we get off the ground without these?
    scheme.setBinding(implies, 0, scheme.RIGHT(), "_imim1");
    expect(scheme.RIGHT().equals(scheme.getBinding(implies,0)), "setGetBinding0");
    scheme.setBinding(implies, 1, scheme.LEFT(), "_imim2");
        expect(scheme.LEFT().equals(scheme.RIGHT().compose(scheme.RIGHT())), "r*r=l");
    
} catch (x) {
    sys.puts("ERROR: " + x);
    throw(x);
}
