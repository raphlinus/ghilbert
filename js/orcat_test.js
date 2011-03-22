var sys = require('sys');

function expectEq(a, b, msg) {
    if (a !== b) throw msg;
}
function expect(t, msg) {
    if (!t) throw msg;
}

try {
    ORCAT = {};
    document = { getElementById: function(id) { return null; }
    };
    ORCAT.Theory = require('./theory.js').Theory;
    ORCAT.Scheme = require('./scheme.js').Scheme;
    ORCAT.Prover = require('./proof.js').Prover;
    ORCAT.Ui = require('./orcat_ui.js').Ui;
    ORCAT = require('./orcat_PosPropCal.js');
    var scheme = ORCAT.scheme;
    expect(scheme.LEFT().equals(scheme.RIGHT().compose(scheme.RIGHT())), "r*r=l");

    var prover = ORCAT.prover;
    var proofState = prover.newProof("Simplify");
    // PICKUP: verify this
    sys.puts("proof: " + proofState.proof('thm1'));
} catch (x) {
    sys.puts("ERROR: " + x);
    throw(x);
}
