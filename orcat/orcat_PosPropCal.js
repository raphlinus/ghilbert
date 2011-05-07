var theory = new ORCAT.Theory();
exports.theory = theory;
var wff = exports.theory.newKind("wff");
exports.wff = wff;
var implies = exports.theory.newOperator("&rarr;", wff, [wff, wff]);
exports.implies = implies;
var scheme = new ORCAT.Scheme(implies, "ax-mp");
exports.scheme = scheme;
// TODO: can we get off the ground without these?
exports.scheme.setBinding(implies, 0, scheme.RIGHT(), "_imim1");
exports.scheme.setBinding(implies, 1, scheme.LEFT(), "_imim2");

var ghVars = {
    'wff':[["A", "B", "C", "D", "E", "F", "G", "H"]],
    'set':[["S", "T", "U", "V"]],
    'num':[["a", "b", "c", "d", "e", "f", "g", "h"],
           ["z", "y", "x", "w", "v",
            "z'", "y'", "x'", "w'", "v'"]]
};

var prover = new ORCAT.Prover(theory, scheme, ghVars);
exports.prover = prover;
exports.ui = new ORCAT.Ui(document, theory, prover, scheme);
exports.theory.addAxiom(
    "Simplify", theory.parseTerm(
        [implies, 0, [implies, 1, 0]]));
exports.theory.addAxiom(
    "Distribute",
    theory.parseTerm([implies, [implies, 0, [implies, 1, 2]],
                      [implies, [implies, 0, 1], [implies, 0, 2]]]));
if (exports.startUi) {
    exports.ui.reset();
    exports.ui.addAxiom("Simplify");
    exports.ui.addAxiom("Distribute");
}
