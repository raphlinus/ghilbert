var theory = new ORCAT.Theory();
exports.theory = theory;
var wff = exports.theory.newKind("wff");
var implies = exports.theory.newOperator("&rarr;", wff, [wff, wff]);
var not = exports.theory.newOperator("not", wff, [wff]);
exports.implies = implies;
var scheme = new ORCAT.Scheme(implies, "ax-mp");
exports.scheme = scheme;
// TODO: can we get off the ground without these?
exports.scheme.setBinding(implies, 0, scheme.RIGHT(), "_imim1");
exports.scheme.setBinding(implies, 1, scheme.LEFT(), "_imim2");
exports.scheme.setBinding(not, 0, scheme.RIGHT(), "_imim2");

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
exports.theory.addAxiom("Transpose", theory.parseTerm(
                            [implies, [implies, [not, 0], [not, 1]],
                             [implies, 1, 0]]));

if (exports.startUi) {
    exports.ui.reset();
    exports.ui.addAxiom("Simplify");
    exports.ui.addAxiom("Distribute");
    exports.ui.addAxiom("Transpose");

    var proofState;
var ghText = "";
function startWith(thmName) {
        proofState = prover.newProof(thmName);
}
function applyArrow(xpath, thmName) {
    proofState = proofState.consider(xpath, thmName)[0].execute();
}
function saveAs(thmName) {
    ghText += proofState.proof(thmName) + "\n";
    theory.addAxiom(thmName, proofState.assertion());
}
startWith("Distribute");
applyArrow([0], "Simplify");
saveAs("imim2");
applyArrow([], "Distribute");
applyArrow([0], "Simplify");
saveAs("imim1");
startWith("Simplify");
applyArrow([], "imim1");
saveAs('himp1');
startWith("Distribute");
applyArrow([1,0],'Simplify');
saveAs('con12');
startWith('Simplify');
applyArrow([], 'Distribute');
saveAs('iddlem1');
applyArrow([0], 'Simplify');
saveAs('idd');
applyArrow([], 'idd');
saveAs('id');
startWith('Distribute');
applyArrow([0], 'idd');
    console.log(ghText);
}
