ORCAT = {};

var util = require('util');
var spawn = require('child_process').spawn;
var fs = require('fs');

function expectEq(a, b, msg) {
    if (a !== b) throw new Error(msg);
}
function expectUnify(a, b, msg) {
    var u = ORCAT.theory.unify(a, b);
    msg = msg + " unify: " + a.toString() + " with "  + b.toString();
    if (!u) throw new Error("no unifcation " + msg);
    u.steps(0).forEach(
        function(s) {
            a = ORCAT.theory.parseTerm(a.specify(s), a.kind());
        }
    );
    u.steps(1).forEach(
        function(s) {
            b = ORCAT.theory.parseTerm(b.specify(s), b.kind());
        }
    );
    msg += " specify to " + a.toString() + " and " + b.toString();
    expect(a.equals(b), msg);
}

function expect(t, msg) {
    if (!t) throw new Error(msg);
}

document = {
    getElementById: function(id) { return null; }
};
ORCAT.Theory = require('./theory.js').Theory;
ORCAT.Scheme = require('./scheme.js').Scheme;
ORCAT.Prover = require('./proof.js').Prover;
ORCAT.Ui = require('./orcat_ui.js').Ui;
ORCAT = require('./orcat_PosPropCal.js');
var scheme = ORCAT.scheme;
expect(scheme.LEFT().equals(scheme.RIGHT().compose(scheme.RIGHT())), "r*r=l");

var exports = ORCAT;
var theory = exports.theory;
var ax1 = exports.theory.theorem('Simplify');
var ax2 = exports.theory.theorem('Distribute');
var I = exports.implies;
expectUnify(ax1, ax2.xpath([0]));
expectUnify(ax2.xpath([0]), ax1);
expectUnify(ax1.xpath([0]), ax2);
expectUnify(ax2.xpath([1]), ax1);
expectUnify(ORCAT.theory.parseTerm([I, 1, [I, 2, 3]]),
            ORCAT.theory.parseTerm([I, 4, 4]));
expectUnify(ORCAT.theory.parseTerm([I, [I, 4, 5], [I, [I, 6, 4], [I, 6, 5]]]),
            ax2.xpath([0]));
expect(!exports.theory.unify(ax1, exports.theory.parseTerm(
                                 [I, 0, 0])));
var t = exports.theory.parseTerm(ax1.specifyAt({"":[I, 0, 1]},[0]));
var u = exports.theory.parseTerm([I, [I, 0, 1], [I, 2, [I, 0, 1]]]);
expect(t.equals(u), "specify: wanted "  + u.toString() + " got " + t.toString());
t = exports.theory.parseTerm([I, 0, [I, 1, 2]]);
u = exports.theory.parseTerm([I, [I, 1, 2], [I, 1, 2]]);
expect(!t.equals(u), "A(BC) should not equal (BC)(BC)!");
t = exports.theory.parseTerm([I, [I, 0, 1], [I, 2, 3]]);
u = exports.theory.parseTerm([I, [I, 0, 1], [I, 0, 1]]);
expect(!t.equals(u), "(AB)(CD) should not equal (AB)(AB)!");

// Verify prover
var prover = ORCAT.prover;
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
/*
applyArrow([1,0], 'Simplify');
saveAs('mpd');
applyArrow([], 'mpd');
saveAs('mp');
startWith('id');
applyArrow([], 'mp');
saveAs('idie');
startWith('mp');
applyArrow([], 'Distribute');
saveAs('contract');
// Level 2
startWith('Simplify');
applyArrow([1], 'Transpose');
saveAs('fie');
startWith('fie');
applyArrow([1], 'Transpose');
applyArrow([1], 'idie');
saveAs('nn1');
startWith('fie');
applyArrow([1], 'Transpose');
applyArrow([1], 'idie');
applyArrow([], 'Transpose');
saveAs('nn2');
startWith('Transpose');
applyArrow([0,1], 'nn2');
applyArrow([0,0], 'nn1');
saveAs('con3');
startWith('Simplify');
applyArrow([], 'con3');
saveAs('nimp2');
startWith('fie');
applyArrow([], 'con3');
applyArrow([1], 'nn1');
saveAs('nimp1');
startWith('mp');
applyArrow([1], 'con3');
saveAs('conjnimp');
startWith('fie');
applyArrow([], 'Distribute');
applyArrow([1], 'Transpose');
applyArrow([1], 'idie');
saveAs('contradict');
startWith('id');
applyArrow([], 'conjnimp');
applyArrow([0], 'nn2');
applyArrow([], 'idie');
saveAs('dfand');
/**/
util.puts("verifying proof: " + ghText);
var verify = spawn('python', ['../verify.py','--','-'],
                   {cwd:__dirname + '/../orcat/'});
verify.stdout.on('data', util.puts);
verify.stderr.on('data',util.puts);
verify.on('exit',  function(code) { expectEq(0,code,"thm1 verify");});
fs.readFile('../orcat/PosPropCal_bootstrap.gh',
            function (err, data) {
                if (err) throw err;
                verify.stdin.write(data);
                verify.stdin.write(ghText);
                verify.stdin.end();
            });

