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
            a = ORCAT.theory.parseTerm(a.specifyAt(s), a.kind());
        }
    );
    u.steps(1).forEach(
        function(s) {
            b = ORCAT.theory.parseTerm(b.specifyAt(s), b.kind());
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
ORCAT = require('../orcat/orcat_PosPropCal.js');
var scheme = ORCAT.scheme;
expect(scheme.LEFT().equals(scheme.RIGHT().compose(scheme.RIGHT())), "r*r=l");

var exports = ORCAT;
var theory = exports.theory;
var ax1 = exports.theory.theorem('Simplify');
var ax2 = exports.theory.theorem('Distribute');
var I = exports.implies;
expectUnify(ax2.xpath([1]), ax1);
expectUnify(ax1, ax2.xpath([0]));
expectUnify(ax2.xpath([0]), ax1);
expectUnify(ax1.xpath([0]), ax2);
expectUnify(ax2.xpath([1]), ax1);
expectUnify(ORCAT.theory.parseTerm([I, [I, 0, 1], [I, 2, 3]]),
            ORCAT.theory.parseTerm([I, [I, 0, 1], [I, 0, 1]]));

expectUnify(ORCAT.theory.parseTerm([I, 1, [I, 2, 3]]),
            ORCAT.theory.parseTerm([I, 4, 4]));
expectUnify(ORCAT.theory.parseTerm([I, [I, 4, 5], [I, [I, 6, 4], [I, 6, 5]]]),
            ax2.xpath([0]));
expectUnify(ORCAT.theory.parseTerm([I, [I, 0, 1], 1]),
            ORCAT.theory.parseTerm([I, 1, 2]));
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

expect(u.equals(theory.parseTerm(eval(u.toSource()))));

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
ghText += '\nimport (COREPROPCAL CorePropCal.ghi (POSPROPCAL) "")\n';
var not = exports.theory.newOperator("not", exports.wff, [exports.wff]);
exports.not = not;
//var I = exports.implies;
exports.theory.addAxiom("Transpose", theory.parseTerm(
                            [I, [I, [not, 0], [not, 1]],
                             [I, 1, 0]]));

expect(!exports.theory.unify(exports.theory.parseTerm([I, [not, [not, 0]], 0]),
                             exports.theory.parseTerm([I, 0, [I, 0, 1]])));

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

scheme.setBinding(not, 0, scheme.RIGHT(), "con3");

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

// Level 3
var and = exports.theory.newOperator("and", exports.wff, [exports.wff, exports.wff]);
exports.and = and;
expectUnify(ORCAT.theory.parseTerm([I, 1353, [I, [and, 1354, 1355], 1356]]),
            ORCAT.theory.parseTerm([I, 1357, [I, 1357, 1358]]));
exports.theory.addAxiom("Conjoin", theory.parseTerm(
                            [not, [I, [I, [and, 0, 1], [not, [I, 0, [not, 1]]]],
                                   [not, [I, [not, [I, 0, [not, 1]]], [and, 0, 1]]]]]));
//scheme.setBinding(not, 0, scheme.RIGHT(), "con3");

ghText += "\ndefthm (Conjoin wff (and A B) () () \
          (not (rarr (rarr (and A B) (not (rarr A (not B)))) \
                  (not (rarr (not (rarr A (not B))) (and A B))))) \
     (not (rarr A (not B)))  (not (rarr A (not B)))  dfand)\n";
startWith('Conjoin');
applyArrow([], 'nimp1');
saveAs('and1');

startWith('Conjoin');
applyArrow([], 'nimp2');
applyArrow([], 'nn1');
saveAs('and2');

startWith('imim1');
applyArrow([1], 'con3');
applyArrow([1,0], 'and1');
applyArrow([1,1], 'and2');
saveAs('anim1');

scheme.setBinding(and, 0, scheme.LEFT(), "anim1");

startWith('imim2');
applyArrow([1], 'con3');
applyArrow([1,1], 'and2');
applyArrow([1,0], 'and1');
applyArrow([0], 'con3');
saveAs('anim2');

scheme.setBinding(and, 1, scheme.LEFT(), "anim2");


startWith('and1');
applyArrow([1], 'nimp1');
saveAs('andl');

startWith('and1');
applyArrow([1], 'nimp2');
applyArrow([1], 'nn1');
saveAs('andr');

startWith('conjnimp');
applyArrow([1,1], 'and2');
applyArrow([1,0], 'nn2');
saveAs('conj');

startWith('conj');
applyArrow([], 'contract');
saveAs('anid');

startWith('and1');
applyArrow([1,0], 'Transpose');
applyArrow([1,0,0], 'nn1');
applyArrow([1], 'and2');
saveAs('ancom');

startWith('anim2');
applyArrow([1,0], 'anid');
saveAs('ancr');

startWith('andr');
applyArrow([], 'imim1');
applyArrow([], 'imim2');
applyArrow([1], 'contract');
applyArrow([0,0], 'andl');
saveAs('import');

startWith('mp');
applyArrow([], 'import');
saveAs('anmp');

startWith('andl');
applyArrow([1], 'conj');
applyArrow([1], 'imim2');
applyArrow([], 'ancr');
applyArrow([1,0], 'andr');
applyArrow([1], 'anmp');
saveAs('anim3');

startWith('anim3');
applyArrow([1,1], 'ancom');
applyArrow([1,1], 'anim3');
applyArrow([1], 'import');
applyArrow([1,0], 'ancom');
applyArrow([1,1], 'ancom');
saveAs('prth');

startWith('id');
applyArrow([], 'conj');
applyArrow([], 'idie');
saveAs('dfbi');
// Level 4
var iff = exports.theory.newOperator("iff", exports.wff, [exports.wff, exports.wff]);
exports.iff = iff;
exports.theory.addAxiom("Equivalate", theory.parseTerm(
                            [and, [I, [iff, 1, 2], [and, [I, 1, 2], [I, 2, 1]]],
                             [I, [and, [I, 1, 2], [I, 2, 1]], [iff, 1, 2]]]));
ghText += "\ndefthm (Equivalate wff (iff A B) () () \
     (and (rarr (iff A B) (and (rarr A B) (rarr B A))) \
         (rarr (and (rarr A B) (rarr B A)) (iff A B))) \
    (and (rarr A B) (rarr B A))  (and (rarr A B) (rarr B A))  dfbi \
)\n";

startWith('Equivalate');
applyArrow([], 'andl');
saveAs('def-bi-1');

startWith('Equivalate');
applyArrow([], 'andr');
saveAs('def-bi-2');

startWith('def-bi-1');
applyArrow([1], 'andl');
saveAs('bi1');

startWith('def-bi-1');
applyArrow([1], 'andr');
saveAs('bi2');

startWith('def-bi-1');
applyArrow([1,1], 'imim1');
applyArrow([1,0], 'imim1');
applyArrow([1], 'def-bi-2');

saveAs('imbi1');

startWith('def-bi-1');
applyArrow([1,0], 'imim2');
applyArrow([1,1], 'imim2');
applyArrow([1], 'def-bi-2');
saveAs('imbi2');

startWith('def-bi-1');
applyArrow([1,0], 'imim1');
applyArrow([1,1], 'imim2');
applyArrow([1], 'prth');
applyArrow([1,0], 'def-bi-1');
applyArrow([1,1], 'def-bi-2');
applyArrow([], 'ancr');
applyArrow([1,0], 'def-bi-1');
applyArrow([1,0,0], 'imim2');
applyArrow([1,0,1], 'imim1');
applyArrow([1,0], 'prth');
applyArrow([1,0,0], 'ancom');
applyArrow([1,0,1], 'ancom');
applyArrow([1,0,0], 'def-bi-1');
applyArrow([1,0,1], 'def-bi-2');
applyArrow([1], 'def-bi-2');
saveAs('bibi1');

startWith('def-bi-1');
applyArrow([1,0], 'imim2');
applyArrow([1,1], 'imim1');
applyArrow([1], 'prth');
applyArrow([1,0], 'def-bi-1');
applyArrow([1,1], 'def-bi-2');
applyArrow([], 'ancr');
applyArrow([1,0], 'def-bi-1');
applyArrow([1,0,0], 'imim1');
applyArrow([1,0,1], 'imim2');
applyArrow([1,0], 'prth');
applyArrow([1,0,0], 'ancom');
applyArrow([1,0,1], 'ancom');
applyArrow([1,0,0], 'def-bi-1');
applyArrow([1,0,1], 'def-bi-2');
applyArrow([1], 'ancom');
applyArrow([1], 'def-bi-2');
saveAs('bibi2');

startWith('mp');
applyArrow([1,0], 'bi1');
saveAs('mpbi');

startWith('mp');
applyArrow([1,0], 'bi2');
saveAs('mpbir');

startWith('def-bi-1');
applyArrow([1,0], 'anim1');
applyArrow([1,1], 'anim1');
applyArrow([1], 'def-bi-2');
saveAs('anbi1');

startWith('def-bi-1');
applyArrow([1,0], 'anim2');
applyArrow([1,1], 'anim2');
applyArrow([1], 'def-bi-2');
saveAs('anbi2');

startWith('def-bi-1');
applyArrow([1,0], 'con3');
applyArrow([1,1], 'con3');
applyArrow([1], 'def-bi-2');
saveAs('notbi');


// Level 5

startWith('bi1');
applyArrow([], 'ancr');
applyArrow([1,0], 'bi2');
applyArrow([1], 'def-bi-2');
applyArrow([], 'conj');
applyArrow([1], 'def-bi-2');
applyArrow([0,1], 'def-bi-2');
applyArrow([0,1,1], 'bi1');
applyArrow([0,1], 'ancom');
applyArrow([0], 'ancr');
applyArrow([0,1], 'bi2');
applyArrow([], 'idie');
saveAs('bicom');

startWith('dfbi');
applyArrow([], 'def-bi-2');
saveAs('biid');

/*
startWith('nn1');
applyArrow([], 'conj');
applyArrow([1], 'def-bi-2');
applyArrow([0,1], 'nn2');
applyArrow([], 'idie');
applyArrow([], 'equivalents, 'bicom~');
saveAs('nnbi');

startWith('Transpose');
applyArrow([], 'conj');
applyArrow([1], 'ancom');
applyArrow([1], 'def-bi-2');
applyArrow([0,1], 'con3');
applyArrow([], 'idie');
saveAs('con3bi');

startWith('and1');
applyArrow([], 'conj');
applyArrow([1], 'def-bi-2');
applyArrow([0,1], 'and2');
applyArrow([], 'idie');
saveAs('dfanbi');

startWith('ancom');
applyArrow([], 'conj');
applyArrow([1], 'def-bi-2');
applyArrow([0,0], 'ancom');
applyArrow([], 'idie');
saveAs('ancombi');

startWith('anid');
applyArrow([], 'conj');
applyArrow([1], 'def-bi-2');
applyArrow([0,0], 'andr');
applyArrow([], 'idie');
saveAs('anidbi');

startWith('con12');
applyArrow([], 'conj');
applyArrow([1], 'def-bi-2');
applyArrow([0,1], 'con12');
applyArrow([], 'idie');
saveAs('con12bi');

startWith('dfanbi');
applyArrow([1,0,1,0], 'dfanbi');
applyArrow([1,0,1], 'nnbi~');
applyArrow([1,0], 'con12bi');
applyArrow([1,0,1], 'nnbi');
applyArrow([1], 'dfanbi');
applyArrow([1,1], 'dfanbi');
applyArrow([0], 'ancombi');
applyArrow([1,1], 'ancombi');
saveAs('anass');


startWith('import');
applyArrow([], 'conj');
applyArrow([1], 'def-bi-2');
applyArrow([0,0], 'imim2');
applyArrow([0,0,0], 'conj');
applyArrow([], 'idie');
saveAs('impexp');


startWith('def-bi-1');
applyArrow([], 'conj');
applyArrow([1], 'def-bi-2');
applyArrow([0,1], 'def-bi-2');
applyArrow([], 'idie');
saveAs('dfbi3');
// Level 6
startWith('biid');
applyArrow([1], 'term substitute, '->');
applyArrow([1,0], 'term substitute, '-.');
GHT.DefThm('or');
// GHT.Operators['or'] = new Operator('or','or','wff',['wff','wff'],[Infinity,Infinity]);

startWith('df-or');
applyArrow([], 'bi2');
applyArrow([0], 'Simplify');
saveAs('or2');
 // GHT.Thms['or2'] = T(O("->"),TV("wff -53792),T(O("or"),TV("wff -53793),TV("wff -53792)));

startWith('df-or');
applyArrow([], 'bi2');
applyArrow([0], 'equivalents, 'con3bi');
applyArrow([0], 'Simplify');
applyArrow([0], 'equivalents, 'nnbi~');
saveAs('or1');

startWith('imim2');
applyArrow([1,0], 'equivalents, 'con3bi~');
applyArrow([1,0], 'equivalents, 'df-or');
applyArrow([1,1], 'equivalents, 'con3bi');
applyArrow([1,1,1], 'equivalents, 'nnbi~');
applyArrow([1,1], 'equivalents, 'df-or');
applyArrow([0,0], 'equivalents, 'nnbi~');
saveAs('orim1');

startWith('imbi1');
applyArrow([1,0], 'df-or');
applyArrow([1,1], 'df-or');
applyArrow([0], 'notbi');
saveAs('orbi1');

startWith('imim2');
applyArrow([1,0], 'equivalents, 'df-or');
applyArrow([1,1], 'equivalents, 'df-or');
saveAs('orim2');

GHT.showTerminals([], null, setfirst)({pageX:0,pageY:0});GHT.theMenu.options['imbi1');
applyArrow([1,0], 'con3bi~');
applyArrow([1,1], 'con3bi~');
applyArrow([1,0], 'df-or');
applyArrow([1,1], 'df-or');
applyArrow([0], 'notbi');
saveAs('orbi2');

GHT.showTerminals([], null, setfirst)({pageX:0,pageY:0});GHT.theMenu.options['con3bi');
applyArrow([1], 'df-or');
applyArrow([0], 'df-or');
applyArrow([1,1], 'nnbi~');
saveAs('orcom');

*/

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


