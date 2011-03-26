var util = require('util');
var spawn = require('child_process').spawn;
var fs = require('fs');

function expectEq(a, b, msg) {
    if (a !== b) throw msg;
}
function expect(t, msg) {
    if (!t) throw msg;
}

try {
    ORCAT = {};
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

    var prover = ORCAT.prover;
    var proofState = prover.newProof("Simplify");
    var ghProof = proofState.proof('thm1');
    util.puts("verifying proof: " + ghProof);
    var verify = spawn('python', ['../verify.py','--','-'],
		       {cwd:__dirname + '/../orcat/'});
    verify.stdout.on('data', util.puts);
    verify.stderr.on('data',util.puts);
    verify.on('exit',  function(code) { expectEq(0,code,"thm1 verify");});
    fs.readFile('../orcat/PosPropCal_bootstrap.gh',
		function (err, data) {
		    if (err) throw err;
		    verify.stdin.write(data);
		    verify.stdin.write(ghProof);
		    verify.stdin.end();
		});
    //TODO
//    var consideration = ghProof.consider([], 'Distribute', ORCAT.Theory.getTheorem('Distribute'));
} catch (x) {
    util.puts("ERROR: " + x);
    throw(x);
}
