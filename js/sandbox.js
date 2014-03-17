// various stuff for testing Ghilbert verifier

log = function(str) {
    if (window.console) {
	window.console.log(str);  // Safari - FF needs something different
    } else {
	function show(node) {
	    document.getElementById("output").appendChild(node);
	}
	function print(str, cls) {
	    var node = document.createElement('p');
	    if (cls) {
		node.setAttribute('class', cls);
	    }
	    node.appendChild(document.createTextNode(str));
	    show(node);
	}
	print(str);
    }
};

// Gets called only for interface files.
function interfaceRun(urlctx, url, ctx) {
    var s = new GH.Scanner(urlctx.resolve(url).split(/\r?\n/));
    var cmd = GH.read_sexp(s);
	var justification = [];
	while (cmd) {
		cmd = GH.read_sexp(s);
		if (cmd && (cmd.length == 4) && (cmd[0] == GH.getThmName())) {
			justification = s.styleScanner.get_justification();
			if ((justification.length == 2) && (justification[0] == 'redirect')) {
				window.location.replace('../' + justification[1] + '/' + GH.getThmName());
			}
		}
	}
	return {context: s.styleScanner.get_context(), justification: justification};
};

function run(urlctx, url, ctx) {
    var s = new GH.Scanner(urlctx.resolve(url).split(/\r?\n/));
    //try {
	while (true) {
	    var cmd = GH.read_sexp(s);
	    if (cmd == null) {
			return {context: s.styleScanner.get_context(), justification: s.styleScanner.get_justification()};
	    }
	    if (GH.typeOf(cmd) != 'string') {
			throw 'Cmd must be atom';
	    }
		// The styling is currently not a part of the core Ghilbert language,
		// but is included using structured comments. The special case logic
		// for styling will go away if it gets included in the language.
		var filename = (url[0] == '/') ? url : urlctx.base + '/' + url;
		var styling = s.styleScanner.get_styling(filename);
	    var arg = GH.read_sexp(s);
	    //log(cmd + ' ' + GH.sexp_to_string(arg));
	    ctx.do_cmd(cmd, arg, styling);
		s.styleScanner.clear();
	}
	//} catch (e) {
	//log(url + ':' + s.lineno + ': ' + e);
	//}
	return {context: null, justification: []};
}
