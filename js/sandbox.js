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

function run(urlctx, url, ctx) {
    var s = new GH.Scanner(urlctx.resolve(url).split(/\r?\n/));
    //try {
	while (true) {
	    var cmd = GH.read_sexp(s);
	    if (cmd == null) {
			return true;
	    }
	    if (GH.typeOf(cmd) != 'string') {
			throw 'Cmd must be atom';
	    }
		// The styling is currently not a part of the core Ghilbert language,
		// but is included using structured comments. The special case logic
		// for styling will go away if it gets included in the language.
		var styling = s.styleScanner.get_styling(urlctx.base + '/' + url);
	    var arg = GH.read_sexp(s);
	    //log(cmd + ' ' + GH.sexp_to_string(arg));
	    ctx.do_cmd(cmd, arg, styling);
		s.styleScanner.clear();
	}
	//} catch (e) {
	//log(url + ':' + s.lineno + ': ' + e);
	//}
    return false;
}
