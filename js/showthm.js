// License

GH.max = function(x, y) {
    return x > y ? x : y;
};

GH.typeset_intermediates = function() {
    var checkbox = document.getElementById('show-code');
	checkbox.checked = true;
	checkbox.onclick = GH.onCheckboxClicked;
    var elements = document.getElementsByClassName('sexp');
    var n = elements.length;
    for (var i = 0; i < n; i++) {
        var e = elements[i];
        var sexp_str = e.firstChild.nodeValue;
        var scanner = new GH.Scanner([sexp_str]);
        e.innerHTML = '\\(' + GH.sexptohtml(GH.read_sexp(scanner), true) + '\\)';
		MathJax.Hub.Queue(["Typeset", MathJax.Hub, e]);
    }
};

GH.onCheckboxClicked = function(element) {
    var checkbox = document.getElementById('show-code');
    var proofBody = document.getElementById('proof-body');
	if (checkbox.checked) {
		proofBody.className = '';
	} else {
		proofBody.className = 'hide-code';
	}
};