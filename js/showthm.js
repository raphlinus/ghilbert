// License

GH.max = function(x, y) {
    return x > y ? x : y;
};

GH.typeset_intermediates = function() {
    var elements = document.getElementsByClassName('intermediate');
    var n = elements.length;
    for (var i = 0; i < n; i++) {
        var e = elements[i];
        var sexp_str = e.firstChild.nodeValue;
        var scanner = new GH.Scanner([sexp_str]);
        e.innerHTML = GH.sexptohtml(GH.read_sexp(scanner));
    }
}
