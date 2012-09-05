GH.escapeHtml = function(s) {
    return s
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;');
}
GH.gotostep = function(num) {
    var elements = document.getElementsByClassName('step');
    for (var i = 0; i < elements.length; i++) {
        var e = elements[i];
        if (i == num) {
            e.className = 'step highlighted';
        } else {
            e.className = 'step';
        }
    }

    // produce the stack
    var stack = []
    for (var i = 0; i < num + 1; i++) {
        var numpop = trace[i][0]
        stack.splice(stack.length - numpop, numpop, trace[i][1]);
    }
    var html = [];
    for (var i = 0; i < stack.length; i++) {
        var scanner = new GH.Scanner([stack[i]]);
        var typeset = GH.sexptounicode(GH.read_sexp(scanner));
        html.push('<div>' + GH.escapeHtml(typeset) + '</div>\n');
    }
    document.getElementById('stack').innerHTML = html.join('');
        
};
currentstep = 0;
window.onload = function() {
    GH.gotostep(currentstep);
    document.onkeydown = function(evt) {
        if (evt.keyCode == 37 && currentstep > 0) {
            currentstep -= 1;
            GH.gotostep(currentstep);
        } else if (evt.keyCode == 39 && currentstep < trace.length - 1) {
            currentstep += 1;
            GH.gotostep(currentstep);
        }
    }
}

