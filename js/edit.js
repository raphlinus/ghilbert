// <license>

GH.min = function(x, y) {
    return x < y ? x : y;
};

GH.max = function(x, y) {
    return x > y ? x : y;
};

GH.abs = function(x) {
    return x >= 0 ? x : -x;
};

GH.cursormin = function(c1, c2) {
    if (c1[0] === c2[0]) {
        return c1[1] < c2[1] ? c1 : c2;
    }
    return c1[0] < c2[0] ? c1 : c2;
};

GH.cursormax = function(c1, c2) {
    if (c1[0] === c2[0]) {
        return c1[1] > c2[1] ? c1 : c2;
    }
    return c1[0] > c2[0] ? c1 : c2;
};

GH.TextareaEdit = function(textarea) {
    var self = this;
    textarea.focus();

    // Stack of [before,func] pairs for ctrl-z.  If empty, use regular undo.
    this.undoStack = [];
    self.restore_excursion = function() {};
    textarea.onkeydown = function(event) {
        self.restore_excursion();
        if (event.keyCode === 13 && (event.ctrlKey || event.shiftKey)) {
            // Ctrl- or Shift-Enter: accept autounify
            var auLink = document.getElementById("autounify");
            if (auLink.style.display !='none') {
                auLink.onclick();
                return false;
            }
        } else if (event.keyCode == 90 && event.ctrlKey) {
            // Ctrl-z: undo
            if (self.undoStack.length &&
                (textarea.value ==
                 self.undoStack[self.undoStack.length - 1][0])) {
                self.undoStack.pop()[1]();
                return false;
            }
        }
        return true;
    };
    textarea.onkeyup = function(event) {
        window.onbeforeunload = function() { return "Are you sure you want to leave?";};
        var cursor = textarea.selectionEnd;
        var i = cursor - 1;
        if (event.keyCode === 48 && (textarea.value[i] == ')')) {
            // Electric parens
            var parenCount = 0;
            while (true) {
                if (textarea.value[i] == ')') {
                    parenCount++;
                } else if (textarea.value[i] == '(') {
                    parenCount--;
                }
                if (parenCount == 0) {
                    break;
                }
                i--;
                if (i < 0) {
                    return true;
                }
            }
            textarea.setSelectionRange(i, i + 1);
            self.restore_excursion = function() {
                textarea.setSelectionRange(cursor, cursor);
                self.restore_excursion = function() {};
            };
            window.setTimeout(
                function() {
                    self.restore_excursion();
                }, 500);
            return true;
        } 
        if (self.listener) self.listener();
        return true;
    };
    this.clearImtrans = function() {
        
    };
    this.numLines = function() {
        return textarea.value.split('\n').length;
    };
    this.getLine = function(i) {
        return textarea.value.split('\n')[i];
    };
    this.addListener = function(callback) {
        this.listener = callback;        
    };
    this.setLines = function(text) {
        textarea.value = text.map(
            function(line) { return line.replace(/^#!/,''); })
            .join('\n');
        if (self.listener) self.listener();
    };
    this.appendText = function(text) {
    textarea.value += text;
    };
    this.splice = function(start, len, newText) {
        var oldChars;
        var selectionEnd = textarea.selectionEnd;
        var newSelectionEnd = selectionEnd;
        if (start < selectionEnd) {
            newSelectionEnd += newText.length - len;
        }
        {
        var chars = textarea.value.split('');
        oldChars = chars.splice(start, len, newText);
        textarea.value = chars.join('');
        }
        var undoFunc = function() {
            var chars = textarea.value.split('');
        chars.splice(start, newText.length, oldChars.join(''));
        textarea.value = chars.join('');
            textarea.setSelectionRange(selectionEnd, selectionEnd);
        };
        textarea.setSelectionRange(newSelectionEnd, newSelectionEnd);
        this.undoStack.push([textarea.value, undoFunc]);
    };
};


// As it's written now, this class combines both model and view of the text.
// It's probably a good idea to separate these out a bit.
GH.CanvasEdit = function(canvas, inputlayer) {
    var self = this;
    this.canvas = canvas;
    this.inputlayer = inputlayer;
    if (inputlayer) {
    inputlayer.set_handler(function(evt, data) {
        return self.handler(evt, data);
        });
    }
    this.text = [''];
    this.fontsize = 16;
    this.font = this.fontsize + "px Times";
    this.setcursor([0, 0]); // line, offset
    this.linespace = this.fontsize + 2;
    this.cursorvisible = true;

    this.undostack = [];

    this.clearImtrans = function() {
        this.imtrans = {};
    };
    this.numLines = function() {
        return this.text.length;
    };
    this.getLine = function(i) {
        return this.text[i];
    };
    this.addListener = function(callback) {
        this.listeners.push(callback);
    };
    this.setLines = function(text) {
        this.text = text.map(
            function(line) { return line.replace(/^#!/,''); });
    this.dirty();
    };
    this.appendText = function(text) {
    this.text += text;
    this.dirty();
    };
    this.splice = function(start, len, newText) {
    var chars = this.text.split('');
    chars.splice(start, len, newText);
    this.text = chars.join('');
    this.dirty();
    };

    // todo: use slightly different logic for identifier->symbols, these
    // fire too easily as substrings
    this.imtrans = {
      'et':    '\u03b7',
      'th':    '\u03b8',
      'ta':    '\u03c4',
      'ph':    '\u03c6',
      'ch':    '\u03c7',
      'ps':    '\u03c8',

      '-.':    '\u00ac',
      '->':    '\u2192',
      '<->':   '\u2194',
      'A.':    '\u2200',
      'E.':    '\u2203',
      '{/}':   '\u2205',
      'e.':    '\u2208',
      'x.':    '\u2219',
      '/\\':   '\u2227',
      '\\/':   '\u2228',
      'i^i':   '\u2229',
      'u.':    '\u222a',
      'C.':    '\u2282',
      'C_':    '\u2286'
    };

    this.imtranslongest = 3;

    this.imbuf = null;
    this.listeners = [function() { self.draw(); }];
};

GH.CanvasEdit.prototype.dirty = function() {
    for (var i = 0; i < this.listeners.length; i++) {
    this.listeners[i]();
    }
};

GH.CanvasEdit.prototype.addundo = function(title) {
    // Full copy is expensive asymptotically, but should be okay for small
    // buffers.
    this.undostack.push([this.text.slice(), this.cursor]);
};

GH.CanvasEdit.prototype.undo = function() {
    if (this.undostack.length) {
    var newstate = this.undostack.pop();
    this.text = newstate[0];
    this.cursor = newstate[1];
    this.dirty();
    }
};

GH.CanvasEdit.prototype.canvasctx = function() {
    var ctx = this.canvas.getContext("2d");
    ctx.font = this.font;
    return ctx;
};

GH.CanvasEdit.prototype.draw = function() {
    var ctx = this.canvasctx();
    var x = 4;
    var y = this.linespace;
    var x0, x1;
    // So this is a funny story: on FF, subpixel text rendering happens
    // if you fillRect white, but not if you clearRect. Bizarre.
    ctx.fillStyle = "white";
    ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
    ctx.fillStyle = "black";
    for (var i = 0; i < this.text.length; i++) {
    var line = this.text[i];
    var cursor = this.cursor;
    if (this.selectionpt !== null) {
        var cmin = GH.cursormin(this.selectionpt, cursor);
        var cmax = GH.cursormax(this.selectionpt, cursor);
        if (i >= cmin[0] && i <= cmax[0]) {
        if (i === cmin[0]) {
            x0 = x + ctx.measureText(line.substr(0, cmin[1])).width;
        } else {
            x0 = x;
        }
        if (i === cmax[0]) {
            x1 = x + ctx.measureText(line.substr(0, cmax[1])).width;
        } else {
            x1 = this.canvas.width;
        }
        ctx.fillStyle = '#b4d5fe';
        ctx.fillRect(x0, y - this.linespace + 3, x1 - x0, this.linespace);
        ctx.fillStyle = 'black';
        }
    }
    ctx.fillText(line, x, y);
    if (this.cursorvisible && i === cursor[0] && this.selectionempty()) {
        var string_width = ctx.measureText(line.substr(0, cursor[1])).width;
        ctx.strokeStyle = "black";
        ctx.beginPath();
        ctx.moveTo(x + string_width + 0.5, y - this.fontsize + 3);
        ctx.lineTo(x + string_width + 0.5, y + 3);
        ctx.stroke();
    }
    y = y + this.linespace;
    }
};

GH.CanvasEdit.prototype.handler = function(evt, data) {
    window.onbeforeunload = function() { return "Are you sure you want to leave?";};
    if (evt === 'textinput') {
    return this.handle_textinput(data);
    } else if (evt === 'keydown') {
    return this.handle_keydown(data);
    } else if (evt === 'cut') {
    this.imbuf = null;  // should be for copy too?
    this.addundo('Cut');
    this.deleteselection();
    this.dirty();
    return true;
    } else if (evt === 'paste') {
    this.imbuf = null;
    this.addundo('Paste');
    this.inserttext(data);
    return true;
    } else if (evt === 'undo') {
    this.imbuf = null;
    this.undo();
    return true;
    } else if (evt === 'focus') {
    this.cursorvisible = data;
    this.dirty();
    return true;
    }
    return false;
};

GH.CanvasEdit.prototype.selectionempty = function() {
    return (this.selectionpt === null || 
        (this.selectionpt[0] === this.cursor[0] &&
         this.selectionpt[1] === this.cursor[1]));
};

GH.CanvasEdit.prototype.selectiontext = function() {
    if (this.selectionpt === null) {
    return null;
    }
    var cmin = GH.cursormin(this.selectionpt, this.cursor);
    var cmax = GH.cursormax(this.selectionpt, this.cursor);
    if (cmin[0] === cmax[0]) {
    return this.text[cmin[0]].substring(cmin[1], cmax[1]);
    }
    var result = [this.text[cmin[0]].substring(cmin[1])];
    for (var i = cmin[0] + 1; i < cmax[0]; i++) {
    result.push(this.text[i]);
    }
    result.push(this.text[cmax[0]].substring(0, cmax[1]));
    return result.join('\n');
};

GH.CanvasEdit.prototype.setcursor = function(cursor) {
    this.selectionpt = null;
    this.cursor = cursor;
    var ctx = this.canvasctx();
    var line = this.text[cursor[0]];
    this.cursorx = ctx.measureText(line.substr(0, cursor[1])).width;
    // todo: dirty?
};

GH.CanvasEdit.prototype.xtopos = function(x, lineno) {
    var text = this.text[lineno];
    var ctx = this.canvasctx();
    var r = text.length + 1;
    var l = 0;
    while (r > l + 1) {
    var m = (r + l) >> 1;
    if (ctx.measureText(text.substr(0, m)).width > x) {
        r = m;
    } else {
        l = m;
    }
    }
    // todo: maybe pos to the right is closer
    return (r + l) >> 1;
};

GH.CanvasEdit.prototype.deleteselection = function() {
    if (this.selectionpt === null) {
    return;
    }
    var cmin = GH.cursormin(this.selectionpt, this.cursor);
    var cmax = GH.cursormax(this.selectionpt, this.cursor);
    this.text.splice(cmin[0], cmax[0] - cmin[0] + 1, 
             this.text[cmin[0]].substr(0, cmin[1]) +
             this.text[cmax[0]].substr(cmax[1]));
    this.setcursor(cmin);
};

GH.save = function(content, url) {
    // TODO(abliss): properly handle button presses while xhr in flight
    var saving = document.getElementById("saving");
    var req = new XMLHttpRequest();
    var number = document.getElementById('number').value;
    var text = ('name=' + encodeURIComponent(name) +
                '&number=' + encodeURIComponent(number) +
                '&content=' + encodeURIComponent(content) +
                '&url=' + encodeURIComponent(url));
    req.onreadystatechange = function () {
        if (req.readyState == 4) {
            var result = JSON.parse(req.responseText)
            this.result = result[1];
            if (result[0] === "ok") {
                window.onbeforeunload = function() { };
            }
        }
    };
    req.open('POST', '/save', true);
    req.setRequestHeader('Content-Type', 'application/x-www-form-urlencoded');
    req.send(text);
    var dots = 0;
    function spin() {
        if (req.result) {
            saving.innerHTML = req.result;
        } else {
            saving.innerHTML = "Saving";
            for (var i = 0; i < dots; i++) {
                saving.innerHTML += ".";
            }
            dots = (dots + 1) % 4;
            window.setTimeout(spin, 100);
        }
    }
    spin();
};

GH.saveDraft = function(content) {
    GH.save(
        content.split("\n")
            .map(function(line) { return "#!" + line; })
            .join("\n"));
};

GH.CanvasEdit.prototype.handle_keydown = function(evt) {
    var lineno = this.cursor[0];
    var pos = this.cursor[1];
    var text = this.text[lineno];
    var updown = false;
    var newcursor = null;
    if (evt.keyCode === 8) {
    this.addundo('Backspace');
    this.imbuf = null;
    if (this.selectionpt === null) {
        if (pos) {
        this.selectionpt = [lineno, pos - 1];
        } else if (lineno) {
        this.selectionpt = [lineno - 1, this.text[lineno - 1].length];
        }
    }
    this.deleteselection();
    } else if (evt.keyCode === 13) {
    this.deleteselection();
    this.imbuf = null;
    this.inserttext('\n');
    } else if (evt.keyCode === 37) {
    if (pos) {
        newcursor = [lineno, pos - 1];
    } else if (lineno) {
        newcursor = [lineno - 1, this.text[lineno - 1].length];
    }
    } else if (evt.keyCode === 39) {
    if (pos < text.length) {
        newcursor = [lineno, pos + 1];
    } else if (lineno < this.text.length - 1) {
        newcursor = [lineno + 1, 0];
    }
    } else if (evt.keyCode === 38 || evt.keyCode === 40) {
    updown = true;
    if (evt.keyCode === 38 && lineno === 0) {
        newcursor = [0, 0];
    } else if (evt.keyCode === 40 && lineno === this.text.length - 1) {
        newcursor = [lineno, text.length];
    } else {
        lineno += evt.keyCode === 38 ? -1 : 1;
        newcursor = [lineno, this.xtopos(this.cursorx, lineno)];
    }
    } else if (evt.keyCode === 65 && evt.ctrlKey) {
    newcursor = [lineno, 0];
    } else if (evt.keyCode === 69 && evt.ctrlKey) {
    newcursor = [lineno, text.length];
    } else if (evt.keyCode === 83 && evt.ctrlKey) {
    GH.save(this.text.join('\n'));
    return true;
    } else {
    return false;
    }
    if (newcursor !== null) {
    this.imbuf = null;
    if (evt.shiftKey) {
        if (this.selectionpt === null) {
        this.selectionpt = this.cursor;
        }
        this.cursor = newcursor;
        this.inputlayer.set_selection(this.selectiontext());
    } else {
        if (updown) {
        this.selectionpt = null;
        this.cursor = newcursor;
        } else {
        this.setcursor(newcursor);
        }
    }
    }
    this.dirty();
    return true;
};

GH.CanvasEdit.prototype.inserttext = function(data) {
    this.deleteselection();
    var lineno = this.cursor[0];
    var pos = this.cursor[1];
    var text = this.text[lineno];
    var spl = data.split('\n');
    if (spl.length === 1) {
    this.text[lineno] = text.substr(0, pos) + data + text.substr(pos);
    this.setcursor([lineno, pos + data.length]);
    } else {
    this.text = this.text.slice(0, lineno).concat(
              text.substr(0, pos) + spl[0],
              spl.slice(1, spl.length - 1),
              spl[spl.length - 1] + text.substr(pos),
              this.text.slice(lineno + 1));
    this.setcursor([lineno + spl.length - 1, spl[spl.length - 1].length]);
    }
    this.dirty();
};

GH.CanvasEdit.prototype.handle_textinput = function(data) {
    this.addundo('Insert text');
    if (this.imbuf === null) {
    this.imbuf = '';
    }
    this.imbuf += data;
    // Note, this functionality doesn't work at all at present since direct.js
    // sets this.imtrans to {}.
    for (var i = GH.min(this.imbuf.length, this.imtranslongest); i >= 1; i--) {
    var seq = this.imbuf.substr(-i);
    if (this.imtrans.hasOwnProperty(seq)) {
        var lineno = this.cursor[0];
        var pos = this.cursor[1];
        var line = this.text[lineno];
        // Note: there are some logic errors if one substitution
        // is a prefix of another (eg <-, <->).
        var newpos = pos - i + 1;
        this.text[lineno] = line.substr(0, newpos) + line.substr(pos);
        this.cursor = [lineno, newpos];
        this.inserttext(this.imtrans[seq]);
        return true;
    }
    }
    this.inserttext(data);
    return true;
};

// This gets an editor instantiated quickly, for testing.
GH.CanvasEdit.init = function() {
    var canvas = document.getElementById('canvas');
    var inputlayer = new GH.InputLayer();
    inputlayer.attach(canvas);
    var text = new GH.CanvasEdit(canvas, inputlayer);
    canvas.focus();
    text.dirty();
    var number = document.getElementById('number');
    number.onchange = function() {
        var url = '../peano/peano_thms.gh';
        var uc = new GH.XhrUrlCtx('../', url);
        var v = new GH.VerifyCtx(uc, run);
        run(uc, '../proofs_upto/' + number.value, v);
        window.direct.vg = v;
        text.dirty();
    };

    return text;
};

function myalert(s) {
    document.getElementById('status').firstChild.nodeValue = s;
}

GH.setSize = function(size) {
  document.getElementById("canvas").cols = 60 + size * 20;
  document.getElementById("canvas").rows = 8 + size * 8;
  document.getElementById("stack").width = 600 + size * 400;
  document.getElementById("stack").height = 240 + size * 60;
};