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

GH.setSelectionRange = function(start, end) {
	var textarea = document.getElementById("canvas");
	// Check that this is not an ACE-editor.
	if (textarea.className == '') {
		// TODO: Get this to work for ACE-editors.
		textarea.setSelectionRange(start, end);
	}
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

    textarea.onmouseup = function(event) {
        if (self.listener) self.listener();
        return true;
		}

    textarea.onkeyup = function(event) {
        //window.onbeforeunload = function() { return "Are you sure you want to leave?";};
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

    this.getCursorPosition = function() {
        return textarea.selectionEnd;
    };
    this.getValue = function() {
        return textarea.value;
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
		// Insert text at the current cursor position.
		this.insertText = function(text) {
			var start = textarea.selectionStart;
			var value = String(textarea.value);
			var cursorPosition = this.getCursorPosition();
			textarea.value = value.substring(0, cursorPosition) + text + value.substring(cursorPosition, value.length);
			textarea.selectionEnd = start + text.length;
			textarea.selectionStart = textarea.selectionEnd;
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
    this.getSession = function() {
        return null;
    };
};

// Wrapper for ACE-based editor
GH.AceEdit = function(editor) {
    var self = this;
    var session = editor.getSession();
    this.clearImtrans = function() {};
    this.numLines = function() {
        return session.getDocument().getLength();
    };
    this.getLine = function(i) {
        return session.getDocument().getLine(i);
    };
    this.getValue = function() {
        return session.getValue();
    };
	this.getCursorPosition = function() {
		// TODO: Figure out how to covert from {column, row} to index. Document.PositionToIndex
		// might work, except there is no document.
		//session.selection.getCursor();
        return 0;
    };
    this.addListener = function(callback) {
        self.listener = callback;
    };
    this.setLines = function(text) {
        session.setValue(text.join('\n'));
    };
    session.on('change', function(e) {
        if (self.listener) self.listener();
    });
	session.selection.on('changeCursor', function(e) {
        if (self.listener) self.listener();
	});
    this.appendText = function(text) {
        editor.insert(text);
    };
    // TODO: splice (needed for autounify)
    this.getSession = function() {
        return session;
    };
    this.Range = ace.require('ace/range').Range;
}

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
    req.setRequestHeader('Content-Type', 'application/x-www-form-urlencoded; charset=UTF-8');
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

GH.setDisplayMode = function(mode) {
	document.body.className=mode;
}

function myalert(s) {
    document.getElementById('status').firstChild.nodeValue = s;
}
