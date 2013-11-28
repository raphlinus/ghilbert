GH.Table = function(tableElement) {
    // ================ Private Variables ================
    var table = tableElement;
    var collection = [];
    // map from row name to TR element.
    var rowMap = {};


    function sortByIndex(index) {
        collection.forEach(function(rowObj) {table.removeChild(rowMap[rowObj.name]);});
        collection.sort(function(a, b) {
                            return (a.cells[index] < b.cells[index])
                                ?  1 : -1;
                        });
        collection.forEach(function(rowObj) {table.appendChild(rowMap[rowObj.name]);});
    }
    var header = document.createElement('tr');
    header.className += 'headerRow';
    function addHeader(name, sortIndex) {
        var th = document.createElement('th');
        var a = document.createElement('a');
        a.innerHTML = name;
        a.href='#';
        a.onclick = function() { sortByIndex(sortIndex); return false;};
        th.appendChild(a);
        header.appendChild(th);
    };
    addHeader('Name', 0);
    addHeader('Hyps', 1);
    addHeader('Result', 2);
    table.appendChild(header);

    // ================ Public Functions ================
    /**
     * @param collection an array of table rows. Each row is an object
     * with the following members. cells: the string values for the
     * rows. name: the (unique) symName of the row.  onclick: an optional
     * onclick function for the row.
     */
    this.setContents = function(newCollection) {
        var rowObj;
        while ((rowObj = collection.pop())) {
            table.removeChild(rowMap[rowObj.name]);
            delete rowMap[rowObj.name];
        }
        newCollection.forEach(
            function(row) {
                collection.push(row);
                var tr = document.createElement('tr');
                tr.className += "clickableRow";
                rowMap[row.name] = tr;
                row.cells.forEach(
                    function(cell) {
                        var datum = document.createElement('td');
                        datum.innerHTML = cell;
                        tr.appendChild(datum);
                    });
                if (row.onclick) { tr.onclick = row.onclick; }
                table.appendChild(tr);
            });
    };
    this.filter = function(pattern) {
        collection.forEach(
            function (row) {
                rowMap[row.name].style.display =
                    (!pattern || (row.filterString.indexOf(pattern) >= 0))
                    ? "table-row" : "none";
        });
    };
};

GH.Panel = function(ctx) {
    var self = this;
    self.inferences = [];
    self.ctx = ctx;
    self.table = new GH.Table(document.getElementById('panel'));

    function addStep(symName, sym) {
        return function() {
            function insertText(text) {
                window.direct.text.insertText(text);
                window.direct.update(true);
            }
            // Push on the mandatory hyps using their default names
            insertText(sym[4].map(function(mand) { return mand[2]; }).join(' ') + ' ');
            // Push on the sym name itself
            insertText(symName);
        };
    }
    var inferenceCollection = [];
    var deductionCollection = [];
    self.inferences = inferenceCollection;
    for (var symName in ctx.syms) {
        var sym = ctx.syms[symName];
        switch (sym[0]) {
        case 'tvar':
        case 'var':
            continue;
        }
        var collection = (sym[2].length > 0) ? inferenceCollection : deductionCollection;
        collection.push(
            {
                name: symName,
                filterString: symName + " " +
                    sym[2].map(GH.sexp_to_string).join(" ") + " "
                    + GH.sexp_to_string(sym[3]),
                onclick: addStep(symName, sym),
                cells: [GH.escapeHtml(symName),
                        sym[2].map(GH.sexptohtml).join("<br/>"),
                        GH.sexptohtml(sym[3])]});
    }
		GH.Panel.highlightButton(GH.Panel.ButtonId.INFERENCES);
		self.table.setContents(inferenceCollection);
    document.getElementById(GH.Panel.ButtonId.INFERENCES).onclick = function() {
			GH.Panel.highlightButton(GH.Panel.ButtonId.INFERENCES);
      self.table.setContents(inferenceCollection);
			GH.Panel.resizePanel();
    };
    document.getElementById(GH.Panel.ButtonId.DEDUCTIONS).onclick = function() {
			GH.Panel.highlightButton(GH.Panel.ButtonId.DEDUCTIONS);
      self.table.setContents(deductionCollection);
		GH.Panel.resizePanel();
    };
    document.getElementById(GH.Panel.ButtonId.UNIFIED).onclick = function() {
				GH.Panel.highlightButton(GH.Panel.ButtonId.UNIFIED);
        var collection = [];
        self.inferences.forEach(
            function(row) {
                var symName = row.name;
                var sym = self.ctx.syms[symName];
                var proofctx = window.direct.thmctx.proofctx;
                var result;
                try {
                    var mandstack =  sym[4].map(function(mand) {
                                                    return [mand, mand[2]];
                                                });
                    result = self.ctx.match_inference(sym, proofctx, mandstack);
                    collection.push(
                        {
                            name: symName,
                            filterString: symName + " "
                                + GH.sexp_to_string(result),
                            onclick: addStep(symName, sym),
                            cells: [symName, sym[2].length,
                                    GH.sexptohtml(result)]});
                } catch (e) {
                    // cannot unify.
                    return;
                }
            });
        self.table.setContents(collection);
				GH.Panel.resizePanel();
    };

    document.getElementById('filter').onkeyup = function() {
        self.table.filter(document.getElementById('filter').value);
    };
};

// Change the styling on a button that has been selected.
GH.Panel.highlightButton = function(button) {
	var buttonId = GH.Panel.ButtonId;
	var ids = [buttonId.INFERENCES, buttonId.DEDUCTIONS, buttonId.UNIFIED];
	for (var i = 0; i < ids.length; i++) {
		document.getElementById(ids[i]).className = (button == ids[i]) ? 'highlighted-button' : '';
	}
}

// The list of buttons to press in the dictionary panel.
GH.Panel.ButtonId = {
	INFERENCES: 'inferences',
	DEDUCTIONS: 'deductions',
	UNIFIED: 'unified'
};

// Recalculates the height of the dictionary, editor, and stack panels based on the size of the
// browser window.
GH.Panel.resizePanel = function(num) {
	var container = document.getElementById('panel-container');
	var panel = document.getElementById('panel');
	var rightPanel = document.getElementById('right-panel');
	var maxHeight = window.innerHeight - 200;
	container.style.height = GH.min(maxHeight + 40, panel.scrollHeight + 10);

	var canvas = document.getElementById('canvas');
	var stack = document.getElementById('stack');
	canvas.style.height = maxHeight + 60;

	num = num || GH.Panel.getPanelNum();
	stack.style.height = (num >= 2) ? maxHeight - 68 : maxHeight + 30;
	if (num == 1) {
		var stackWidth = GH.min(window.innerWidth - 20, 1000);
		var margin = (window.innerWidth - stackWidth) / 2;
		rightPanel.style.width = stackWidth;
		rightPanel.style.margin = '0 ' + margin;
	} else {
		rightPanel.style.width = '';
		rightPanel.style.margin = '';
	}
	if (window.direct) {
		window.direct.resize();
	}
};

GH.Panel.setPanelNum = function(num) {
	if (num == 1) {
		document.body.className='stack-mode';
	} else if (num == 2) {
		document.body.className='editor-mode';
	} else {
		document.body.className='';
	}
	GH.Panel.resizePanel(num);
};

GH.Panel.getPanelNum = function(num) {
	var bodyClass = document.body.className;
	if (bodyClass == 'stack-mode') {
		return 1;
	} else if (bodyClass == 'editor-mode') {
		return 2;
	} else {
		return 3;
	}
};

window.onresize = function() {
	GH.Panel.resizePanel();
};

window.onload = function() {
	GH.Panel.resizePanel();
};
