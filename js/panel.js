GH.Panel = function(ctx) {
    var self = this;
    self.table = document.getElementById('panel');
    self.inferences = [];
    self.ctx = ctx;

    function addStep(symName, sym) {
	return function() {
	    function appendText(text) {
		window.direct.text.appendText(text);
		window.direct.update();
	    }
	    appendText("\n");
	    // Push on the mandatory hyps using their default names
	    appendText("\n" + sym[4].map(function(mand) { return mand[2]; }).join(" "));
	    // Push on the sym name itself
	    appendText(" " + symName + "\n");
	};
    }
    var row = document.createElement('tr');
    function addChild(tag, contents) {
	var datum = document.createElement(tag);
	datum.innerHTML = contents;
	row.appendChild(datum);
	return datum;
    }
    addChild('th', 'Name');
    addChild('th', 'Hyps').className = "hyp";
    addChild('th', 'Result');
    self.table.appendChild(row);
    for (var symName in ctx.syms) {
	row = document.createElement('tr');
	row.id = 'panel.row.' + symName;
	var sym = ctx.syms[symName];
	switch (sym[0]) {
	case 'tvar':
	case 'var':
	    continue;
	}
	row.className += "sym " + sym[0];
	if (sym[2].length > 0) {
	    row.className += ' inference';
	    self.inferences.push(symName);
	} else {
	    row.className += ' deduction';
	}
	addChild('td',symName);
	//addChild('td',sym[1].map(GH.sexptounicode).join("<br/>"));
	addChild('td',sym[2].map(GH.sexptounicode).join("<br/>")).className = "hyp";
	addChild('td',GH.sexptounicode(sym[3]));
	row.onclick = addStep(symName, sym);
	self.table.appendChild(row);
    }
    function addStyleSheetRule(sIndex, selector, rule) {
	var oStyleSheet = document.styleSheets[sIndex];

	if (oStyleSheet.addRule) { // Internet Explorer
	    oStyleSheet.addRule(selector, rule, oStyleSheet.rules.length);
	} else { // w3c complient
	    oStyleSheet.insertRule(selector + '{' + rule + '}',oStyleSheet.cssRules.length);
	}
    }
    function showRows(className, show) {
	addStyleSheetRule(0,'tr.' + className, 'display:' + (show ? 'table-row' : 'none'));
    }
    function showHyps(show) {
	addStyleSheetRule(0,'.hyp', 'display:' + (show ? 'table-cell' : 'none'));
    }
    function clearUnified() {
	if (self.unified) {
	    self.unified.forEach(function(row) { self.table.removeChild(row); });
	    self.unified = false;
	}
    }
    addStyleSheetRule(0,'tr.sym', 'display:none');
    document.getElementById('inferences').onclick = function() {
	clearUnified();
	showRows('deduction', false);
	showRows('inference', true);
	showHyps(true);
    };
    document.getElementById('deductions').onclick = function() {
	clearUnified();
	showRows('deduction', true);
	showRows('inference', false);
	showHyps(false);
    };
    document.getElementById('unified').onclick = function() {
	clearUnified();
	showRows('deduction', false);
	showRows('inference', false);
	showHyps(false);
	self.unified = [];
	self.inferences.forEach(
	    function(symName) {
		var sym = self.ctx.syms[symName];
		var proofctx = window.direct.thmctx.proofctx;
		var result;
		try {
		    result = self.ctx.match_inference(sym, proofctx);
		} catch (e) {
		    return;
		}

		var row = document.createElement('tr');
		var datum = document.createElement('td');
		datum.innerHTML = symName;
		row.appendChild(datum);
		datum = document.createElement('td');
		datum.innerHTML = GH.sexptounicode(result);
		row.appendChild(datum);
		row.onclick = addStep(symName, sym);
		self.table.appendChild(row);
		self.unified.push(row);
	    });
    };
};