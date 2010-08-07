GH.Table = function(tableElement) {
    // ================ Private Variables ================
    var table = tableElement;
    var collection = [];
    // map from row ID (== the first cell of the row) to TR element.
    var rowMap = {};


    function sortByIndex(index) {
        collection.forEach(function(rowArr) {table.removeChild(rowMap[rowArr[0]]);});
        collection.sort(function(a, b) {
                            if (a[index] < b[index]) {
                                return -1;
                            } else if (a[index] > b[index]) {
                                return 1;
                            } else {
                                return 0;
                            }
                        });
        collection.forEach(function(rowArr) {table.appendChild(rowMap[rowArr[0]]);});
    }
    var header = document.createElement('tr');
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
     * @param collection an array of table rows. Each row is an array
     * containing the string values for the rows, plus one last value
     * to be the onclick function for the row.  The first datum in each
     * row is treated as rowId so it should be unique.
     */
    this.setContents = function(newCollection) {
        var rowArr;
        while ((rowArr = collection.pop())) {
            table.removeChild(rowMap[rowArr[0]]);
            delete rowMap[rowArr[0]];
        }
        newCollection.forEach(function(row) {
                                  collection.push(row);
                                  var tr = document.createElement('tr');
                                  rowMap[row[0]] = tr;
                                  row.forEach(function(cell) {
                                                  if (typeof(cell) === 'function') {
                                                      tr.onclick = cell;
                                                  } else {
                                                      var datum = document.createElement('td');
                                                      datum.innerHTML = cell;
                                                      tr.appendChild(datum);
                                                  }
                                              });
                                  table.appendChild(tr);
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
            function appendText(text) {
                window.direct.text.appendText(text);
                window.direct.update();
            }
            // Push on the mandatory hyps using their default names
            appendText(" " + sym[4].map(function(mand) { return mand[2]; }).join(" "));
            // Push on the sym name itself
            appendText(" " + symName + "\n");
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
        collection.push([symName,
                         sym[2].map(GH.sexptounicode).join("<br/>"),
                         GH.sexptounicode(sym[3]),
                         addStep(symName, sym)]);
    }
    document.getElementById('inferences').onclick = function() {
        self.table.setContents(inferenceCollection);
    };
    document.getElementById('deductions').onclick = function() {
        self.table.setContents(deductionCollection);
    };
    document.getElementById('unified').onclick = function() {
        var collection = [];
        self.inferences.forEach(
            function(row) {
                var symName = row[0];
                var sym = self.ctx.syms[symName];
                var proofctx = window.direct.thmctx.proofctx;
                var result;
                try {
                    var mandstack =  sym[4].map(function(mand) {
                                                    return [mand, mand[2]];
                                                });
                    result = self.ctx.match_inference(sym, proofctx, mandstack);
                    collection.push([symName, sym[2].length, GH.sexptounicode(result), addStep(symName, sym)]);
                } catch (e) {
                    // cannot unify.
                    return;
                }
            });
        self.table.setContents(collection);
    };
};
