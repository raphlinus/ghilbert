// Run with "(rhino|node) js/verify_test.js testsuite"

// rhino->node shim
if (typeof(load) === "undefined" && typeof(require)==="function") {
  GH = global.GH = {};
  load = function(arr) {
    arr.forEach(
      function(path) {
        require(path.replace('js','.'));
      }
    );
  };
  print = console.log;
  arguments = process.argv.slice(2);
  readFile = function(path) {
    return require('fs').readFileSync(path).toString();
  }
}

load(["js/verify.js"]);
load(["js/proofstep.js"]);

load(["js/prover/numUtil.js"]);
load(["js/showthm.js"]);

// HTML for s-expressions is used in error messages. For now just print the HTML;
// in the future perhaps the testsuites should run in a browser or we should
// do plain text s-expression output.
load(["js/typeset.js"]);

// I guess we might as well namespace things
if (typeof GhilbertTest == 'undefined') {
  var GhilbertTest = {};
}

// In-memory file repository
GhilbertTest.TestUrlContext = function () {
  this.files = {};
  this._stash = {};
};

GhilbertTest.TestUrlContext.prototype.resolve = function (url) {
  var content = this.files[url];
  if (content === undefined) {
    throw "No such url " + url;
  }
  return content;
};

GhilbertTest.TestUrlContext.prototype.open_append = function (url) {
  this.current_url = url;
  if (this.files[url] === undefined) {
    this.files[url] = '';
  }
}

GhilbertTest.TestUrlContext.prototype.append_current = function (text, lineno) {
  if (this.current_url === undefined) {
    print(lineno + ": unable to parse tests: found text without !append");
    throw("aborting");
  }
  this.files[this.current_url] += text;
}

GhilbertTest.TestUrlContext.prototype.revert = function () {
  this.files = JSON.parse(JSON.stringify(this._stash));
  this.current_url = undefined
}

GhilbertTest.TestUrlContext.prototype.stash = function () {
  this._stash = JSON.parse(JSON.stringify(this.files));
}

// A few miscellaneous functions, similar in function to the ones from js/sandbox.js
log = function(string) {
  print(string)
}

GhilbertTest.run_verifier = function (url_context, url, context) {
  var scanner = new GH.Scanner(url_context.resolve(url).split(/\r?\n/));
  while (true) {
    var command = GH.read_sexp(scanner);
    if (command === null || command === undefined) {
      return true;
    }
    if (GH.typeOf(command) != 'string') {
      throw 'Command must be atom';
    }
    // We don't care about styling, but apparently we need to participate in passing
    // it around.
    var styling = scanner.styleScanner.get_styling('');
    var arg = GH.read_sexp(scanner);
    context.do_cmd(command, arg, styling);
    scanner.styleScanner.clear();
  }
  return false;
}

GhilbertTest.run = function(test_source) {
  var lines = test_source.split(/\n/);

  var url_context = new GhilbertTest.TestUrlContext();
  var tests = 0;
  var failures = 0;
  var line_count = lines.length;
  for (var i = 0; i < line_count; i++) {
    line = lines[i];
    var lineno = i + 1;

    if (line[0] == '!') {
      var tokens = line.split(/ /);
      var command = tokens[0];
      if (command == '!append') {
        var file = tokens[1];
        url_context.open_append(file);
      }
      else if (command == '!shared') {
        url_context = new GhilbertTest.TestUrlContext();
      }
      else if (command == '!end') {
        url_context.stash();
      }
      else if (command == '!unshare') {
        url_context = new GhilbertTest.TestUrlContext();
      }
      else if (command == '!accept' || command == '!reject') {
        tests += 1;
        if (tokens.length < 2) {
          failures += 1
          print('' + lineno + ": FAIL, Missing proof module name for !accept or !reject command");
        }
        else {
          file = tokens[1]
          var verify_context = new GH.VerifyCtx(url_context, GhilbertTest.run_verifier);
          var error = null;
          try {
            GhilbertTest.run_verifier(url_context, file, verify_context);
          } catch (exception) {
            error = '' + exception;
          }
          if (error === null && command == '!reject') {
            failures += 1
            var expected = tokens.slice(2, 999999).join(' ');
            print('' + lineno + ': FAIL, expected error: ' + expected);
          }
          else if (error !== null && command == '!accept') {
            failures += 1
            print('' + lineno + ': FAIL, got unexpected ' + error);
          }
        }

        url_context.revert();
      }
      else {
        failures += 1;
        print('' + lineno + ': FAIL, unrecognized command ' + command);
      }
    }
    else {
      var trimmed = line.trim()
      if (trimmed !== '' && trimmed[0] !== '#') {
        url_context.append_current(line, lineno);
      }
    }
  }
  return [tests, failures];
}

if (arguments.length != 1) {
  print();
  print('Usage: rhino js/verify_test.js testsuite');
}
else {
  var results = GhilbertTest.run(readFile(arguments[0]));
  tests = results[0];
  failures = results[1];
  print(tests, 'tests run,', failures, 'failures');
  if (failures > 0) {
    // what is a better way to exit with unsuccessful exit status?
    throw("there were test failures");
  }
}

