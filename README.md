# Ghilbert

Ghilbert is a formal proof checker, heavily inspired by
[Metamath](http://us.metamath.org/). This repo contains a new
implementation in progress, written Rust, as well as older versions:

* `ghilbert_2014`: the Python and JavaScript implementation from
  2010-2015, with the web app and proof content. The tag `ghilbert-2010`
  marks its state at the end of 2010.
* `ghilbert_2007`: a snapshot of the original Python prototype from
  2005-2007.

A few more resources are at [ghilbert.org](http://ghilbert.org/).
There's also a fair amount of discussion on the [mailing
list](https://groups.google.com/forum/#!forum/ghilbert).

## Quick start

This quick start translates the propositional and predicate calculus
fragment from Metamath into Ghilbert format and checks it.

Check out a copy of [set.mm](https://github.com/metamath/set.mm).

```
cd mm_xlat
cargo run -- script ../../set.mm/set.mm /tmp/out.gh
cd ..
cargo run -- /tmp/out.gh
```

This will spew a lot of diagnostics, and also generate an HTML file for
each proof in the `gen` directory. Note that to view these files
you probably want a simple server like `python3 -m http.server`
rather than using `file://` URL's, because the JavaScript interactivity
features load further files using XMLHttpRequest.

To translate and check all of set.mm instead of stopping at the end of
predicate calculus, use `--all`. Translation takes roughly 5 minutes, and
the check about 10 seconds. The theorem pages aren't published past
predicate calculus, because for all of set.mm the HTML is well over a
gigabyte.

```
git -C path/to/set.mm checkout b975dbbd636372803f3102045aa333771f25a477
cargo build --release
cargo build --release --manifest-path mm_xlat/Cargo.toml
mm_xlat/target/release/mm_xlat --all mm_xlat/script path/to/set.mm/set.mm /tmp/all.gh
target/release/ghilbert -q -k /tmp/all.gh
```

This should print `checked 48276 theorems, 0 failed`. The revision is the
same one pinned in `.github/workflows/pages.yml`.

## License

All of the Rust, Python, and JavaScript code is under Apache 2 license,
a copy of which is in [LICENSE](LICENSE).

Note: includes the minified JavaScript version of google-diff-match-patch,
which is (also) under Apache 2 license. For full attribution, please see:
http://code.google.com/p/google-diff-match-patch/

Proofs under `ghilbert_2014/content/general` are under
[Creative Commons Share Alike 3.0](http://creativecommons.org/licenses/by-sa/3.0/).
All other proofs are under [Creative Commons CC0 Public Domain
Dedication](http://creativecommons.org/publicdomain/zero/1.0/).
Many of the proofs are derived in some form from Metamath's set.mm, which
is also under CC0.

## Contributing

The main author is Raph Levien, with contributions from many others.
*(TODO: improve contributor attributions)*

Contributions are welcome, just send a pull request!
