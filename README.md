# Ghilbert

Ghilbert is a formal proof checker, heavily inspired by
[Metamath](http://us.metamath.org/). This repo contains a new
implementation in progress, written Rust, as well as an older
prototype, written in Python.

A few more resources are at [ghilbert.org](http://ghilbert.org/).
There's also a fair amount of discussion on the [mailing
list](https://groups.google.com/forum/#!forum/ghilbert).

## Quick start

This quick start translates the propositional calculus fragment
from Metamath into Ghilbert format and checks it.

Check out a copy of [set.mm](https://github.com/metamath/set.mm).

```
cd mm_xlat
cargo run -- script ../../set.mm/set.mm /tmp/out.gh
cd ..
cargo run -- /tmp/out.gh
```

This will spew a lot of diagnostics, and also generate a file
called `out.html`.

## License

All of the Rust, Python, and JavaScript code is under Apache 2 license,
a copy of which is in [LICENSE](LICENSE).

Note: includes the minified JavaScript version of google-diff-match-patch,
which is (also) under Apache 2 license. For full attribution, please see:
http://code.google.com/p/google-diff-match-patch/

Proofs under `content/general` are under
[Creative Commons Share Alike 3.0](http://creativecommons.org/licenses/by-sa/3.0/).
All other proofs are under [Creative Commons CC0 Public Domain
Dedication](http://creativecommons.org/publicdomain/zero/1.0/).
Many of the proofs are derived in some form from Metamath's set.mm, which
is also under CC0.

## Contributing

The main author is Raph Levien, with contributions from many others.
*(TODO: improve contributor attributions)*

Contributions are welcome, just send a pull request!
