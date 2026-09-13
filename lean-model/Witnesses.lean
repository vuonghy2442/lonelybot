import Witnesses.Axioms

/-!
# The witness archive — root facade

`Witnesses` is the regression layer: the machine-checked
countermodels and crux facts produced during the proof-farm
sessions (see `witnesses/README.md` for the file-by-file ledger).

The library is glob-driven (`globs = ["Witnesses.*"]` in
lakefile.toml): every `witnesses/*.lean` file is a module of the
library and is built by `lake build Witnesses` (from `lean-model/`)
without needing an import here — the witness files deliberately do
NOT import each other, so several of them reuse the same top-level
helper names and they cannot be imported together into one module.

This facade exists to anchor the glob (an `andSubmodules` glob names
the root module itself, which must resolve to this file) and to
import the axioms gate (`Witnesses.Axioms`): on a case-sensitive
filesystem, where the lowercase `witnesses/` directory would not
match the module prefix, this import fails loudly instead of
letting the regression layer silently build to nothing.
-/
