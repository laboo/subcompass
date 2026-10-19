# Subcompass

Arithmetic models of a universe built from two numbers, +1 and −1. Each model
is written in [Lean](https://lean-lang.org), a programming language whose
checker refuses any rule that leaves a case undefined and any proof with a gap.

## What's here

| Path | What it is |
| --- | --- |
| `The Model, v0.1.md` | The Model in plain words, matching the Lean below rule for rule. |
| `Subcompass/OSM.lean` | OSM ("our standard model", not physics' Standard Model): the same model, stated exactly in Lean, with each rule tagged by where it comes from. Start with its opening comment. |
| `Subcompass.lean` | Imports every model, so one command checks them all. |
| `lean-toolchain` | The exact Lean version: 4.35.0. |
| `scripts/setup-lean.sh` | Gets that Lean and checks every model. |
| `.github/workflows/check.yml` | GitHub runs the same check on every push. |

## Check it

On Linux, including Claude's cloud sandboxes, from the repo folder:

```
scripts/setup-lean.sh
```

The first run downloads Lean from GitHub (about 600 MB, 3 GB unpacked, a few
minutes); after that it takes seconds. To re-check later, run `lake build`
with `~/.elan/bin` on your `PATH`.

On a Mac or Windows machine, install [elan](https://github.com/leanprover/elan)
and run `lake build` in the repo folder; elan reads `lean-toolchain` and fetches
the right Lean itself.

A passing check ends with `Build completed successfully`. Above that, the
`#print axioms` lines at the end of each model list what each proof rests on:
only Lean's standard rules of logic (`propext`, `Quot.sound`,
`Classical.choice`). If `sorryAx` ever appears there, a proof is unfinished.

## Adding a model

1. Write `Subcompass/YourModel.lean`, inside its own `namespace YourModel`.
2. Add `import Subcompass.YourModel` to `Subcompass.lean`.
3. Run `lake build`, and commit only when it passes with no errors.

To run the same tests against several models, give yours the common shape
`ArithModel` from section 8 of `Subcompass/OSM.lean` (add
`import Subcompass.OSM` at the top of your file).
