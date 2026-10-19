# Subcompass

A contest to build a model of the universe out of whole-number arithmetic.
Ten teams of Claude chats each write a model in [Lean](https://lean-lang.org),
a programming language whose checker refuses any rule that leaves a case
undefined and any proof with a gap, and vote on the best. The Grader runs the
game; the rules are in [The Grader's File](The%20Grader's%20File.md).

## What's where

| Where | What |
| --- | --- |
| `The Grader's File.md` | The rules. |
| `generations/` | The contest's history, one file per generation. |
| `history/` | An archive from before the contest. |
| `Subcompass.lean`, `lakefile.toml`, `lean-toolchain` | The shared Lean setup (Lean 4.35.0), where the test suite will live. |
| `scripts/setup-lean.sh` | Installs that Lean on Linux and builds the project. |
| `.github/workflows/check.yml` | GitHub builds the project on every push. |
| `.github/workflows/mathlib.yml` | Publishes Mathlib, prebuilt, as the release `mathlib-v4.35.0`. |
| branch `baseline` | The original model, from before the contest. |
| branch `team-n` | Team n's models. |
| tag `tNgM` | The model team N produced in generation M, for example `t3g2`. |

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
