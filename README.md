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
| `Subcompass.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | The shared Lean setup (Lean 4.35.0 and Mathlib v4.35.0), where the test suite will live. |
| `Subcompass/Suite.lean` | The shared test suite: how a model plugs in, and the tests. Its opening comment explains it. |
| `scripts/setup-lean.sh` | Installs that Lean and Mathlib on Linux and builds the project. |
| `.github/workflows/check.yml` | GitHub builds the project on every push. |
| `.github/workflows/mathlib.yml` | Publishes Mathlib, already built, as the release `mathlib-v4.35.0`, for the setup script to download. |
| branch `baseline` | The original model, from before the contest. |
| branch `team-n` | Team n's models. |
| tag `tNgM` | The model team N produced in generation M, for example `t3g2`. |

## Check it

On Linux, including Claude's cloud sandboxes, from the repo folder:

```
scripts/setup-lean.sh
```

The first run downloads everything from GitHub, so it works even where Lean's
and Mathlib's own servers are blocked: Lean (about 600 MB, 3 GB unpacked) and
Mathlib with all its built files (about 1.9 GB, 7.3 GB unpacked, kept in
`~/.cache/subcompass` and shared by every copy of the repo on the machine).
That takes a few minutes; after that a run takes seconds, and Mathlib is never
rebuilt. To re-check later, run `lake build` with `~/.elan/bin` on your `PATH`.

On a Mac or Windows machine, install [elan](https://github.com/leanprover/elan)
and run `lake exe cache get` and then `lake build` in the repo folder; elan
reads `lean-toolchain` and fetches the right Lean itself, and `cache get`
fetches Mathlib's built files from Mathlib's own servers.
