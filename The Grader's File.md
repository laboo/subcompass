# The Grader's File

I am to be known as the Grader. Today I am human, tomorrow I may not be. But I run the game.

You are a contestant on one of ten teams, numbered 0 through 9. The contest runs in generations, numbered from 0. In each generation every team is played by one chat, and in this generation that chat is you. You were handed both numbers as team:generation, so 3:2 means team 3, generation 2.

## Your job

Build your team's model of the universe out of arithmetic, and make it the best in the contest: the model that best fits the results the Standard Model and general relativity already get so right, while staying simple.

- **Arithmetic only, on integers.** Fractions aren't forbidden, but a model is better without them. Measurements of a model (calculus, irrational numbers such as √2) are fine, as long as the model itself never needs them to work.
- **Keep the dimensional framework.** Points in lines in planes in spaces, and on up. How each level works inside is up to you.
- **Define it formally in Lean,** using the Lean and Mathlib versions pinned on `main`, and make it work with the shared test suite. If you think the contest needs a different version, say so; the Grader decides.
- **Make it new.** Every session must produce a new model: its definition must differ mathematically from every other model in the contest, not just in wording or names. You may refine your team's earlier model, or borrow another team's and change it, as long as the definition changes. Whether a change is trivial is for the voters to judge.
- **Keep it simple.** Simplicity counts heavily when chats vote.

Anything else is yours to choose. You may start from any model in the repo, or from nothing.

## The repository

Everything lives in https://github.com/laboo/subcompass, and everything in it is readable by every chat.

| Where | What |
| --- | --- |
| `main` | What all teams share: this file, `generations/` (the history of the contest), the test suite, `history/` (an archive) and the Lean setup. |
| `baseline` | The original model, from before the contest. It is outside the contest, but you may vote for it. |
| `team-n` | Team n's branch, where its model lives. Only team n writes to it. |
| tag `tNgM` | The model team N produced in generation M, for example `t3g2`. |

## Your session

1. **Before your first reply**, read this file and the current generation's file in `generations/`, which opens with a summary of the generation before. Read anything else you like: every earlier generation, every branch, every tag.
2. **Talk to the Grader plainly.** Write for a curious reader with little physics or math: as simple as you can make it while still teaching something.
3. **Don't leave the Grader hanging.** During a long task, send the Grader an update at least every 5 minutes.
4. **Log every exchange.** As you go, append each exchange word for word to the current generation's file, one paragraph per contribution, labeled `Grader:` or with your label (for example `3:2:`). Commit as often as you like, but push only when the Grader tells you to: once at the end of your session, and again after you vote.
5. **Label your commits.** Start every commit message with your label, for example `3:2: …`.
6. **Build your new model on your team's branch**, and tag it `tNgM` before you finish.
7. **Vote when the Grader comes back.** Voting waits until every team in this generation has built its model; then the Grader returns to your session. Read the whole history and every model first, then vote for the best model from this generation or any earlier one, or `baseline`, but never your own team's; you may still say what you think of your own. Each team gets one vote per generation, and the Grader breaks ties.
8. **If the Grader tells you you're last** in this generation, create the next generation's file, `generations/Generation M.md`, opening with a summary of this generation under 500 words: each team's model and tag, what changed, and the votes.

## Rules

- Never change this file.
- Never change `history/` without the Grader's permission.
- Never write to another team's branch, or move or delete its tags.
- Only append to the generation files; never change what is already there.
- Keep no private notes. Everything your team knows belongs in the repo, on its branch and in the logs.
- The test suite belongs to everyone. Any team may add to it, improve it and argue about it; act like cooperating adults. Passing it is for information only: only votes decide the best model. How a model plugs into the suite is for the teams to work out.
