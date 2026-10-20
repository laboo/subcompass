# Zigzag (team 4, generation 0, tag `t4g0`)

Velcro (team 3) made every force carrier a thing and every event an
addition, but its world is a bag with no space in it: nothing is anywhere, so
nothing can move. Zigzag puts Velcro's things in space and gives the contest
its first clock. The exact version is in `Subcompass/Zigzag.lean` (the model)
and `Subcompass/ZigzagSuite.lean` (the shared test suite).

The name comes from the zig-zag picture of the electron (Penrose's, and
Feynman's "checkerboard"), which 1:0 mentioned and which falls out here.

## What exists

**Space is a line of cells.** Each cell is a point of space, and the line is
made of those points. Each cell holds a Velcro bag: matter (five slots, each
⊕ or ⊖, the 32 particles of one family) and force carriers (the photon 0, the
W, the gluons, the Higgs). One dimension first, because a grid of cells in
3D has favoured directions, as a chessboard does, and that problem is best
met after the simple case works.

## What a tick is

A **tick** is one event. It locks the cells it needs, does its work there,
and lets them go. That is the Grader's lock idea, from 3:0's session.

| tick | what happens | cells it locks |
| --- | --- | --- |
| join | two things in a cell become their sum | that cell |
| part | a thing in a cell becomes two that add up to it | that cell |
| pair | a cell lends a thing and its twin | that cell |
| hop | a thing moves one cell left or right | its cell and the one it moves into |

There is **no global clock**. Each cell has its own: the number of ticks
that have locked it. Two ticks on different cells come in no order at all.

## The one new rule: the hand is a direction

**Matter hops only the way its hand points.** A particle's hand is the
product of its five points, as in Penta and Velcro: ⊖ is left-handed, ⊕
right-handed. In Zigzag that is literally the way it moves: left-handed
particles move left, right-handed ones move right. A force carrier has no
hand (its product is 0), so it hops either way.

This isn't a pun. In nature, a massless particle's handedness is its spin
measured along its direction of motion. On a line there is no spin left
over, only the direction, so handedness and direction of motion become one
thing. Physicists use exactly this in one-dimensional models: left-handed
means left-moving.

## What comes out

- **Every conservation law still holds.** A tick only regroups or moves
  things, so Velcro's one law, "the world's total never changes", holds in
  space too. Charge, colour and B − L are kept, and baryon and lepton number
  too.
- **Locality.** A tick changes only the cells it locks, and what it does
  depends only on what's in them.
- **No global now.** Two ticks that lock no cell in common can happen in
  either order, with the same result in every cell. So the order in which
  the locks happen to be granted never shows up in the physics: there is no
  fact about which came "first". This is how relativity works: far-apart
  events have no agreed order.
- **A speed limit, not put in by hand.** After n ticks, what a cell holds
  depends only on what was within n cells of it. Nothing travels faster than
  one cell per tick: that is a speed of light.
- **Only the Higgs turns matter around.** The photon, the W and the gluons
  never change a particle's hand (Velcro proved this), so they never change
  its direction. The Higgs always flips the hand, so it always reverses the
  direction. A particle that never meets the Higgs (massless) goes straight
  forever, one cell per hop. A particle that keeps meeting it (massive)
  zigzags, and on average moves slower. The more often it turns, the more
  mass it has. That is the Grader's "mass inside, motion outside", made into
  motion: what happens inside a particle (its hand) steers what it does
  outside (where it goes).
- **The weak force touches only left-moving matter,** and right-moving
  antimatter. That is Velcro's left-handed W, read in space.

A worked example that Lean checks: a left-handed electron goes left; the
vacuum lends a Higgs pair; the electron takes in a Higgs, becomes
right-handed and goes right; it gives the Higgs off, becomes left-handed
again and goes left. That's one zig-zag.

## In the shared test suite

Zigzag passes the new space-and-time tests, added to `main` by 4:0 before
Zigzag was proved against them: `Local`, `ReadsLocks`, `Near`, `NoGlobalNow`,
and so `SpeedLimit`, which the suite proves once for every model that passes
the first three.

It passes everything Velcro passes, with every process happening in one cell:
`ChargeConserved`, `ChargeCarried`, `BaryonConserved`, `LeptonConserved`,
`ProtonStable`, `BetaDecayAmong`, `Annihilation`, `MakesFamily 1`,
`AnnihilatesToLight`, `BetaDecayViaW`, and `MakesBoson` for the photon, the
gluon, the W⁺, the W⁻ and the Higgs. Its things are Velcro's, so it passes
the prediction tests by Velcro's proofs.

It fails what Velcro fails, for the same reasons: `MakesBoson .z` (the empty
container is read as the photon) and `BetaDecay` (no lone quarks).

## What it does not do yet

- **One dimension of space.** Particles still have three tips, one per
  direction of space, but they live on a line. Going to 3D means meeting the
  grid's favoured directions.
- **Light isn't forced to the speed of light.** Carriers hop either way, so
  a photon can wander. Only matter is steered by its hand. A photon that
  moves straight needs a direction of its own, which the empty container
  doesn't have.
- **Hopping is allowed, never required.** Nothing makes a thing hop rather
  than sit, so "speed" means cells per hop, a thing's own count, not cells
  per tick of some outside clock. The speed limit is about ticks, and holds
  regardless.
- **No rates.** How often a particle meets the Higgs is its mass, but
  nothing yet fixes that rate, so the masses aren't modelled, only what a
  mass does.
- **One family; colour not confined;** no strengths, as in Velcro.
