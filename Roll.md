# Roll

Team 5's model, generation 0 (tag `t5g0`). The Lean is in `Subcompass/Roll.lean` (motion in any dimension), `Subcompass/RollPlace.lean` (the same motion written out in 3D), `Subcompass/RollWorld.lean` (things in 3D space) and `Subcompass/RollSuite.lean` (the shared test suite).

## The problem it takes on

Zigzag (team 4) gave the contest motion: a line of cells, with locked ticks and no global clock, where matter hops the way its hand points. It got stuck at one dimension. A hand is one bit, and a line has two directions, while space has many. 4:0 called this the critical point: if motion can't be made to work the same way in every dimension, the approach is probably a dead end. 4:0 also suggested where to look. Don't put particles in a grid. Let simplices move by giving up a corner and taking a new one on the far side of a face.

Roll does exactly that, with one rule that uses only addition.

## The rule

A simplex in d-dimensional space has d + 1 corners. Roll keeps them in a ring, so every corner has one corner before it and one after it. The corners are points with whole-number coordinates. To **tip** the simplex over the face opposite corner i:

> replace corner i by (the corner before it) + (the corner after it) − (itself).

Nothing else changes. In 1D a segment tips over one of its ends; in 2D a triangle tips over an edge; in 3D a tetrahedron tips over a face.

The *steps* of a simplex are the arrows from each corner to the next one round the ring. A proper simplex's steps are the d unit directions plus one more, minus all of them, which closes the loop. Every proper simplex is the same shape, and together they fill space with no gaps (Kuhn's triangulation).

**What Lean proves, for every dimension:**

- **A tip swaps two neighbouring steps** and changes nothing else. So a proper simplex always tips into a proper simplex of the same shape, sharing a face with the old one.
- **Each move is one lattice step.** The corner that moves shifts by the difference of two directions. In 2D those are the 6 directions of a hexagon; in 3D the 12 directions of the densest packing of spheres.
- **Every move can be undone.** Tipping twice at the same corner gets you back. So any history can be run backwards.
- **Far corners need no order.** Tips at two corners that aren't neighbours give the same result in either order: Zigzag's "no global now", inside a single simplex.
- **The braid law.** For neighbouring corners, tip i, i + 1, i is the same as tip i + 1, i, i + 1. Together these three laws are the laws of a known group: the one that moves the simplices (alcoves) of the group SU(d + 1).

## Rolling, and light

To **roll** forward, tip at the first corner and then count the corners from the next one round the ring, so the next tip is again at the first corner. To roll back, do the opposite. Rolling back undoes rolling forward exactly.

**A roll keeps one step fixed and turns the others one place round the ring** (Lean proves this for every dimension). Call the fixed step the *seam*. After d rolls, the other steps are back where they started. So the simplex is itself again, moved by exactly one lattice step, against its seam. Lean checks this for every proper simplex in 1D, 2D, 3D and 4D.

So a thing that keeps rolling the same way goes in a **straight line at a steady speed**: one lattice step every d tips. Which way it goes depends on its seam and on forward versus back. That gives 2(d + 1) straight directions: 2 in a line, 6 in a plane, 8 in space, all at the same speed. In 1D one roll is one tip, and it is exactly Zigzag's hop. So Zigzag is Roll in one dimension.

## Things in space

In 3D, Roll's world is Velcro's things (team 3), each sitting on a tetrahedron. The events are Zigzag's with the hop replaced by a roll:

- **join, part, pair**: Velcro's addition events, at one tetrahedron.
- **roll**: a thing rolls one tip, forward or back. It locks its tetrahedron and the one it rolls into, which shares a face and is one step away.

**The one rule: matter rolls the way its hand turns.** Right-handed things roll forward round the ring and left-handed things roll back. Force carriers have no hand and roll either way. This fixes what stopped Zigzag at one dimension. *Which way in space* a thing goes isn't stored in the thing; it's stored in the order of its tetrahedron's corners. The hand only says forward or back along that way. Two electrons on differently ordered tetrahedra go different ways. In The Unflattening's words, "order matters".

**What Lean checks, with no gaps and only the standard axioms:**

- Velcro's one law still holds, so charge, colour, baryon number and lepton number are all kept.
- **Locality:** a tick reads and changes only the places it locks, and those are at most one step apart. The distance is how far apart two tetrahedra's centres are, in lattice steps, and it obeys the triangle law.
- **No global now:** ticks on separate places can happen in either order with the same result.
- **A speed limit**, from the new suite section: after n ticks, what a place holds depends only on what was within n steps of it.
- **Only the Higgs turns matter round.** The photon, the W and the gluons never change a particle's hand. So a massless particle rolls straight forever, and a massive one zigzags back and forth along its line.
- **The weak force touches only matter that rolls back** (left-handed), and antimatter that rolls forward.
- **Worked examples:**
  - A right-handed electron rolls 3 tips and is one step along the cube's diagonal, then 12 tips and four steps.
  - A left-handed one rolls back along the same line, and can't roll forward.
  - The zigzag in 3D: the electron rolls back, takes in a Higgs, rolls forward to where it started, gives the Higgs off, and rolls back again.

**Shared suite** (`RollSuite.lean`):

- **Passes the new "space in any dimension" tests:** `LocalIn`, `ReadsLocksIn`, `NearIn`, `NoGlobalNowIn` and `SpeedLimitIn`.
- **Passes everything Zigzag passes:** charge, baryon and lepton conservation, `ChargeCarried`, `ProtonStable`, β decay among onlookers and via a real W, annihilation into light, family 1, and `MakesBoson` for the photon, gluon, W⁺, W⁻ and Higgs, plus the prediction tests.
- **Fails what Zigzag fails:** `MakesBoson .z` and `BetaDecay`.

## What it changed in the shared suite

Section 10 on `main`, "Space in any dimension", committed before anything was proved for Roll. Section 9's space is a line of numbered cells. Section 10 lets a model bring its own kind of place and a distance between places that obeys the triangle law. It asks for the same locality tests and proves the speed limit once, for every model. A line of cells is one example (`Spacetime.toSpace`).

## Limits, honestly

- **Light isn't round.** In 3D a thing rolls straight in only 8 directions: the diagonals of a cube. That is far from "the same in every direction". The hope, untested, is that roundness appears on average, from many tetrahedra in many orders or from adding up many paths.
- **Straight rolling is proved in Lean only for dimensions 1 to 4.** The reason it works in every dimension (a roll keeps the seam and turns the other steps) is proved in general, and the rest of the argument is short. The corner opposite the seam moves by each of the other steps once, and those add up to minus the seam. But that last part isn't written in Lean yet.
- **Space is still a fixed tiling.** Tetrahedra roll over a given lattice of points, so space doesn't curve yet. Curvature, and so gravity, would need simplices that don't all fit the same lattice: Regge's "count the simplices round an edge".
- **The SU(d + 1) link is a resemblance, not a result.** The moves of a d-dimensional simplex are the steps of SU(d + 1)'s lattice. That is SU(4), "colour with the lepton as a fourth colour", for our space, and it contains SU(3), colour. But the tiling was chosen knowing this, and nothing yet shows that the moves which change colour are the gluon's.
- **As in Zigzag:** rolling is allowed, never required. Nothing fixes how often a particle meets the Higgs, so masses aren't numbers yet. One family only, and colour isn't confined.
