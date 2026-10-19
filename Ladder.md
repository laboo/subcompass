# Ladder (team 2, generation 0, tag `t2g0`)

Team 1's Penta is a particle for 3D space. Ladder builds the same kind of
particle on every rung of the dimension ladder, and adds the one exchange
Penta lacked: colour, the gluon's work. The exact version is in
`Subcompass/Ladder.lean` (any dimension) and `Subcompass/LadderSuite.lean`
(our three dimensions, and the shared test suite).

## Why every dimension

In Penta three things come out as the same number, three: a quark's charge
is in thirds, quarks come in three colours, and space has three dimensions.
That could be a coincidence, or it could be one fact. The way to tell is to
build the model for space of any dimension d, choosing nothing about three,
and see what the arithmetic does.

## What exists

Points are ⊕ (+1) or ⊖ (−1). In space of dimension d, a particle is a
simplex with d + 2 points: a **root**, d **tips** (one per direction of
space), and a **hand**, the point added in the jump to the next dimension.
A world is just the particles it holds; there are no loose points.

## The arithmetic

    2d × charge = the sum, over the d edges at the root, of both ends of each edge
                = d × root + all the tips
    hand        = the product of all d + 2 points   (−1 = left, +1 = right)

At d = 3 this is Penta exactly: 6 × charge = 3 × root + tips. The factor of
three in front of the root is no longer put in by hand: it's the number of
edges at the root, which is the dimension.

| root | no tip ⊖ | one ⊖ | two ⊖ | three ⊖ |
| --- | --- | --- | --- | --- |
| ⊕ | positron | up quark | anti-down | neutrino |
| ⊖ | antineutrino | down quark | anti-up | electron |

A quark's **colour** is the place of its odd tip.

## The five events

1. **Pair.** The vacuum makes a particle and its twin (every sign flipped).
2. **Annihilate.** A particle and its twin meet and vanish.
3. **Swap** (the W boson). Two particles whose hand agrees with their root
   trade roots, each hand going with its root. A down quark becomes an up, a
   neutrino becomes an electron.
4. **Flip** (mass). A hand point moves to the other side.
5. **Twist** (the gluon, new in Ladder). Two particles both swap their tips at
   the same two places, when their tips at the first place add up to the same
   as at the second. That keeps the world's total at every place, so colour
   is never made or lost. A red and a green quark can trade colours; a quark
   and its antiquark can change colour together; but no quark can change
   colour beside a lepton, or on its own.

So the geometry now does work along every kind of edge: the edges at the root
carry charge, the root–hand edge decides who feels the W, and the edges
between tips carry colour.

## What is proved, for every dimension d

- **Charge comes in steps of e/d.** Every charge is a whole number of
  d-ths of the electron's.
- **The smallest charge comes in exactly d colours.** A particle with charge
  −e/d (a "down quark") has d kinds, one per place of its odd tip.
- **Fractional charge always comes with colour.** If a charge, in lowest
  terms, has denominator q, the number of kinds with that charge is a
  multiple of q. At d = 3 this is "thirds come in threes", but nothing chose
  three: it comes from a fact about counting (k × (d choose k) is always a
  multiple of d).
- **Twins have opposite hands exactly when d is odd**, that is, when
  spacetime (d space plus one time) has an even number of dimensions. The
  antiparticle of a left-handed electron is right-handed, as in nature, only
  because our spacetime has 4 dimensions. Physicists know that left- and
  right-handed particles of this kind exist only in even dimensions; here
  that comes out of counting points.
- **Every event keeps charge and colour**, place by place, in every
  dimension.

## What is proved in our space, d = 3

- Every particle has its measured charge, and its twin is its antiparticle
  with the opposite hand.
- The W touches exactly the left-handed particles and the right-handed
  antiparticles.
- No event changes charge, baryon number or lepton number. A gluon never
  changes which particle something is, only its colour.
- β decay for a left-handed down quark; two quarks trading colours; a quark
  and antiquark changing colour together; and no quark changing colour
  beside a lepton.

## In the shared test suite

Passes `ChargeConserved`, `ChargeCarried`, `BaryonConserved`,
`LeptonConserved`, `ProtonStable`, `BetaDecayAmong`, `Annihilation`,
`MakesFamily 1`, and the prediction tests `TwinFlipsHand`,
`VectorlikeCharge`, `OneFamilyCharges`, `ThirdsComeInThrees` and (new this
session) `TwinIsAnti`.

It provably fails `BetaDecay`, as Penta does: the vacuum makes particles
only with their antiparticles, so no world holds a lone down quark.

## What it does not do yet

- **One family only.** No muon, tau, charm, strange, top or bottom.
- **No forces as things.** Swap and twist do the W's and the gluon's work,
  but there are no photons, gluons, W, Z or Higgs in a world, and
  annihilation leaves nothing behind.
- **Colour is conserved but not confined.** Nothing yet stops a world from
  being split into coloured pieces; in nature quarks are always found in
  colourless groups.
- **Only d = 3 matches nature,** of course: at other d the charges differ.
  Ladder explains why charge, colour and dimension share one number; it
  doesn't explain why space has three dimensions.
- **No rates, masses or clock,** as in the baseline and Penta.
