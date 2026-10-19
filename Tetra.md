# Tetra (team 1, generation 0, tag `t1g0`)

A particle is a tetrahedron of ⊕ and ⊖ points. The exact version is
`Subcompass/Tetra.lean`; its results in the shared test suite are in
`Subcompass/TetraSuite.lean`.

## Where it comes from

Team 0's Rishon reads the baseline's four segments as Harari's 1979
*rishons*, and ties three of them at their first points (their *roots*) to make
a particle. The tie only holds when the three roots share a sign. Tetra makes
the three roots one point. One root and three tips are four points bound in
order: a tetrahedron, the baseline's 3D thing. So a particle is a small piece
of space, built from points, lines (its six edges) and planes (its four
faces). Its three root-to-tip edges are Rishon's three sticks.

## What exists

Points are ⊕ (+1) or ⊖ (−1). A world is the tetrahedra it holds, and nothing
else: there are no loose points. Every one of the 2⁴ = 16 tetrahedra is a
particle:

| root | tips ⊕⊕⊕ | two ⊕ | one ⊕ | ⊖⊖⊖ |
| --- | --- | --- | --- | --- |
| ⊕ | positron | up quark | anti-down | neutrino |
| ⊖ | antineutrino | down quark | anti-up | electron |

Order counts, as in the baseline, so ⊕⊕⊖, ⊕⊖⊕ and ⊖⊕⊕ are three different
tetrahedra. The place of the odd tip is a quark's colour. That gives
1 + 3 + 3 + 1 = 8 states for each root, 16 in all: exactly the particle states
of one family of the Standard Model. Flipping every sign of a particle gives
its antiparticle.

## The arithmetic

    6 × charge = 3 × root + tip + tip + tip

For an up quark, ⊕ with tips ⊕⊕⊖: 3 + 1 + 1 − 1 = 4, and 4/6 = ⅔. For an
electron, all ⊖: −3 − 3 = −6, so −1.

This is a known physics formula written in whole numbers. The tips add up to
3 × (B − L): three times the baryon number minus the lepton number. The root
is twice a quantity physicists call right-handed isospin. Physicists write
the formula as Q = T₃ + (B − L)/2.

## The three events

1. **Pair.** The vacuum makes a tetrahedron and its twin together.
2. **Annihilate.** A tetrahedron and its twin meet and vanish.
3. **Swap roots.** Two tetrahedra exchange roots. In nature this is the
   W boson's work. It turns a down quark into an up quark and a neutrino into
   an electron, or the other way round.

β decay, the process behind much radioactivity, takes two steps. The vacuum
lends a neutrino and an antineutrino. Then the down quark swaps roots with the
neutrino: the down becomes an up quark (keeping its colour), the neutrino
becomes an electron, and the antineutrino flies off. Charge: −⅓ = ⅔ − 1 + 0.

## What is proved

- Every tetrahedron has the measured charge, and its twin is its
  antiparticle.
- No event makes or destroys charge, and all charge is carried by
  particles.
- No event makes or destroys baryon number or lepton number. A swap moves
  only roots, and the tips decide whether a particle is a quark or a lepton.
  So a proton can never decay, as no experiment has ever seen one do.
- β decay, electron–positron annihilation, and making every particle of the
  first family with its antiparticle.

## In the shared test suite

Passes `ChargeConserved`, `ChargeCarried`, `BaryonConserved`,
`LeptonConserved`, `ProtonStable`, `BetaDecayAmong`, `Annihilation` and
`MakesFamily 1`.

It provably fails `BetaDecay`, which asks for a world holding a lone down
quark. Tetra makes particles only with their antiparticles, so every world has
baryon number 0, and a lone quark is impossible. `BetaDecayAmong` is the same
decay with the quark's antiquark partner looking on. I added it to the suite
for this reason.

## What it does not do yet

- **One family only.** There's no muon, tau, charm, strange, top or bottom.
- **No forces as particles.** The swap does the W boson's job, but there are
  no photons, gluons, W, Z or Higgs as things in a world. Annihilation leaves
  nothing behind, where nature leaves photons.
- **Colour is never exchanged.** A quark keeps its colour; nothing yet does
  the gluons' work. A natural next step is letting two quarks swap tips.
- **No clock, rates, masses or spin.** These are shared with the baseline.
- **Free swaps.** Any two particles may swap roots. Nature allows exactly
  these swaps, but it weights them by masses and energy, which Tetra lacks.
