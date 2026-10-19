# Penta (team 1, generation 0, tag `t1g0`)

A particle is a 4-simplex (a "5-cell") of ⊕ and ⊖ points. The jump from 3D to
4D is what makes it left- or right-handed. The exact version is
`Subcompass/Penta.lean`; its results in the shared test suite are in
`Subcompass/PentaSuite.lean`.

## Where it comes from

Team 0's Rishon reads the baseline's four segments as Harari's 1979
*rishons*, and ties three of them at their first points (their *roots*) into a
particle. The tie only holds when the three roots share a sign. So in this
session I first made the three roots one point. One root and three tips make
a tetrahedron, the baseline's 3D thing. That model, Tetra, got one family's
charges right, but its particles had no hand.

Penta takes one more step up the baseline's ladder. Raising a thing one
dimension means adding a point off its flat, and that point can go on either
side. The baseline notes this choice and never uses it. In Penta that choice
is the particle's hand.

## What exists

Points are ⊕ (+1) or ⊖ (−1). A particle is five points bound in order: a
root, three tips, and a *hand*, the point added in the jump to 4D. A world is
the particles it holds, and nothing else: there are no loose points. Every
one of the 2⁵ = 32 four-simplices is a particle:

| root | tips ⊕⊕⊕ | two ⊕ | one ⊕ | ⊖⊖⊖ |
| --- | --- | --- | --- | --- |
| ⊕ | positron | up quark | anti-down | neutrino |
| ⊖ | antineutrino | down quark | anti-up | electron |

Each comes left- or right-handed. Order counts, so the place of the odd tip is
a quark's colour. 32 is exactly one complete family of the Standard Model:
every particle and antiparticle, every colour, both hands. That includes the
right-handed neutrino, which the Standard Model leaves out but whose existence
neutrino masses strongly suggest.

## The arithmetic

    6 × charge = 3 × root + tip + tip + tip
    hand = root × tip × tip × tip × hand point   (⊖ = left, ⊕ = right)

The hand point carries no charge. The hand is the baseline's own *value*, the
product of a thing's points. A twin flips all five points, an odd number, so
it also flips the hand: the antiparticle of a left-handed electron is a
right-handed positron, just as in nature. (A tetrahedron has four points, so
its twin keeps its hand. The rule alternates with every jump in dimension,
and 4D lands on the side physics needs.)

A particle *feels the W boson* when its hand point agrees with its root. Lean
checks that these are exactly the left-handed particles and the right-handed
antiparticles. That's the most striking fact about the weak force: it can
tell left from right. Here it comes out of the counting rather than being
added by hand.

## The four events

1. **Pair.** The vacuum makes a particle and its twin together.
2. **Annihilate.** A particle and its twin meet and vanish.
3. **Swap.** Two particles that feel the W exchange roots, each hand point
   travelling with its root. This is the W boson's work: a down quark becomes
   an up quark and a neutrino becomes an electron, and neither changes hand.
4. **Flip.** A particle's hand point moves to the other side, so a
   left-handed particle becomes right-handed. In nature this is what mass
   does: a massive particle keeps turning from one hand to the other.

β decay takes two steps. The vacuum lends a neutrino and an antineutrino.
Then a left-handed down quark swaps with the neutrino: the down becomes a
left-handed up quark (keeping its colour), the neutrino becomes a left-handed
electron, and the antineutrino flies off. A right-handed down quark can't do
it, as in nature.

## What is proved

- Every particle has its measured charge; its twin is its antiparticle with
  the opposite hand.
- The W touches exactly the left-handed particles and the right-handed
  antiparticles, and never changes a hand.
- No event makes or destroys charge, baryon number or lepton number, and all
  charge is carried by particles. So a proton can never decay, as no
  experiment has ever seen one do.
- β decay for a left-handed down quark, and not for a right-handed one;
  electron–positron annihilation; making every particle of the first family
  with its antiparticle.

## In the shared test suite

Passes `ChargeConserved`, `ChargeCarried`, `BaryonConserved`,
`LeptonConserved`, `ProtonStable`, `BetaDecayAmong`, `Annihilation` and
`MakesFamily 1`.

It also passes the prediction tests, which read only the charges and hands
Penta's own arithmetic gives, never the particle names: `TwinFlipsHand`,
`VectorlikeCharge`, `OneFamilyCharges` (including a right-handed neutrino)
and `ThirdsComeInThrees` (fractional charge only ever comes in threes).

It provably fails `BetaDecay`, which asks for a world holding a lone down
quark. Penta makes particles only with their antiparticles, so every world has
baryon number 0, and a lone quark is impossible. `BetaDecayAmong` is the same
decay with the quark's antiquark partner looking on.

## What it does not do yet

- **One family only.** There's no muon, tau, charm, strange, top or bottom.
- **No forces as particles.** The swap does the W boson's job, but there are
  no photons, gluons, W, Z or Higgs as things in a world. Annihilation leaves
  nothing behind, where nature leaves photons.
- **Colour is never exchanged.** Nothing yet does the gluons' work. A natural
  next step is letting two quarks swap tips.
- **No rates, masses or clock.** Flip says that a mass turns hands, not how
  often, so every particle may flip as freely as any other. These
  limits are shared with the baseline.
- **The geometry is still mostly bookkeeping.** The side of the jump gives
  the hand, but the events never use edges, faces or touching.
- **No arrow of time.** The 3D → 4D side can be read as past and future, but
  nothing in the rules prefers one.
