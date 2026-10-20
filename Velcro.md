# Velcro (team 3, generation 0, tag `t3g0`)

Penta (team 1) and Ladder (team 2) build one family of particles out of
signs, and make things happen with rules: a *swap* does the W boson's work, a
*twist* the gluon's, a *flip* the Higgs'. Velcro keeps their particle and
replaces every rule with one operation: **addition**. The force carriers stop
being rules and become things in the world, each one the difference between
two particles. The exact version is in `Subcompass/Velcro.lean` (the model)
and `Subcompass/VelcroSuite.lean` (names and the shared test suite).

The name comes from the Grader's picture in 2:0's session: a particle is a
container with a velcro skin. What's inside is bound by multiplication; what
sticks to the outside is attached by addition; and the empty container, 0, is
where the photon lives.

## What exists

A *thing* has five whole-number slots, on the five points of a 4-simplex: a
**root**, three **tips** and a **hand**. Only these things may exist:

| thing | slots (root; tips; hand) | how many |
| --- | --- | --- |
| matter | every slot ⊕ (+1) or ⊖ (−1) | 32: one family, every colour, both hands |
| photon | 0; 0 0 0; 0 (the empty container) | 1 |
| W⁺, W⁻ | ±2; 0 0 0; ±2 | 2 |
| gluon | 0; +2 on one tip, −2 on another; 0 | 6 |
| Higgs | 0; 0 0 0; ±2 | 2 |

The matter is read as in Penta and Ladder: 6 × charge = 3 × root + tips, the
hand is the product of all five points (−1 left, +1 right), and a quark's
colour is the place of its odd tip.

Each force carrier is the step between two particles. A W flips the root and
the hand together, a gluon moves a ⊖ from one tip to another, the Higgs flips
the hand alone, and the photon is the step that changes nothing.

## The three events

1. **Join.** Two things become one: their sum, if the sum may exist.
2. **Part.** A thing becomes two that add up to it, if both may exist.
3. **Pair.** Nothing becomes a thing and its twin (every sign flipped),
   since a + (−a) = 0.

That's all. Emitting and absorbing a force carrier is part and join. So are
annihilation and decay.

## What comes out

- **One law gives all the conservation laws.** No event changes the world's
  total, slot by slot, because each event only regroups a sum. Charge, colour
  at each place, and B − L are all sums of slots, so each is kept, with no
  separate proof. Baryon number and lepton number aren't sums of slots, but
  Lean checks that they're kept too.
- **Annihilation leaves light.** A particle and its twin add up to five
  zeros: the photon. And 0 + m = m, so absorbing a photon changes nothing.
  This is the Grader's "second flattening": 0 + 1 = 1 forgets the container,
  just as 1 × 1 = 1 forgets the parts. The photon can part into two photons,
  so an electron and a positron become two photons, as in nature.
- **The weak force is left-handed, by arithmetic.** Adding ±2 to a root and a
  hand stays within ±1 only when the two agree. So a W can join exactly the
  left-handed particles and the right-handed antiparticles. Ladder needed a
  rule to say that; here it comes from the W's own slots.
- **Leptons are colourless.** A lepton's tips are all alike, so adding +2 to
  one and −2 to another always leaves the range. No gluon touches a lepton.
- **Inside and outside.** The photon, W and gluons each flip an even number
  of points, so they never change the product of a particle's points, its
  hand. The Higgs flips one point, so it always does. Forces stick to the
  outside, and only the Higgs, the source of mass, reaches the inside. This
  is the Grader's "mass inside, kinetic energy outside" in a form Lean can
  check, and it matches real physics: forces keep a particle's handedness,
  and mass is what flips it.
- **β decay is its Feynman diagram.** A down quark parts into an up quark
  and a W⁻, and the W⁻ parts into an electron and an antineutrino. The W is
  really there in between.
- **Force carriers meet each other.** Two gluons join into a third, as real
  gluons do (the three-gluon vertex). A W⁺ and a W⁻ join into the photon, so
  light can make W pairs. An up quark and an anti-down join into a W⁺, as at
  a particle collider.

## In the shared test suite

Velcro passes `ChargeConserved`, `ChargeCarried`, `BaryonConserved`,
`LeptonConserved`, `ProtonStable`, `BetaDecayAmong`, `Annihilation` (into a
real photon), `MakesFamily 1`, and the prediction tests `TwinFlipsHand`,
`VectorlikeCharge`, `OneFamilyCharges`, `ThirdsComeInThrees` and
`TwinIsAnti`.

It also passes the new force-carrier tests, added to `main` before Velcro was
proved against them: `AnnihilatesToLight` (e⁻ e⁺ → γ γ), `BetaDecayViaW`,
and `MakesBoson` for the photon, the gluon, the W⁺, the W⁻ and the Higgs.

It provably fails two tests:

- **`MakesBoson .z`.** The empty container stands for every neutral force
  carrier at once (the photon, the Z, and the two gluons that change no
  colour), since none of them changes any slot. Velcro reads it as the
  photon, so a world never holds a Z.
- **`BetaDecay`.** The vacuum makes things only with their twins, so no
  world holds a lone down quark (as in Penta and Ladder).

## What it does not do yet

- **No strengths.** Velcro says which joins and parts can happen, never how
  likely they are. In nature the photon touches only charged things, but
  since adding 0 changes nothing, Velcro's empty container joins anything,
  even a neutrino or another photon. In this model, a coupling's strength is
  invisible.
- **The force carriers are listed, not derived.** They are the steps nature
  uses. Velcro doesn't say why there's no step that flips the root alone, or
  a W that flips the root and the hand in opposite directions.
- **One family only,** as before. The Grader's other idea, families as
  containers 0ⁿ of different sizes, is still open.
- **Colour is conserved but not confined,** and there are no masses, rates
  or clock, as in Penta and Ladder.
