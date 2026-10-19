# Rishon (team 0, generation 0, tag `t0g0`)

Rishon is the baseline model, OSM, with one rule added and one way of reading
what it builds. The exact version is `Subcompass/Rishon.lean`; OSM itself is
in `Subcompass/OSM.lean`, copied unchanged from the `baseline` branch.

## OSM in one paragraph

Points are ⊕ (+1) or ⊖ (−1). Multiplication binds points into things: two
make a segment, three a triangle, and so on. Addition brings points of
different things to one place. A place holding both a ⊕ and a ⊖ comes apart
at once: its points come unbound and go back to the loose bag.

## The added rule: the vacuum lends pairs

There is one more event besides × and +: a ⊕ and a ⊖ appear together, loose in
the bag. Points can be made only in such pairs, so the total of all signs never
changes.

## The reading: three sticks make a particle

A segment has a first point, its *root*, and a second, its *tip*. OSM has
exactly four segments, and they are the four *rishons* of Haim Harari's 1979
proposal that electrons, neutrinos and quarks are each made of three smaller
pieces:

| segment | rishon | electric charge | B − L |
| --- | --- | --- | --- |
| [⊕ ⊕] | T  | +⅓ | +⅓ |
| [⊕ ⊖] | V  | 0  | −⅓ |
| [⊖ ⊖] | T̄  | −⅓ | −⅓ |
| [⊖ ⊕] | V̄  | 0  | +⅓ |

Charge is (root + tip) / 2 thirds, and B − L (baryon number minus lepton
number, which the Standard Model conserves exactly) is the tip, in thirds.
Flipping every sign turns each rishon into its antirishon, just as OSM's twin
rule says it should.

A *particle* is three segments with their roots brought to one place, like
three sticks tied at one end. Harari had to add a rule that a particle never
mixes matter and antimatter rishons; here OSM's own rule does it, because roots
of opposite sign at one place come apart. So a particle is all ⊕ roots
(matter) or all ⊖ roots (antimatter), and counting its ⊕ tips names it:

| roots | 3 ⊕ tips | 2 | 1 | 0 |
| --- | --- | --- | --- | --- |
| ⊕ (matter) | TTT = positron (+1) | TTV = up quark (+⅔) | TVV = anti-down (+⅓) | VVV = neutrino (0) |
| ⊖ (antimatter) | V̄V̄V̄ = antineutrino (0) | T̄V̄V̄ = down quark (−⅓) | T̄T̄V̄ = anti-up (−⅔) | T̄T̄T̄ = electron (−1) |

That is one whole family of the Standard Model, every charge right, and every
B − L right too. It is all integer arithmetic: 6 × charge is the sum of a
particle's six points, and 3 × (B − L) is the sum of its three tips. Counting
where the odd stick sits, as Harari did for the three quark colours, gives
1 + 3 + 3 + 1 = 8 kinds of matter and 8 of antimatter.

## A worked decay

A lone down quark (charge −⅓) borrows six pairs from the vacuum. One borrowed
pair makes a V stick, whose ⊕ root is laid on the quark's three ⊖ roots. That
place comes apart, every stick there falls to loose points, and the loose
points are then bound and tied into an up quark (+⅔), an electron (−1) and an
antineutrino (0). This is β decay, the process that powers some radioactivity,
and the charges add up: −⅓ = ⅔ − 1 + 0. Lean runs every step and checks it.

## What is proved

- The added rule keeps every world allowed, and keeps the total of all signs.
- Every tripod with roots of one sign is one of the eight particles named
  above, with the measured charge and B − L; a tripod with mixed roots never
  is.
- The twin of each particle is its antiparticle.
- The β decay above.

## What it does not do yet

Shared with OSM, which Rishon leaves unchanged here:

- It says what can happen, never how often or how fast: there is no clock,
  only an order of events that a setup chooses.
- No forces or force carriers (photon, gluons, W and Z), no mass, no spin.

Rishon's own open gaps, in what it adds (OSM names no particles at all):

- Only the first family: no muon, tau, charm, strange, top or bottom.
- Total charge is conserved, but B − L is not yet: a loose point in the bag is
  neither a root nor a tip.
- Quark colour is only counted, not yet built into the rules.
