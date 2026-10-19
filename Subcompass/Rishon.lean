import Subcompass.OSM

/-!
# Rishon: team 0's model, generation 0 (tag `t0g0`)

Rishon is OSM (`Subcompass/OSM.lean`, copied unchanged from the `baseline`
branch) with one rule added and one way of reading the result. The plain-words
version is `Rishon.md`.

## The added rule

**The vacuum lends pairs.** Besides × and +, there is one more event, `pair`:
a ⊕ and a ⊖ appear together, loose in the bag. Points are no longer fixed;
they can only be made in opposite pairs, so the total of all signs never
changes (proved below as `step_total`). Nothing else in OSM changes.

## The reading: particles are tripods

A *rishon* is a segment, one of OSM's four ordered 1D things. Its first point
is its *root*, its second its *tip*:

| segment | rishon | charge (in thirds of e) | B − L (in thirds) |
| --- | --- | --- | --- |
| [⊕ ⊕] | T  | +1 | +1 |
| [⊕ ⊖] | V  |  0 | −1 |
| [⊖ ⊖] | T̄  | −1 | −1 |
| [⊖ ⊕] | V̄  |  0 | +1 |

Charge = (root + tip) / 2, and B − L = tip. The twin of each rishon (every
sign flipped) is its antirishon, as OSM's twin rule demands.

A *particle* is a tripod: three segments whose roots are brought to one place
by +, and nothing else at that place. OSM's own undoing rule (a place holding
both ⊕ and ⊖ comes apart) forces the three roots to share one sign, so a
particle is all matter (roots ⊕) or all antimatter (roots ⊖). That leaves
exactly 16 kinds, one family of the Standard Model, each with its measured
electric charge and B − L:

* matter:      TTT = e⁺, TTV = u, TVV = d̄, VVV = ν
* antimatter:  T̄T̄T̄ = e⁻, T̄T̄V̄ = ū, T̄V̄V̄ = d, V̄V̄V̄ = ν̄

(counting the three places of the odd rishon in TTV and TVV, as Harari did
for quark colour, gives 1 + 3 + 3 + 1 = 8 of each, 16 in all.)

All of this is integer arithmetic: 6 × charge is the sum of a particle's six
signs, and 3 × (B − L) is the sum of its three tips.

## What is checked below

* `pair` keeps every world allowed, and keeps the total of all signs.
* Every possible tripod with unmixed roots is one of the eight named
  particles, with the Standard Model's charge and B − L (`tripod_is_particle`).
* The twin of a particle is its antiparticle.
* A worked β decay: a lone down quark, with six pairs from the vacuum,
  becomes an up quark, an electron and an antineutrino (`beta_decay`).
-/

namespace Rishon
open OSM

/-! ## 1. The added rule -/

/-- The events: OSM's × and +, plus `pair`, which puts a new ⊕ and ⊖ into the
bag. -/
inductive Event where
  | osm (e : OSM.Event)
  | pair
  deriving DecidableEq, Repr

/-- One event. `pair` adds points 2k (⊕) and 2k + 1 (⊖) after the last point;
they are loose in the bag, touching nothing, so nothing comes apart. -/
def step (w : World) : Event → Option World
  | .osm e => w.step e
  | .pair => some { w with signs := w.signs ++ [.pos, .neg] }

/-- A history: events one after another. -/
def run (w : World) : List Event → Option World
  | [] => some w
  | e :: es =>
    match step w e with
    | none => none
    | some w' => run w' es

/-- Rishon as a filling of OSM's common template for models. -/
def rishon : ArithModel where
  World := World
  Event := Event
  start := World.start
  step := step
  bag w := w.signsOf w.bag
  things w := w.thingSigns

/-! ## 2. The reading: rishons and particles -/

/-- A rishon: a segment's root and tip. -/
abbrev Rish := Sign × Sign

/-- Electric charge of a rishon, in thirds of the electron's charge. -/
def Rish.charge (r : Rish) : Int := (r.1.toInt + r.2.toInt) / 2

/-- B − L of a rishon, in thirds. -/
def Rish.bl (r : Rish) : Int := r.2.toInt

/-- The particles of one Standard Model family. -/
inductive Particle where
  | positron | up | antidown | neutrino
  | electron | antiup | down | antineutrino
  deriving DecidableEq, Repr

namespace Particle

/-- Measured electric charge, in thirds of e (the electron's is −3). -/
def charge : Particle → Int
  | positron => 3 | up => 2 | antidown => 1 | neutrino => 0
  | electron => -3 | antiup => -2 | down => -1 | antineutrino => 0

/-- Baryon number minus lepton number, in thirds (a quark has B = 1/3, an
electron or neutrino L = 1). -/
def bl : Particle → Int
  | positron => 3 | up => 1 | antidown => -1 | neutrino => -3
  | electron => -3 | antiup => -1 | down => 1 | antineutrino => 3

def anti : Particle → Particle
  | positron => electron | up => antiup | antidown => down | neutrino => antineutrino
  | electron => positron | antiup => up | down => antidown | antineutrino => neutrino

end Particle

/-- Which particle a tripod is: counted by its roots' sign and its number of
⊕ tips. `none` if the roots are mixed, which OSM never lets stand. -/
def classify (a b c : Rish) : Option Particle :=
  let tips := [a.2, b.2, c.2].countP (· == .pos)
  match a.1, b.1, c.1 with
  | .pos, .pos, .pos =>
    some (match tips with
      | 3 => .positron | 2 => .up | 1 => .antidown | _ => .neutrino)
  | .neg, .neg, .neg =>
    some (match tips with
      | 3 => .antineutrino | 2 => .down | 1 => .antiup | _ => .electron)
  | _, _, _ => none

/-- The rishon whose root is point `i`: the segment starting at `i`, if any. -/
def rishAt (w : World) (i : Nat) : Option Rish :=
  match w.shape.things.find? (fun t => t.head? == some i), w.signs[i]? with
  | some [_, j], some r => (w.signs[j]?).map fun s => (r, s)
  | _, _ => none

/-- The particles of a world: every place that holds exactly three roots of
segments. -/
def particles (w : World) : List Particle :=
  w.shape.places.filterMap fun g =>
    match g with
    | [i, j, k] =>
      match rishAt w i, rishAt w j, rishAt w k with
      | some a, some b, some c => classify a b c
      | _, _, _ => none
    | _ => none

/-! ## 3. Checks -/

section Checks
open Sign

/-- The rishon table above. -/
example : Rish.charge (pos, pos) = 1 ∧ Rish.charge (pos, neg) = 0 ∧
    Rish.charge (neg, neg) = -1 ∧ Rish.charge (neg, pos) = 0 ∧
    Rish.bl (pos, pos) = 1 ∧ Rish.bl (pos, neg) = -1 ∧
    Rish.bl (neg, neg) = -1 ∧ Rish.bl (neg, pos) = 1 := by decide

/-- Every tripod whose roots share a sign is a particle whose measured charge
and B − L are the sums over its rishons. All 64 cases are checked. -/
theorem tripod_is_particle (a b c : Rish) (p : Particle) (h : classify a b c = some p) :
    p.charge = a.charge + b.charge + c.charge ∧ p.bl = a.bl + b.bl + c.bl := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases c1 <;> cases c2 <;>
    simp [classify] at h <;> subst h <;> decide

/-- A tripod is a particle exactly when its roots share a sign. -/
theorem classify_isSome (a b c : Rish) :
    (classify a b c).isSome = (a.1 == b.1 && b.1 == c.1) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases c1 <;> cases c2 <;> decide

/-- So 6 × charge is the plain sum of a particle's six signs. -/
theorem six_charge (a b c : Rish) (p : Particle) (h : classify a b c = some p) :
    2 * p.charge = a.1.toInt + a.2.toInt + b.1.toInt + b.2.toInt + c.1.toInt + c.2.toInt := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases c1 <;> cases c2 <;>
    simp [classify] at h <;> subst h <;> decide

/-- The twin of a particle (every sign flipped) is its antiparticle. -/
theorem twin_is_anti (a b c : Rish) (p : Particle) (h : classify a b c = some p) :
    classify (a.1.flip, a.2.flip) (b.1.flip, b.2.flip) (c.1.flip, c.2.flip) = some p.anti := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases c1 <;> cases c2 <;>
    simp [classify] at h <;> subst h <;> decide

end Checks

/-! ## 4. The added rule keeps everything OSM proves -/

section Proofs

/-- A world allowed with n points is allowed with more. -/
theorem wf_mono {n m : Nat} {sh : Shape} (hnm : n ≤ m) (h : WF n sh) : WF m sh := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, fun t ht i hi => Nat.lt_of_lt_of_le (h2 t ht i hi) hnm, h3, h4, h5, h6, h7, h8⟩

/-- Every event leaves an allowed world. -/
theorem step_wf {w w' : World} {e : Event} (hw : WF w.signs.length w.shape)
    (h : step w e = some w') : WF w'.signs.length w'.shape := by
  cases e with
  | osm e => exact (step_ok h).1
  | pair =>
    simp only [step, Option.some.injEq] at h
    subst h
    exact wf_mono (by simp) hw

/-- Every event keeps the total of all signs: points are only made in
opposite pairs, so total charge is conserved. -/
theorem step_total {w w' : World} {e : Event} (h : step w e = some w') :
    total w'.signs = total w.signs := by
  cases e with
  | osm e => exact (step_count_and_total h).2
  | pair =>
    simp only [step, Option.some.injEq] at h
    subst h
    simp [total, Sign.toInt]

/-- Every world any history makes from a loose bag is allowed, and has the
starting bag's total. -/
theorem run_ok : ∀ (es : List Event) (w w' : World),
    WF w.signs.length w.shape → run w es = some w' →
    WF w'.signs.length w'.shape ∧ total w'.signs = total w.signs
  | [], w, w', hw, h => by
    simp only [run, Option.some.injEq] at h
    subst h; exact ⟨hw, rfl⟩
  | e :: es, w, w', hw, h => by
    simp only [run] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      obtain ⟨hwf, ht⟩ := run_ok es w₁ w' (step_wf hw h₁) h
      exact ⟨hwf, ht.trans (step_total h₁)⟩

end Proofs

/-! ## 5. Worked example: β decay, d → u + e⁻ + ν̄ -/

section Beta
open Sign

/-- A lone down quark, T̄V̄V̄: segments [0,1] = [⊖⊖], [2,3] and [4,5] = [⊖⊕],
roots 0, 2, 4 brought to one place. -/
def downQuark : Option World :=
  run (World.start [neg, neg, neg, pos, neg, pos])
    [.osm (.bind 0 1), .osm (.bind 2 3), .osm (.bind 4 5), .osm (.join [(0, 2), (0, 4)])]

example : downQuark.map particles = some [.down] := by decide +kernel

/-- The decay. Six pairs come from the vacuum (points 6 to 17, even ⊕, odd ⊖).
One pair is bound into a V stick and its ⊕ root is laid on the quark's ⊖
roots: that place comes apart and every stick involved dissolves into the bag.
The loose points are then bound and joined into u (TTV), e⁻ (T̄T̄T̄) and
ν̄ (V̄V̄V̄). Charge −1 = 2 − 3 + 0 and B − L 1 = 1 − 3 + 3, in thirds. -/
def betaDecay : List Event :=
  List.replicate 6 .pair ++
  [ .osm (.bind 6 7), .osm (.join [(6, 0)]),
    -- u: [8,10] T, [12,14] T, [16,7] V
    .osm (.bind 8 10), .osm (.bind 12 14), .osm (.bind 16 7),
    .osm (.join [(8, 12), (8, 16)]),
    -- e⁻: [0,1], [2,4], [9,11], all T̄
    .osm (.bind 0 1), .osm (.bind 2 4), .osm (.bind 9 11),
    .osm (.join [(0, 2), (0, 9)]),
    -- ν̄: [13,3], [15,5], [17,6], all V̄
    .osm (.bind 13 3), .osm (.bind 15 5), .osm (.bind 17 6),
    .osm (.join [(13, 15), (13, 17)]) ]

theorem beta_decay :
    (downQuark.bind fun w => run w betaDecay).map particles
      = some [.up, .electron, .antineutrino] := by decide +kernel

end Beta

/-! ## 6. Audit -/

#print axioms tripod_is_particle
#print axioms classify_isSome
#print axioms six_charge
#print axioms twin_is_anti
#print axioms run_ok
#print axioms beta_decay

end Rishon
