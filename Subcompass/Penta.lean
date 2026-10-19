import Subcompass.Suite

/-!
# Penta: team 1's model, generation 0 (tag `t1g0`)

The plain-words version is `Penta.md`.

## What exists

Points are ⊕ (+1) or ⊖ (−1), as in the baseline. A *particle* is a 4-simplex
(a "5-cell"): five points bound in order, a 4D thing. Its first point is its
*root*, the next three its *tips*, and the last its *hand*: the point added in
the jump from 3D to 4D, on one side or the other of the tetrahedron below it.
Every one of the 2⁵ = 32 such things is a particle, and a world is just the
particles it holds. There are no loose points.

## The readings

* **Charge:** 6 × charge = 3 × root + the three tips. The hand carries none.
* **Handedness:** the baseline's value, the product of all five points.
  ⊖ is left-handed, ⊕ right-handed. A twin flips all five points, an odd
  number, so the twin of a left-handed particle is right-handed.
* **Weak charge:** a particle feels the W boson when its hand agrees with its
  root (`active`). Lean checks below that these are exactly the left-handed
  particles and the right-handed antiparticles (`active_iff`), as in nature.

| root | tips ⊕⊕⊕ | two ⊕ | one ⊕ | ⊖⊖⊖ |
| --- | --- | --- | --- | --- |
| ⊕ | e⁺ | u | d̄ | ν |
| ⊖ | ν̄ | d | ū | e⁻ |

Each comes with either hand, and order counts, so the odd tip's position is a
quark's colour: 2 × 16 = 32 states, one complete family of the Standard Model,
left- and right-handed.

## The four events

* `pair t`: the vacuum makes `t` together with its twin.
* `annihilate t`: `t` and its twin meet and vanish.
* `swap s t`: two particles that both feel the W exchange roots, each hand
  travelling with its root. This is the W boson's work: a down quark becomes
  an up, a neutrino an electron.
* `flip t`: `t`'s hand moves to the other side. This is what a mass does in
  nature: it turns a left-handed electron into a right-handed one.

## What is checked below

* Every particle has its measured charge, and its twin is its antiparticle
  with the opposite hand (`charge6_eq`, `twin_is_anti`, `twin_value`).
* The W touches exactly the left-handed particles and the right-handed
  antiparticles (`active_iff`), and never changes a hand (`swap_value`).
* Every event keeps charge, baryon number and lepton number (`step_charge`,
  `step_baryon`, `step_lepton`).
* β decay; the rest of the shared suite is in `PentaSuite.lean`.
-/

namespace Penta

/-! ## 1. Points -/

/-- A point is ⊕ (`pos`, +1) or ⊖ (`neg`, −1). -/
inductive Sign where
  | pos
  | neg
  deriving DecidableEq, Repr

namespace Sign

def toInt : Sign → Int
  | pos => 1
  | neg => -1

/-- The twin flips ⊕ and ⊖. -/
def flip : Sign → Sign
  | pos => neg
  | neg => pos

/-- Multiplying two values. -/
def mul : Sign → Sign → Sign
  | pos, s => s
  | neg, s => s.flip

end Sign

/-! ## 2. Particles: 4-simplices -/

/-- A 4-simplex: its root, its three tips, and its hand, in order. -/
structure Pent where
  root : Sign
  a : Sign
  b : Sign
  c : Sign
  hand : Sign
  deriving DecidableEq, Repr

namespace Pent

/-- The twin: every sign flipped. -/
def twin (t : Pent) : Pent := ⟨t.root.flip, t.a.flip, t.b.flip, t.c.flip, t.hand.flip⟩

/-- 6 × electric charge (in e): three times the root, plus the tips. -/
def charge6 (t : Pent) : Int := 3 * t.root.toInt + t.a.toInt + t.b.toInt + t.c.toInt

/-- How many tips are ⊕. -/
def up (t : Pent) : Nat := [t.a, t.b, t.c].count .pos

/-- The value, the product of all five points: ⊖ is left-handed, ⊕ right. -/
def value (t : Pent) : Sign := t.root.mul (t.a.mul (t.b.mul (t.c.mul t.hand)))

/-- It feels the W: its hand agrees with its root. -/
def active (t : Pent) : Bool := t.hand == t.root

/-- Take another particle's root and hand. -/
def withWeak (t s : Pent) : Pent := { t with root := s.root, hand := s.hand }

/-- The hand moves to the other side. -/
def flipped (t : Pent) : Pent := { t with hand := t.hand.flip }

end Pent

/-! ## 3. Worlds and events -/

/-- A world: the particles it holds. Their order is bookkeeping. -/
abbrev World := List Pent

inductive Event where
  | pair (t : Pent)
  | annihilate (t : Pent)
  | swap (s t : Pent)
  | flip (t : Pent)
  deriving DecidableEq, Repr

/-- One event; `none` means it can't happen here. -/
def step (w : World) : Event → Option World
  | .pair t => some (t :: t.twin :: w)
  | .annihilate t =>
    if t ∈ w ∧ t.twin ∈ w.erase t then some ((w.erase t).erase t.twin) else none
  | .swap s t =>
    if s ∈ w ∧ t ∈ w.erase s ∧ s.active ∧ t.active then
      some (s.withWeak t :: t.withWeak s :: (w.erase s).erase t)
    else none
  | .flip t => if t ∈ w then some (t.flipped :: w.erase t) else none

/-- A world's total of some quantity, particle by particle. -/
def sumOf (q : Pent → Int) (w : World) : Int := (w.map q).sum

/-- The world's total charge, in sixths of e. -/
def charge (w : World) : Int := sumOf Pent.charge6 w

/-! ## 4. Conservation -/

theorem sumOf_cons (q : Pent → Int) (t : Pent) (w : World) :
    sumOf q (t :: w) = q t + sumOf q w := by simp [sumOf]

/-- Taking out a member leaves the total less that member's share. -/
theorem sumOf_erase (q : Pent → Int) {t : Pent} {w : World} (h : t ∈ w) :
    sumOf q w = q t + sumOf q (w.erase t) := by
  induction w with
  | nil => cases h
  | cons x xs ih =>
    by_cases hx : x = t
    · subst hx; simp [sumOf_cons]
    · have ht : t ∈ xs := (List.mem_cons.mp h).resolve_left (Ne.symm hx)
      rw [List.erase_cons_tail (by simpa using hx), sumOf_cons, sumOf_cons, ih ht]
      omega

/-- A quantity is kept by every event if a twin pair has none of it, an
exchange of roots and hands leaves the pair's total the same, and a hand flip
doesn't change it. -/
theorem step_keeps (q : Pent → Int) (htwin : ∀ t, q t + q t.twin = 0)
    (hswap : ∀ s t, q (s.withWeak t) + q (t.withWeak s) = q s + q t)
    (hflip : ∀ t, q t.flipped = q t)
    {w w' : World} {e : Event} (h : step w e = some w') : sumOf q w' = sumOf q w := by
  cases e with
  | pair t =>
    simp only [step, Option.some.injEq] at h; subst h
    rw [sumOf_cons, sumOf_cons, ← Int.add_assoc, htwin, Int.zero_add]
  | annihilate t =>
    simp only [step] at h
    split at h
    · rename_i hm; cases h
      rw [sumOf_erase q hm.1, sumOf_erase q hm.2, ← Int.add_assoc, htwin, Int.zero_add]
    · cases h
  | swap s t =>
    simp only [step] at h
    split at h
    · rename_i hm; cases h
      rw [sumOf_cons, sumOf_cons, ← Int.add_assoc, hswap,
        sumOf_erase q hm.1, sumOf_erase q hm.2.1, Int.add_assoc]
    · cases h
  | flip t =>
    simp only [step] at h
    split at h
    · rename_i hm; cases h
      rw [sumOf_cons, hflip, sumOf_erase q hm]
    · cases h

/-- Charge is never made or destroyed. -/
theorem step_charge {w w' : World} {e : Event} (h : step w e = some w') :
    charge w' = charge w :=
  step_keeps _ (fun t => by
    obtain ⟨r, a, b, c, h⟩ := t; cases r <;> cases a <;> cases b <;> cases c <;> cases h <;> decide)
    (fun s t => by
      obtain ⟨r, a, b, c, _⟩ := s; obtain ⟨r', _, _, _, _⟩ := t
      cases r <;> cases r' <;> simp [Pent.charge6, Pent.withWeak] <;> omega)
    (fun _ => rfl) h

/-! ## 5. The reading: which particle each 4-simplex is -/

/-- Root and number of ⊕ tips name the particle (the table above); the hand
says which way it turns. -/
def Pent.particle (t : Pent) : Suite.Particle :=
  match t.root, t.up with
  | .pos, 3 => .anti .electron
  | .pos, 2 => .matter .up
  | .pos, 1 => .anti .down
  | .pos, _ => .matter .nuE
  | .neg, 3 => .anti .nuE
  | .neg, 2 => .matter .down
  | .neg, 1 => .anti .up
  | .neg, _ => .matter .electron

/-- The particle doesn't depend on the hand, so a hand flip keeps it. -/
theorem particle_flipped (t : Pent) : t.flipped.particle = t.particle := rfl

/-- Matter, not antimatter. -/
def isMatter : Suite.Particle → Bool
  | .matter _ => true
  | _ => false

/-- All 32 four-simplices, every one a particle. -/
def Pent.all : List Pent :=
  let ss := [Sign.pos, Sign.neg]
  ss.flatMap fun r => ss.flatMap fun a => ss.flatMap fun b => ss.flatMap fun c =>
    ss.map fun h => ⟨r, a, b, c, h⟩

/-- Every particle has the measured charge: 6 × charge = 3 × root + tips. -/
theorem charge6_eq (t : Pent) : t.charge6 = 2 * t.particle.charge3 := by
  obtain ⟨r, a, b, c, h⟩ := t
  cases r <;> cases a <;> cases b <;> cases c <;> cases h <;> decide

/-- The twin of a particle is its antiparticle. -/
theorem twin_is_anti (t : Pent) : t.twin.particle = t.particle.antiOf := by
  obtain ⟨r, a, b, c, h⟩ := t
  cases r <;> cases a <;> cases b <;> cases c <;> cases h <;> decide

/-- ...with the opposite hand: five points is an odd number. -/
theorem twin_value (t : Pent) : t.twin.value = t.value.flip := by
  obtain ⟨r, a, b, c, h⟩ := t
  cases r <;> cases a <;> cases b <;> cases c <;> cases h <;> decide

/-- The W touches exactly the left-handed particles and the right-handed
antiparticles, as in nature. -/
theorem active_iff (t : Pent) :
    t.active = (t.value == .neg && isMatter t.particle || t.value == .pos && !isMatter t.particle) := by
  obtain ⟨r, a, b, c, h⟩ := t
  cases r <;> cases a <;> cases b <;> cases c <;> cases h <;> decide

/-- The W never changes a hand: a particle that feels it takes on a root and
hand that agree, as its own did. -/
theorem swap_value (s : Pent) (r : Sign) (hs : s.active) :
    { s with root := r, hand := r }.value = s.value := by
  obtain ⟨r₀, a, b, c, h⟩ := s
  revert hs
  cases r <;> cases r₀ <;> cases a <;> cases b <;> cases c <;> cases h <;> decide

/-- One family, both hands: each lepton twice, each quark six times (three
colours, two hands). -/
example : (Pent.all.map Pent.particle).count (.matter .up) = 6 ∧
    (Pent.all.map Pent.particle).count (.matter .down) = 6 ∧
    (Pent.all.map Pent.particle).count (.matter .electron) = 2 ∧
    (Pent.all.map Pent.particle).count (.matter .nuE) = 2 := by decide

/-- Baryon number is never made or destroyed. -/
theorem step_baryon {w w' : World} {e : Event} (h : step w e = some w') :
    sumOf (fun t => t.particle.baryon3) w' = sumOf (fun t => t.particle.baryon3) w :=
  step_keeps _ (fun t => by
    obtain ⟨r, a, b, c, h⟩ := t; cases r <;> cases a <;> cases b <;> cases c <;> cases h <;> decide)
    (fun s t => by
      obtain ⟨r, a, b, c, _⟩ := s; obtain ⟨r', a', b', c', _⟩ := t
      cases r <;> cases r' <;> cases a <;> cases b <;> cases c <;>
        cases a' <;> cases b' <;> cases c' <;> rfl)
    (fun _ => rfl) h

/-- Lepton number is never made or destroyed. -/
theorem step_lepton {w w' : World} {e : Event} (h : step w e = some w') :
    sumOf (fun t => t.particle.lepton) w' = sumOf (fun t => t.particle.lepton) w :=
  step_keeps _ (fun t => by
    obtain ⟨r, a, b, c, h⟩ := t; cases r <;> cases a <;> cases b <;> cases c <;> cases h <;> decide)
    (fun s t => by
      obtain ⟨r, a, b, c, _⟩ := s; obtain ⟨r', a', b', c', _⟩ := t
      cases r <;> cases r' <;> cases a <;> cases b <;> cases c <;>
        cases a' <;> cases b' <;> cases c' <;> rfl)
    (fun _ => rfl) h

/-! ## 6. Worked example: β decay, d → u + e⁻ + ν̄ -/

section Beta
open Sign

/-- A left-handed down quark: root ⊖, tips ⊖ ⊕ ⊕, hand ⊖. -/
def down : Pent := ⟨neg, neg, pos, pos, neg⟩
/-- A left-handed neutrino: root ⊕, tips ⊖ ⊖ ⊖, hand ⊕. -/
def nu : Pent := ⟨pos, neg, neg, neg, pos⟩

example : down.value = .neg ∧ nu.value = .neg := by decide

/-- The vacuum lends a neutrino and an antineutrino; the down quark swaps
roots with the neutrino. The down becomes a left-handed up (same colour), the
neutrino a left-handed electron, and the antineutrino is left over. -/
example : (List.foldlM step [down] [Event.pair nu, Event.swap down nu]).map
      (·.map fun t => (t.particle, t.value))
    = some [(.matter .up, .neg), (.matter .electron, .neg), (.anti .nuE, .pos)] := by decide

/-- A right-handed down quark can't do it: the W doesn't touch it. -/
example : List.foldlM step [down.flipped] [Event.pair nu, Event.swap down.flipped nu]
    = none := by decide

end Beta

/-! ## 7. Audit -/

#print axioms charge6_eq
#print axioms twin_is_anti
#print axioms twin_value
#print axioms active_iff
#print axioms swap_value
#print axioms step_charge
#print axioms step_baryon
#print axioms step_lepton

end Penta
