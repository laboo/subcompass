import Subcompass.Suite

/-!
# Tetra: team 1's model, generation 0 (tag `t1g0`)

The plain-words version is `Tetra.md`.

## What exists

Points are ⊕ (+1) or ⊖ (−1), as in the baseline. A *particle* is a
tetrahedron: four points bound in order, a 3D thing whose edges are lines and
whose faces are planes. Its first point is its *root*, the other three its
*tips*. Every one of the 2⁴ = 16 tetrahedra is a particle, and a world is just
the tetrahedra it holds. There are no loose points.

## The three events

* `pair t`: the vacuum makes tetrahedron `t` together with its twin (every
  sign flipped).
* `annihilate t`: `t` and its twin meet and vanish, back to the vacuum.
* `swap s t`: two tetrahedra exchange roots. In nature this is the W boson's
  work: it turns a down quark into an up and an electron into a neutrino.

## The reading

6 × charge = 3 × root + the three tips, all ±1. The root is twice the
particle's right-handed isospin and the tips add up to 3 × (B − L), so this
is the physicists' Q = T₃ + (B − L)/2 written in whole numbers.

| root | tips ⊕⊕⊕ | two ⊕ | one ⊕ | ⊖⊖⊖ |
| --- | --- | --- | --- | --- |
| ⊕ | e⁺ | u | d̄ | ν |
| ⊖ | ν̄ | d | ū | e⁻ |

Order counts, so the odd tip's position (first, second or third) is a quark's
colour: 1 + 3 + 3 + 1 = 8 states for each root, 16 in all, which is one
family of the Standard Model.

## What is checked below

* Every tetrahedron is a particle with the measured charge, and its twin is
  its antiparticle (`charge6_eq`, `twin_is_anti`).
* Every event keeps the total charge (`step_charge`); since there are no
  loose points, all of it is carried by particles.
* Every event keeps baryon number and lepton number (`step_baryon`,
  `step_lepton`): swaps never touch tips.
* β decay and the rest of the shared suite: see `TetraSuite.lean`.
-/

namespace Tetra

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

end Sign

/-! ## 2. Particles: tetrahedra -/

/-- A tetrahedron: its root, then its three tips, in order. -/
structure Tet where
  root : Sign
  a : Sign
  b : Sign
  c : Sign
  deriving DecidableEq, Repr

namespace Tet

/-- The twin: every sign flipped. -/
def twin (t : Tet) : Tet := ⟨t.root.flip, t.a.flip, t.b.flip, t.c.flip⟩

/-- 6 × electric charge (in e): three times the root, plus the tips. -/
def charge6 (t : Tet) : Int := 3 * t.root.toInt + t.a.toInt + t.b.toInt + t.c.toInt

/-- How many tips are ⊕. -/
def up (t : Tet) : Nat := [t.a, t.b, t.c].count .pos

/-- Exchange roots with another tetrahedron. -/
def withRoot (t : Tet) (r : Sign) : Tet := { t with root := r }

theorem twin_twin (t : Tet) : t.twin.twin = t := by
  obtain ⟨r, a, b, c⟩ := t; cases r <;> cases a <;> cases b <;> cases c <;> rfl

theorem twin_ne (t : Tet) : t.twin ≠ t := by
  obtain ⟨r, a, b, c⟩ := t; cases r <;> cases a <;> cases b <;> cases c <;> decide

end Tet

/-! ## 3. Worlds and events -/

/-- A world: the tetrahedra it holds. Their order is bookkeeping. -/
abbrev World := List Tet

inductive Event where
  | pair (t : Tet)
  | annihilate (t : Tet)
  | swap (s t : Tet)
  deriving DecidableEq, Repr

/-- One event; `none` means it can't happen here. -/
def step (w : World) : Event → Option World
  | .pair t => some (t :: t.twin :: w)
  | .annihilate t =>
    if t ∈ w ∧ t.twin ∈ w.erase t then some ((w.erase t).erase t.twin) else none
  | .swap s t =>
    if s ∈ w ∧ t ∈ w.erase s then
      some (s.withRoot t.root :: t.withRoot s.root :: (w.erase s).erase t)
    else none

/-- A world's total of some quantity, tetrahedron by tetrahedron. -/
def sumOf (q : Tet → Int) (w : World) : Int := (w.map q).sum

/-- The world's total charge, in sixths of e. -/
def charge (w : World) : Int := sumOf Tet.charge6 w

/-! ## 4. Conservation -/

theorem sumOf_cons (q : Tet → Int) (t : Tet) (w : World) :
    sumOf q (t :: w) = q t + sumOf q w := by simp [sumOf]

/-- Taking out a member leaves the total less that member's share. -/
theorem sumOf_erase (q : Tet → Int) {t : Tet} {w : World} (h : t ∈ w) :
    sumOf q w = q t + sumOf q (w.erase t) := by
  induction w with
  | nil => cases h
  | cons x xs ih =>
    by_cases hx : x = t
    · subst hx; simp [sumOf_cons]
    · have ht : t ∈ xs := (List.mem_cons.mp h).resolve_left (Ne.symm hx)
      rw [List.erase_cons_tail (by simpa using hx), sumOf_cons, sumOf_cons, ih ht]
      omega

/-- A quantity is kept by every event if a twin pair has none of it and a
root exchange leaves the pair's total the same. -/
theorem step_keeps (q : Tet → Int) (htwin : ∀ t, q t + q t.twin = 0)
    (hswap : ∀ s t, q (s.withRoot t.root) + q (t.withRoot s.root) = q s + q t)
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
        sumOf_erase q hm.1, sumOf_erase q hm.2, Int.add_assoc]
    · cases h

/-- Charge is never made or destroyed. -/
theorem step_charge {w w' : World} {e : Event} (h : step w e = some w') :
    charge w' = charge w :=
  step_keeps _
    (fun t => by obtain ⟨r, a, b, c⟩ := t; cases r <;> cases a <;> cases b <;> cases c <;> decide)
    (fun s t => by
      obtain ⟨r, a, b, c⟩ := s; obtain ⟨r', _, _, _⟩ := t
      cases r <;> cases r' <;> simp [Tet.charge6, Tet.withRoot] <;> omega)
    h

/-! ## 5. The reading: which particle each tetrahedron is -/

open Suite in
/-- Root and number of ⊕ tips name the particle (the table above). -/
def Tet.particle (t : Tet) : Suite.Particle :=
  match t.root, t.up with
  | .pos, 3 => .anti .electron
  | .pos, 2 => .matter .up
  | .pos, 1 => .anti .down
  | .pos, _ => .matter .nuE
  | .neg, 3 => .anti .nuE
  | .neg, 2 => .matter .down
  | .neg, 1 => .anti .up
  | .neg, _ => .matter .electron

/-- All 16 tetrahedra, every one a particle. -/
def Tet.all : List Tet :=
  let ss := [Sign.pos, Sign.neg]
  ss.flatMap fun r => ss.flatMap fun a => ss.flatMap fun b => ss.map fun c => ⟨r, a, b, c⟩

/-- Every tetrahedron has the measured charge: 6 × charge = 3 × root + tips. -/
theorem charge6_eq (t : Tet) : t.charge6 = 2 * t.particle.charge3 := by
  obtain ⟨r, a, b, c⟩ := t; cases r <;> cases a <;> cases b <;> cases c <;> decide

/-- The twin of a particle is its antiparticle. -/
theorem twin_is_anti (t : Tet) : t.twin.particle = t.particle.antiOf := by
  obtain ⟨r, a, b, c⟩ := t; cases r <;> cases a <;> cases b <;> cases c <;> decide

/-- The tips add up to 3 × (B − L), in the suite's units. -/
theorem tips_eq (t : Tet) :
    t.a.toInt + t.b.toInt + t.c.toInt = t.particle.baryon3 - 3 * t.particle.lepton := by
  obtain ⟨r, a, b, c⟩ := t; cases r <;> cases a <;> cases b <;> cases c <;> decide

/-- Each particle state appears in one way only for leptons and in three ways
(the colours) for quarks: 1 + 3 + 3 + 1 for each root. -/
example : (Tet.all.map Tet.particle).count (.matter .up) = 3 ∧
    (Tet.all.map Tet.particle).count (.matter .down) = 3 ∧
    (Tet.all.map Tet.particle).count (.matter .electron) = 1 ∧
    (Tet.all.map Tet.particle).count (.matter .nuE) = 1 := by decide

/-- Baryon number is never made or destroyed. -/
theorem step_baryon {w w' : World} {e : Event} (h : step w e = some w') :
    sumOf (fun t => t.particle.baryon3) w' = sumOf (fun t => t.particle.baryon3) w :=
  step_keeps _
    (fun t => by obtain ⟨r, a, b, c⟩ := t; cases r <;> cases a <;> cases b <;> cases c <;> decide)
    (fun s t => by
      obtain ⟨r, a, b, c⟩ := s; obtain ⟨r', a', b', c'⟩ := t
      cases r <;> cases r' <;> cases a <;> cases b <;> cases c <;>
        cases a' <;> cases b' <;> cases c' <;> decide)
    h

/-- Lepton number is never made or destroyed. -/
theorem step_lepton {w w' : World} {e : Event} (h : step w e = some w') :
    sumOf (fun t => t.particle.lepton) w' = sumOf (fun t => t.particle.lepton) w :=
  step_keeps _
    (fun t => by obtain ⟨r, a, b, c⟩ := t; cases r <;> cases a <;> cases b <;> cases c <;> decide)
    (fun s t => by
      obtain ⟨r, a, b, c⟩ := s; obtain ⟨r', a', b', c'⟩ := t
      cases r <;> cases r' <;> cases a <;> cases b <;> cases c <;>
        cases a' <;> cases b' <;> cases c' <;> decide)
    h

/-! ## 6. Worked example: β decay, d → u + e⁻ + ν̄ -/

section Beta
open Sign

/-- A down quark: root ⊖, tips ⊖ ⊕ ⊕. -/
def down : Tet := ⟨neg, neg, pos, pos⟩
/-- A neutrino: root ⊕, tips ⊖ ⊖ ⊖. -/
def nu : Tet := ⟨pos, neg, neg, neg⟩

/-- The vacuum lends a neutrino and an antineutrino; the down quark swaps
roots with the neutrino. The down becomes an up (same colour), the neutrino
an electron, and the antineutrino is left over. -/
example : (List.foldlM step [down] [Event.pair nu, Event.swap down nu]).map (·.map Tet.particle)
    = some [.matter .up, .matter .electron, .anti .nuE] := by decide

end Beta

/-! ## 7. Audit -/

#print axioms charge6_eq
#print axioms twin_is_anti
#print axioms step_charge
#print axioms step_baryon
#print axioms step_lepton

end Tetra
