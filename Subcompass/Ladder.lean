import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Subcompass.Suite

/-!
# Ladder: team 2's model, generation 0 (tag `t2g0`)

The plain-words version is `Ladder.md`.

Team 1's Penta is a particle for 3D space. Ladder is the same kind of
particle on every rung of the dimension ladder, plus the one exchange Penta
lacked: colour.

## What exists

Points are ⊕ (+1) or ⊖ (−1), as in the baseline. In space of dimension `d`,
a *particle* is a (d+1)-simplex: a *root*, `d` *tips* (one per direction of
space), and a *hand*, the point added in the jump to the next dimension. A
world is just the particles it holds; there are no loose points.

## The readings

* **Charge:** each of the `d` edges at the root adds its two ends, and
  2d × charge is the total. At `d = 3` that is Penta's
  6 × charge = 3 × root + tips.
* **Hand:** the baseline's value, the product of all `d + 2` points:
  −1 is left-handed, +1 right-handed.
* **Colour:** the places of a quark's odd tips.
* **Weak charge:** a particle feels the W when its hand agrees with its root.

## The five events

Penta's four, `pair`, `annihilate`, `swap` (the W) and `flip` (mass), and one
more:

* `twist s t i j`: two particles both swap their tips at places `i` and `j`,
  when their tips at `i` add up to the same as at `j`. This is a gluon's
  work: it moves colour along an edge between tips, and keeps the world's
  total at every place. A red and a green quark can trade colours; a quark
  and its antiquark can change colour together; no quark can change colour
  alone.

## What is checked below, for every dimension `d`

* Every event keeps charge, and the world's total at each tip place
  (`step_charge`, `step_colour`).
* Charges come in steps of e/d (`charge_eq`), the smallest, ±e/d, comes in
  exactly `d` colours (`colours`), and any charge m/d comes in a number of
  kinds that `d` divides `m` times (`colour_count`): charge with denominator
  `q` always comes in a multiple of `q` kinds (`denominator_dvd`). At `d = 3` this is "thirds
  come in threes"; nothing chose three.
* The twin's hand is `(−1)^d` times the hand (`twin_value`), so twins have
  opposite hands exactly when `d` is odd, that is when spacetime, `d + 1`,
  has an even number of dimensions (`twin_flips_hand_iff`).

The particle names, β decay and the shared suite are for `d = 3`, in
`LadderSuite.lean`.
-/

open Finset

namespace Ladder

/-! ## 1. Points -/

/-- A point is ⊕ (`pos`, +1) or ⊖ (`neg`, −1). -/
inductive Sign where
  | pos
  | neg
  deriving DecidableEq, Repr

instance : Fintype Sign := ⟨{.pos, .neg}, fun s => by cases s <;> simp⟩

namespace Sign

def toInt : Sign → Int
  | pos => 1
  | neg => -1

/-- The twin flips ⊕ and ⊖. -/
def flip : Sign → Sign
  | pos => neg
  | neg => pos

@[simp] theorem toInt_flip (s : Sign) : s.flip.toInt = -s.toInt := by cases s <;> rfl

theorem toInt_eq (s : Sign) : s.toInt = 1 - 2 * (if s = neg then 1 else 0) := by
  cases s <;> rfl

theorem toInt_ne_zero (s : Sign) : s.toInt ≠ 0 := by cases s <;> decide

end Sign

/-! ## 2. Particles: (d+1)-simplices -/

/-- A particle in space of dimension `d`: its root, its `d` tips, its hand. -/
structure Simplex (d : Nat) where
  root : Sign
  tip : Fin d → Sign
  hand : Sign

namespace Simplex

variable {d : Nat}

instance : DecidableEq (Simplex d) := fun s t =>
  decidable_of_iff (s.root = t.root ∧ s.tip = t.tip ∧ s.hand = t.hand) (by
    cases s; cases t; simp)

def equiv (d : Nat) : Simplex d ≃ Sign × (Fin d → Sign) × Sign where
  toFun t := (t.root, t.tip, t.hand)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (Simplex d) := Fintype.ofEquiv _ (equiv d).symm

/-- The twin: every sign flipped. -/
def twin (t : Simplex d) : Simplex d := ⟨t.root.flip, fun i => (t.tip i).flip, t.hand.flip⟩

/-- 2d × electric charge (in e): each edge at the root adds its two ends. -/
def charge (t : Simplex d) : Int := ∑ i, (t.root.toInt + (t.tip i).toInt)

/-- The value, the product of all `d + 2` points: −1 is left-handed, +1 right. -/
def value (t : Simplex d) : Int := t.root.toInt * (∏ i, (t.tip i).toInt) * t.hand.toInt

/-- How many tips are ⊖. -/
def negs (t : Simplex d) : Nat := (univ.filter fun i => t.tip i = .neg).card

/-- It feels the W: its hand agrees with its root. -/
def active (t : Simplex d) : Bool := t.hand == t.root

/-- Take another particle's root and hand. -/
def withWeak (t s : Simplex d) : Simplex d := { t with root := s.root, hand := s.hand }

/-- The hand moves to the other side. -/
def flipped (t : Simplex d) : Simplex d := { t with hand := t.hand.flip }

/-- The tips at places `i` and `j` trade places. -/
def twisted (t : Simplex d) (i j : Fin d) : Simplex d := { t with tip := t.tip ∘ Equiv.swap i j }

/-- `s` and `t` can twist at `i` and `j`: their tips at `i` add up to the
same as at `j`, so the world's total at each place stays the same. -/
def glues (s t : Simplex d) (i j : Fin d) : Bool :=
  (s.tip i).toInt + (t.tip i).toInt == (s.tip j).toInt + (t.tip j).toInt

end Simplex

/-! ## 3. Worlds and events -/

/-- A world: the particles it holds. Their order is bookkeeping. -/
abbrev World (d : Nat) := List (Simplex d)

inductive Event (d : Nat) where
  | pair (t : Simplex d)
  | annihilate (t : Simplex d)
  | swap (s t : Simplex d)
  | flip (t : Simplex d)
  | twist (s t : Simplex d) (i j : Fin d)
  deriving DecidableEq

variable {d : Nat}

/-- One event; `none` means it can't happen here. -/
def step (w : World d) : Event d → Option (World d)
  | .pair t => some (t :: t.twin :: w)
  | .annihilate t =>
    if t ∈ w ∧ t.twin ∈ w.erase t then some ((w.erase t).erase t.twin) else none
  | .swap s t =>
    if s ∈ w ∧ t ∈ w.erase s ∧ s.active ∧ t.active then
      some (s.withWeak t :: t.withWeak s :: (w.erase s).erase t)
    else none
  | .flip t => if t ∈ w then some (t.flipped :: w.erase t) else none
  | .twist s t i j =>
    if s ∈ w ∧ t ∈ w.erase s ∧ s.glues t i j then
      some (s.twisted i j :: t.twisted i j :: (w.erase s).erase t)
    else none

/-- A world's total of some quantity, particle by particle. -/
def sumOf (q : Simplex d → Int) (w : World d) : Int := (w.map q).sum

/-- The world's total charge, in units of e/(2d). -/
def charge (w : World d) : Int := sumOf Simplex.charge w

/-! ## 4. Conservation -/

theorem sumOf_cons (q : Simplex d → Int) (t : Simplex d) (w : World d) :
    sumOf q (t :: w) = q t + sumOf q w := by simp [sumOf]

/-- Taking out a member leaves the total less that member's share. -/
theorem sumOf_erase (q : Simplex d → Int) {t : Simplex d} {w : World d} (h : t ∈ w) :
    sumOf q w = q t + sumOf q (w.erase t) := by
  induction w with
  | nil => cases h
  | cons x xs ih =>
    by_cases hx : x = t
    · subst hx; simp [sumOf_cons]
    · have ht : t ∈ xs := (List.mem_cons.mp h).resolve_left (Ne.symm hx)
      rw [List.erase_cons_tail (by simpa using hx), sumOf_cons, sumOf_cons, ih ht]
      omega

/-- A quantity is kept by every event if a twin pair has none of it, and a
swap, a flip and a twist each leave the total of what they touch the same. -/
theorem step_keeps (q : Simplex d → Int) (htwin : ∀ t, q t + q t.twin = 0)
    (hswap : ∀ s t, q (s.withWeak t) + q (t.withWeak s) = q s + q t)
    (hflip : ∀ t, q t.flipped = q t)
    (htwist : ∀ s t i j, s.glues t i j = true →
      q (s.twisted i j) + q (t.twisted i j) = q s + q t)
    {w w' : World d} {e : Event d} (h : step w e = some w') : sumOf q w' = sumOf q w := by
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
  | twist s t i j =>
    simp only [step] at h
    split at h
    · rename_i hm; cases h
      rw [sumOf_cons, sumOf_cons, ← Int.add_assoc, htwist s t i j hm.2.2,
        sumOf_erase q hm.1, sumOf_erase q hm.2.1, Int.add_assoc]
    · cases h

theorem Simplex.charge_twisted (t : Simplex d) (i j : Fin d) :
    (t.twisted i j).charge = t.charge :=
  Equiv.sum_comp (Equiv.swap i j) (fun k => t.root.toInt + (t.tip k).toInt)

/-- Charge is never made or destroyed, in any dimension. -/
theorem step_charge {w w' : World d} {e : Event d} (h : step w e = some w') :
    charge w' = charge w :=
  step_keeps _
    (fun t => by
      simp only [Simplex.charge, Simplex.twin, Sign.toInt_flip, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun _ _ => by ring)
    (fun s t => by
      simp only [Simplex.charge, Simplex.withWeak, Finset.sum_add_distrib]; ring)
    (fun _ => rfl)
    (fun s t i j _ => by rw [Simplex.charge_twisted, Simplex.charge_twisted])
    h

/-- Colour is never made or destroyed: the world's total at each tip place
stays the same. -/
theorem step_colour (p : Fin d) {w w' : World d} {e : Event d} (h : step w e = some w') :
    sumOf (fun t => (t.tip p).toInt) w' = sumOf (fun t => (t.tip p).toInt) w :=
  step_keeps _ (fun t => by simp [Simplex.twin]) (fun _ _ => rfl) (fun _ => rfl)
    (fun s t i j hg => by
      simp only [Simplex.glues, beq_iff_eq] at hg
      simp only [Simplex.twisted, Function.comp, Equiv.swap_apply_def]
      split_ifs with h₁ h₂
      · subst h₁; exact hg.symm
      · subst h₂; exact hg
      · rfl)
    h

/-! ## 5. Charge comes in steps of e/d, and colour with it -/

namespace Simplex

theorem sum_tip (t : Simplex d) : ∑ i, (t.tip i).toInt = d - 2 * t.negs := by
  simp only [negs, Finset.card_filter, Sign.toInt_eq, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  push_cast; ring

/-- 2d × charge = d × (root + 1) − 2 × (number of ⊖ tips): charge is always a
whole number of e/d. -/
theorem charge_eq (t : Simplex d) : t.charge = d * (t.root.toInt + 1) - 2 * t.negs := by
  rw [charge, Finset.sum_add_distrib, sum_tip]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Simplex

/-- The number of ways to make `k` of the `d` tips ⊖ is `d choose k`. -/
theorem card_negs (k : Nat) :
    (univ.filter fun f : Fin d → Sign => (univ.filter fun i => f i = .neg).card = k).card =
      d.choose k := by
  have := Finset.card_powersetCard k (univ : Finset (Fin d))
  rw [Finset.card_univ, Fintype.card_fin] at this
  rw [← this]
  apply Finset.card_nbij' (fun f => univ.filter fun i => f i = .neg)
    (fun s i => if i ∈ s then .neg else .pos)
  · intro f hf
    rw [Finset.mem_coe] at hf ⊢
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (Finset.mem_filter.mp hf).2⟩
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    convert hs.2 using 2
    ext i; by_cases hi : i ∈ s <;> simp [hi]
  · intro f _; funext i; cases h : f i <;> simp [h]
  · intro s _; ext i; by_cases hi : i ∈ s <;> simp [hi]

/-- The smallest charge, −e/d (a down-like quark: root ⊖, one tip ⊖), comes
in exactly `d` colours, for either hand. -/
theorem colours (h : Sign) :
    (univ.filter fun f : Fin d → Sign => (⟨.neg, f, h⟩ : Simplex d).charge = -2).card = d := by
  have : (univ.filter fun f : Fin d → Sign => (⟨.neg, f, h⟩ : Simplex d).charge = -2) =
      univ.filter fun f : Fin d → Sign => (univ.filter fun i => f i = .neg).card = 1 := by
    apply Finset.filter_congr
    intro f _
    rw [Simplex.charge_eq]
    simp only [Sign.toInt, Simplex.negs]
    omega
  rw [this, card_negs, Nat.choose_one_right]

/-- `k × (d choose k)` is a multiple of `d`. -/
theorem dvd_mul_choose (d k : Nat) : d ∣ k * d.choose k := by
  rcases d with _ | n
  · rcases k with _ | k <;> simp
  · rcases k with _ | k
    · simp
    · exact ⟨n.choose k, by rw [Nat.add_one_mul_choose_eq]; ring⟩

/-- Any charge m e/d, for a given root and hand, comes in a number of kinds
that `d` divides `m` times. So if the charge, in lowest terms, has
denominator `q`, the number of kinds is a multiple of `q`: fractional charge
always comes with colour. -/
theorem colour_count (r h : Sign) (m : Int) :
    (d : Int) ∣ m * (univ.filter fun f : Fin d → Sign =>
      (⟨r, f, h⟩ : Simplex d).charge = 2 * m).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => (univ.filter fun i => f i = Sign.neg).card)
    (t := range (d + 1))
    (fun f _ => Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))))]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.dvd_sum
  intro k hk
  rw [Finset.filter_filter]
  by_cases hc : (d : Int) * (r.toInt + 1) - 2 * k = 2 * m
  · rw [Finset.filter_congr (q := fun f : Fin d → Sign => (univ.filter fun i => f i = .neg).card = k)
      (fun f _ => by
        rw [Simplex.charge_eq]; simp only [Simplex.negs]
        constructor
        · exact fun h => h.2
        · intro h; subst h; exact ⟨hc, rfl⟩),
      card_negs]
    have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    cases r
    · have hm : m = ((d - k : Nat) : Int) := by simp only [Sign.toInt] at hc; push_cast [hkd]; omega
      rw [hm, ← Nat.choose_symm hkd]; exact_mod_cast dvd_mul_choose d (d - k)
    · have hm : m = -(k : Int) := by simp only [Sign.toInt] at hc; omega
      rw [hm, neg_mul]; exact dvd_neg.mpr (by exact_mod_cast dvd_mul_choose d k)
  · rw [Finset.filter_false_of_mem (fun f _ => by
      rw [Simplex.charge_eq]; simp only [Simplex.negs]
      rintro ⟨h₁, rfl⟩; exact hc h₁)]
    simp

theorem div_gcd_dvd {d a n : Nat} (hd : 0 < d) (h : d ∣ a * n) : d / d.gcd a ∣ n := by
  have hg : 0 < d.gcd a := Nat.gcd_pos_of_pos_left a hd
  have hc := Nat.coprime_div_gcd_div_gcd hg
  have hdg : d = d.gcd a * (d / d.gcd a) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left d a)).symm
  have hag : a = d.gcd a * (a / d.gcd a) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right d a)).symm
  have h' : d / d.gcd a ∣ a / d.gcd a * n := by
    apply Nat.dvd_of_mul_dvd_mul_left hg
    rw [← hdg, ← Nat.mul_assoc, ← hag]; exact h
  exact hc.dvd_of_dvd_mul_left h'

/-- The same in lowest terms: a charge m e/d whose denominator, in lowest
terms, is `q = d / gcd(d, m)` comes in a multiple of `q` kinds. -/
theorem denominator_dvd (hd : 0 < d) (r h : Sign) (m : Int) :
    d / d.gcd m.natAbs ∣ (univ.filter fun f : Fin d → Sign =>
      (⟨r, f, h⟩ : Simplex d).charge = 2 * m).card := by
  apply div_gcd_dvd hd
  have := Int.natAbs_dvd_natAbs.mpr (colour_count (d := d) r h m)
  simpa [Int.natAbs_mul] using this

/-! ## 6. Hands: twins have opposite hands exactly in even spacetime -/

namespace Simplex

theorem value_ne_zero (t : Simplex d) : t.value ≠ 0 := by
  simp only [value, ne_eq, mul_eq_zero, not_or]
  exact ⟨⟨t.root.toInt_ne_zero, Finset.prod_ne_zero_iff.mpr fun i _ => (t.tip i).toInt_ne_zero⟩,
    t.hand.toInt_ne_zero⟩

/-- Flipping all `d + 2` points multiplies the hand by `(−1)^d`. -/
theorem twin_value (t : Simplex d) : t.twin.value = (-1) ^ d * t.value := by
  have : ∏ i, -(t.tip i).toInt = (-1) ^ d * ∏ i, (t.tip i).toInt := by
    rw [show (fun i => -(t.tip i).toInt) = fun i => (-1) * (t.tip i).toInt from by funext; ring,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [value, twin, Sign.toInt_flip, this]
  ring

end Simplex

/-- Every twin has the opposite hand exactly when `d` is odd: when spacetime
has an even number of dimensions. -/
theorem twin_flips_hand_iff : (∀ t : Simplex d, t.twin.value = -t.value) ↔ Odd d := by
  constructor
  · intro h
    have h₁ := h ⟨.pos, fun _ => .pos, .pos⟩
    rw [Simplex.twin_value] at h₁
    have : ((-1 : Int) ^ d) = -1 := by
      have := mul_right_cancel₀ (Simplex.value_ne_zero ⟨.pos, fun _ => .pos, .pos⟩)
        (h₁.trans (neg_one_mul _).symm)
      exact this
    exact (neg_one_pow_eq_neg_one_iff_odd (by decide)).mp this
  · intro h t
    rw [Simplex.twin_value, h.neg_one_pow, neg_one_mul]

end Ladder
