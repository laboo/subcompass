import Subcompass.Suite

/-!
# Velcro: team 3's model, generation 0 (tag `t3g0`)

The plain-words version is `Velcro.md`.

Ladder (team 2) and Penta (team 1) make one family of particles from 4-simplices
of signs, and make things happen with rules: a swap does the W's work, a twist
the gluon's, a flip the Higgs'. Velcro keeps their particle and replaces every
rule with one operation, **addition**. The force carriers become things in the
world: each is the difference between two particles.

## What exists

A *thing* has five integer slots, on the five points of a 4-simplex: a *root*,
three *tips* and a *hand*. Only these things may exist:

* **matter:** every slot ⊕ (+1) or ⊖ (−1): the 32 particles of one family, as
  in Penta and Ladder;
* **the photon** `0`: every slot empty. A particle and its twin add up to it,
  and `0 + m = m`: absorbing it changes nothing;
* **the W** `±(2, 0, 0, 0, 2)`: the root and the hand flipped together;
* **the gluons** `+2` on one tip and `−2` on another (six of them);
* **the Higgs** `±(0, 0, 0, 0, 2)`: the hand flipped alone.

## The three events

* `join a b`: two things become one, their sum, if the sum may exist;
* `part c a`: a thing `c` becomes two, `a` and `c − a`, if both may exist;
* `pair a`: nothing becomes `a` and its twin `−a`, since `a + (−a) = 0`.

## What is checked below

* **One law:** no event changes the world's total, slot by slot
  (`step_keeps`, `step_total`). Charge, colour at each place and B − L are
  all sums of slots, so each is kept (`step_charge`, `step_colour`).
* **Baryon and lepton number** are kept too, though neither is a sum of
  slots (`step_baryon`, `step_lepton`).
* **The W touches only left-handed particles and right-handed
  antiparticles,** because adding `±2` to a root and a hand stays within ±1
  only when they agree (`w_iff`). No rule says so.
* **Leptons are colourless:** no gluon can join a lepton (`gluon_quark`).
* **Inside and outside:** the photon, W and gluons never change a particle's
  hand, the product of its points; the Higgs always does (`inside_outside`).
* **Bosons meet bosons:** two gluons join into a third, and a W⁺ and a W⁻
  into the photon (`gluon_gluon`, `w_w`).
-/

namespace Velcro

/-! ## 1. Things -/

/-- Five integer slots on the points of a 4-simplex. -/
@[ext]
structure Thing where
  root : Int
  t₀ : Int
  t₁ : Int
  t₂ : Int
  hand : Int
  deriving DecidableEq, Repr

namespace Thing

instance : Zero Thing := ⟨⟨0, 0, 0, 0, 0⟩⟩
instance : Add Thing := ⟨fun a b => ⟨a.root + b.root, a.t₀ + b.t₀, a.t₁ + b.t₁, a.t₂ + b.t₂, a.hand + b.hand⟩⟩
/-- The twin: every slot's sign flipped. -/
instance : Neg Thing := ⟨fun a => ⟨-a.root, -a.t₀, -a.t₁, -a.t₂, -a.hand⟩⟩
instance : Sub Thing := ⟨fun a b => a + -b⟩

@[simp] theorem add_root (a b : Thing) : (a + b).root = a.root + b.root := rfl
@[simp] theorem add_t₀ (a b : Thing) : (a + b).t₀ = a.t₀ + b.t₀ := rfl
@[simp] theorem add_t₁ (a b : Thing) : (a + b).t₁ = a.t₁ + b.t₁ := rfl
@[simp] theorem add_t₂ (a b : Thing) : (a + b).t₂ = a.t₂ + b.t₂ := rfl
@[simp] theorem add_hand (a b : Thing) : (a + b).hand = a.hand + b.hand := rfl
@[simp] theorem neg_root (a : Thing) : (-a).root = -a.root := rfl
@[simp] theorem neg_t₀ (a : Thing) : (-a).t₀ = -a.t₀ := rfl
@[simp] theorem neg_t₁ (a : Thing) : (-a).t₁ = -a.t₁ := rfl
@[simp] theorem neg_t₂ (a : Thing) : (-a).t₂ = -a.t₂ := rfl
@[simp] theorem neg_hand (a : Thing) : (-a).hand = -a.hand := rfl

theorem add_neg (a : Thing) : a + -a = 0 := by
  ext <;> show _ + -_ = 0 <;> omega

theorem add_sub (c a : Thing) : a + (c - a) = c := by
  ext <;> show _ + (_ + -_) = _ <;> omega

/-- The sum of the three tips: 3 × (baryon number − lepton number). -/
def tips (a : Thing) : Int := a.t₀ + a.t₁ + a.t₂

/-- 6 × electric charge (in e): 3 × root + tips, as in Penta and Ladder. -/
def charge (a : Thing) : Int := 3 * a.root + a.tips

/-- The value, the product of the five points: −1 is left-handed, +1 right. -/
def value (a : Thing) : Int := a.root * a.t₀ * a.t₁ * a.t₂ * a.hand

end Thing

/-- The 32 particles: every slot ⊕ or ⊖. -/
def particles : List Thing :=
  [1, -1].flatMap fun r => [1, -1].flatMap fun a => [1, -1].flatMap fun b =>
    [1, -1].flatMap fun c => [1, -1].map fun h => ⟨r, a, b, c, h⟩

def photon : Thing := 0
def wPlus : Thing := ⟨2, 0, 0, 0, 2⟩
def higgs : Thing := ⟨0, 0, 0, 0, 2⟩
def gluons : List Thing :=
  [⟨0, 2, -2, 0, 0⟩, ⟨0, -2, 2, 0, 0⟩, ⟨0, 2, 0, -2, 0⟩,
   ⟨0, -2, 0, 2, 0⟩, ⟨0, 0, 2, -2, 0⟩, ⟨0, 0, -2, 2, 0⟩]

/-- The force carriers and the Higgs. -/
def carriers : List Thing := [photon, wPlus, -wPlus, higgs, -higgs] ++ gluons

/-- Everything that may exist, as a list. -/
def things : List Thing := particles ++ carriers

/-- A slot of matter: ⊕ or ⊖. -/
def isSign (x : Int) : Bool := x == 1 || x == -1

theorem isSign_iff (x : Int) : isSign x = true ↔ x = 1 ∨ x = -1 := by simp [isSign]

/-- Matter: every slot ⊕ or ⊖. -/
def Thing.isParticle (a : Thing) : Bool :=
  isSign a.root && isSign a.t₀ && isSign a.t₁ && isSign a.t₂ && isSign a.hand

/-- `a` may exist: it is matter or a force carrier. -/
def Thing.ok (a : Thing) : Bool := a.isParticle || carriers.contains a

/-- The list holds exactly what may exist. -/
theorem ok_of_mem : ∀ a ∈ things, a.ok = true := by decide

theorem neg_carriers : ∀ a ∈ carriers, -a ∈ carriers := by decide

/-- The twin of anything that may exist may exist too. -/
theorem neg_ok (a : Thing) (h : a.ok = true) : (-a).ok = true := by
  simp only [Thing.ok, Bool.or_eq_true, List.contains_iff_mem] at h ⊢
  rcases h with h | h
  · left
    simp only [Thing.isParticle, Bool.and_eq_true, isSign_iff, Thing.neg_root, Thing.neg_t₀,
      Thing.neg_t₁, Thing.neg_t₂, Thing.neg_hand] at h ⊢
    omega
  · exact Or.inr (neg_carriers a h)

/-! ## 2. Worlds and events -/

/-- A world: the things it holds. Their order is bookkeeping. -/
abbrev World := List Thing

inductive Event where
  | join (a b : Thing)
  | part (c a : Thing)
  | pair (a : Thing)
  deriving DecidableEq

/-- One event; `none` means it can't happen here. -/
def step (w : World) : Event → Option World
  | .join a b =>
    if a ∈ w ∧ b ∈ w.erase a ∧ (a + b).ok = true then some ((a + b) :: (w.erase a).erase b)
    else none
  | .part c a =>
    if c ∈ w ∧ a.ok = true ∧ (c - a).ok = true then some (a :: (c - a) :: w.erase c) else none
  | .pair a => if a.ok = true then some (a :: -a :: w) else none

/-- A world's total of some quantity, thing by thing. -/
def sumOf (q : Thing → Int) (w : World) : Int := (w.map q).sum

theorem sumOf_cons (q : Thing → Int) (t : Thing) (w : World) :
    sumOf q (t :: w) = q t + sumOf q w := by simp [sumOf]

/-- Taking out a member leaves the total less that member's share. -/
theorem sumOf_erase (q : Thing → Int) {t : Thing} {w : World} (h : t ∈ w) :
    sumOf q w = q t + sumOf q (w.erase t) := by
  induction w with
  | nil => cases h
  | cons x xs ih =>
    by_cases hx : x = t
    · subst hx; simp [sumOf_cons]
    · have ht : t ∈ xs := (List.mem_cons.mp h).resolve_left (Ne.symm hx)
      rw [List.erase_cons_tail (by simpa using hx), sumOf_cons, sumOf_cons, ih ht]
      omega

/-! ## 3. One law: the world's total never changes -/

/-- A quantity is kept by every event if a twin pair has none of it, and
whenever `a + b = c` happens, `a` and `b` together have as much as `c`. -/
theorem step_keeps' (q : Thing → Int) (hpair : ∀ a, a.ok = true → q a + q (-a) = 0)
    (hjoin : ∀ a b, a.ok = true → b.ok = true → (a + b).ok = true → q a + q b = q (a + b))
    (w : World) (hw : ∀ t ∈ w, t.ok = true)
    {w' : World} {e : Event} (h : step w e = some w') : sumOf q w' = sumOf q w := by
  cases e with
  | join a b =>
    simp only [step] at h
    split at h
    · rename_i hm; cases h
      have ha := hw a hm.1
      have hb := hw b (List.mem_of_mem_erase hm.2.1)
      rw [sumOf_cons, sumOf_erase q hm.1, sumOf_erase q hm.2.1, ← hjoin a b ha hb hm.2.2]
      omega
    · cases h
  | part c a =>
    simp only [step] at h
    split at h
    · rename_i hm; cases h
      have := hjoin a (c - a) hm.2.1 hm.2.2 (by rw [Thing.add_sub]; exact hw c hm.1)
      rw [Thing.add_sub] at this
      rw [sumOf_cons, sumOf_cons, sumOf_erase q hm.1]
      omega
    · cases h
  | pair a =>
    simp only [step] at h
    split at h
    · rename_i hm; cases h
      rw [sumOf_cons, sumOf_cons, ← Int.add_assoc, hpair a hm, Int.zero_add]
    · cases h

/-- Everything an event leaves behind may exist, if everything before it
could. -/
theorem step_things {w w' : World} {e : Event} (hw : ∀ t ∈ w, t.ok = true)
    (h : step w e = some w') : ∀ t ∈ w', t.ok = true := by
  cases e with
  | join a b =>
    simp only [step] at h
    split at h
    · rename_i hm; cases h
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hm.2.2
      · exact hw t (List.mem_of_mem_erase (List.mem_of_mem_erase ht))
    · cases h
  | part c a =>
    simp only [step] at h
    split at h
    · rename_i hm; cases h
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hm.2.1
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hm.2.2
      · exact hw t (List.mem_of_mem_erase ht)
    · cases h
  | pair a =>
    simp only [step] at h
    split at h
    · rename_i hm; cases h
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hm
      rcases List.mem_cons.mp ht with rfl | ht
      · exact neg_ok _ hm
      · exact hw t ht
    · cases h

/-- Every quantity that adds up, slot by slot, is kept by every event, in
any world. -/
theorem step_keeps (q : Thing → Int) (hq : ∀ a b, q (a + b) = q a + q b)
    {w w' : World} {e : Event} (h : step w e = some w') : sumOf q w' = sumOf q w := by
  have h0 : q 0 = 0 := by have := hq 0 0; rw [show (0 : Thing) + 0 = 0 by rfl] at this; omega
  cases e with
  | join a b =>
    simp only [step] at h
    split at h
    · rename_i hm; cases h
      rw [sumOf_cons, sumOf_erase q hm.1, sumOf_erase q hm.2.1, hq]; omega
    · cases h
  | part c a =>
    simp only [step] at h
    split at h
    · rename_i hm; cases h
      have := hq a (c - a); rw [Thing.add_sub] at this
      rw [sumOf_cons, sumOf_cons, sumOf_erase q hm.1]; omega
    · cases h
  | pair a =>
    simp only [step] at h
    split at h
    · cases h
      have := hq a (-a); rw [Thing.add_neg, h0] at this
      rw [sumOf_cons, sumOf_cons]; omega
    · cases h

/-- The world's total, slot by slot. -/
def total (w : World) : Thing :=
  ⟨sumOf (·.root) w, sumOf (·.t₀) w, sumOf (·.t₁) w, sumOf (·.t₂) w, sumOf (·.hand) w⟩

/-- **The one law.** No event changes the world's total. -/
theorem step_total {w w' : World} {e : Event} (h : step w e = some w') : total w' = total w := by
  simp only [total, step_keeps _ Thing.add_root h, step_keeps _ Thing.add_t₀ h,
    step_keeps _ Thing.add_t₁ h, step_keeps _ Thing.add_t₂ h, step_keeps _ Thing.add_hand h]

/-- Charge is kept (in sixths of e). -/
theorem step_charge {w w' : World} {e : Event} (h : step w e = some w') :
    sumOf Thing.charge w' = sumOf Thing.charge w :=
  step_keeps _ (fun a b => by simp [Thing.charge, Thing.tips]; omega) h

/-- Colour is kept: the world's total at each tip place. -/
theorem step_colour {w w' : World} {e : Event} (h : step w e = some w') :
    sumOf (·.t₀) w' = sumOf (·.t₀) w ∧ sumOf (·.t₁) w' = sumOf (·.t₁) w ∧
      sumOf (·.t₂) w' = sumOf (·.t₂) w :=
  ⟨step_keeps _ Thing.add_t₀ h, step_keeps _ Thing.add_t₁ h, step_keeps _ Thing.add_t₂ h⟩

/-- B − L is kept (in thirds): the sum of the tips. -/
theorem step_tips {w w' : World} {e : Event} (h : step w e = some w') :
    sumOf Thing.tips w' = sumOf Thing.tips w :=
  step_keeps _ (fun a b => by simp [Thing.tips]; omega) h

/-! ## 4. Baryon and lepton number, which are not sums of slots -/

/-- Baryon number, in thirds: a quark's tips add to +1, an antiquark's to −1. -/
def baryon3 (a : Thing) : Int := if a.tips = 1 then 1 else if a.tips = -1 then -1 else 0

/-- Lepton number: a lepton's tips add to −3, an antilepton's to +3. -/
def lepton (a : Thing) : Int := if a.tips = -3 then 1 else if a.tips = 3 then -1 else 0

/-- The tips of anything that may exist add to one of five sums. -/
def tipSums : List Int := [3, 1, -1, -3, 0]

theorem carriers_tips : ∀ a ∈ carriers, a.tips = 0 := by decide

theorem tips_mem (a : Thing) (h : a.ok = true) : a.tips ∈ tipSums := by
  simp only [Thing.ok, Bool.or_eq_true, List.contains_iff_mem] at h
  rcases h with h | h
  · simp only [Thing.isParticle, Bool.and_eq_true, isSign_iff] at h
    simp only [tipSums, Thing.tips, List.mem_cons, List.mem_nil_iff, or_false]
    omega
  · rw [carriers_tips a h]; decide

theorem tips_add (a b : Thing) : (a + b).tips = a.tips + b.tips := by
  simp only [Thing.tips, Thing.add_t₀, Thing.add_t₁, Thing.add_t₂]; omega

/-- The heart of it: whenever two of the five sums add to a third, their
baryon numbers, and their lepton numbers, add up too. -/
theorem sums_baryon : ∀ s ∈ tipSums, ∀ s' ∈ tipSums, s + s' ∈ tipSums →
    (if s = 1 then 1 else if s = -1 then -1 else 0) +
      (if s' = 1 then 1 else if s' = -1 then -1 else 0) =
      (if s + s' = 1 then 1 else if s + s' = -1 then -1 else (0 : Int)) := by decide

theorem sums_lepton : ∀ s ∈ tipSums, ∀ s' ∈ tipSums, s + s' ∈ tipSums →
    (if s = -3 then 1 else if s = 3 then -1 else 0) +
      (if s' = -3 then 1 else if s' = 3 then -1 else 0) =
      (if s + s' = -3 then 1 else if s + s' = 3 then -1 else (0 : Int)) := by decide

/-- Whenever two things join, they carry as much baryon number as the
result. -/
theorem join_baryon (a b : Thing) (ha : a.ok = true) (hb : b.ok = true)
    (hab : (a + b).ok = true) : baryon3 a + baryon3 b = baryon3 (a + b) := by
  have := sums_baryon _ (tips_mem a ha) _ (tips_mem b hb) (tips_add a b ▸ tips_mem _ hab)
  simp only [baryon3, tips_add]; exact this

theorem join_lepton (a b : Thing) (ha : a.ok = true) (hb : b.ok = true)
    (hab : (a + b).ok = true) : lepton a + lepton b = lepton (a + b) := by
  have := sums_lepton _ (tips_mem a ha) _ (tips_mem b hb) (tips_add a b ▸ tips_mem _ hab)
  simp only [lepton, tips_add]; exact this

theorem neg_tips (a : Thing) : (-a).tips = -a.tips := by
  show -a.t₀ + -a.t₁ + -a.t₂ = -(a.t₀ + a.t₁ + a.t₂); omega

theorem step_baryon {w w' : World} {e : Event} (hw : ∀ t ∈ w, t.ok = true)
    (h : step w e = some w') : sumOf baryon3 w' = sumOf baryon3 w :=
  step_keeps' _ (fun a ha => by
    have := join_baryon a (-a) ha (neg_ok a ha) (by rw [Thing.add_neg]; decide)
    rw [Thing.add_neg] at this; exact this.trans (by decide))
    join_baryon w hw h

theorem step_lepton {w w' : World} {e : Event} (hw : ∀ t ∈ w, t.ok = true)
    (h : step w e = some w') : sumOf lepton w' = sumOf lepton w :=
  step_keeps' _ (fun a ha => by
    have := join_lepton a (-a) ha (neg_ok a ha) (by rw [Thing.add_neg]; decide)
    rw [Thing.add_neg] at this; exact this.trans (by decide))
    join_lepton w hw h

/-! ## 5. What addition decides by itself -/

/-- Matter, not antimatter: an up or down quark (tips add to +1) or a
lepton (tips add to −3). -/
def isMatter (a : Thing) : Bool := a.tips == 1 || a.tips == -3

/-- **The weak force is left-handed.** A W can join a particle exactly when
the particle is left-handed matter or right-handed antimatter: adding ±2 to
the root and the hand stays within ±1 only when they agree. -/
theorem w_iff : ∀ a ∈ particles,
    ((a + wPlus).ok = true ∨ (a + -wPlus).ok = true) ↔
      ((a.value == -1 && isMatter a) || (a.value == 1 && !isMatter a)) = true := by
  decide

/-- **Leptons are colourless.** A gluon joins only quarks. -/
theorem gluon_quark : ∀ a ∈ particles, ∀ g ∈ gluons, (a + g).ok = true →
    a.tips = 1 ∨ a.tips = -1 := by decide

/-- **Inside and outside.** When the photon, a W or a gluon joins a
particle, it never changes the particle's hand (the product of its points); the Higgs always
does. Gauge forces add on the outside; the Higgs, the source of mass, changes
the inside. -/
theorem inside_outside : ∀ a ∈ particles, ∀ b ∈ carriers, (a + b).isParticle = true →
    ((a + b).value = a.value ↔ (b ≠ higgs ∧ b ≠ -higgs)) := by decide

/-- **Gluons meet gluons:** two gluons join into a third, or into the
photon (the empty container), as in the three-gluon vertex. -/
theorem gluon_gluon : ∀ g ∈ gluons, ∀ g' ∈ gluons, (g + g').ok = true →
    g + g' ∈ gluons ∨ g + g' = photon := by decide

example : (⟨0, 2, -2, 0, 0⟩ : Thing) + ⟨0, 0, 2, -2, 0⟩ = ⟨0, 2, 0, -2, 0⟩ := by decide

/-- A W⁺ and a W⁻ join into the photon: W pairs come from light. -/
theorem w_w : wPlus + -wPlus = photon := by decide

/-- `0 + m = m`: absorbing a photon changes nothing. -/
theorem photon_add (m : Thing) : photon + m = m := by
  ext <;> show 0 + _ = _ <;> omega

/-- A particle and its twin add up to the photon: annihilation leaves light. -/
theorem annihilate (a : Thing) : a + -a = photon := Thing.add_neg a

end Velcro
