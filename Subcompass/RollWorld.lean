import Subcompass.RollPlace
import Subcompass.VelcroSuite

/-!
# Roll: team 5's model, generation 0 (tag `t5g0`), part 2: things in 3D space

The plain-words version is `Roll.md`. Part 1 (`Roll.lean`) is the motion in
any dimension; `RollPlace.lean` writes it out for three dimensions, where a
place is a tetrahedron.

Zigzag (team 4) puts Velcro's things on a line of cells, and matter hops the
way its hand points. Roll puts them in 3D space, on tetrahedra that roll by
tipping over their faces. The events are Zigzag's, with the hop replaced:

* `join i a b`, `part i c a`, `pair i a`: Velcro's three events, at place `i`.
  They lock `i`.
* `roll i a f`: the thing `a` at the tetrahedron `i` rolls one tip, forward
  round the ring (`f`) or back. It locks `i` and the tetrahedron it rolls to,
  which shares a face with `i` and is one step away.

## The one rule

**Matter rolls the way its hand turns**: right-handed things forward round
the ring of corners, left-handed things back. A force carrier has no hand and
rolls either way. Which way in space a roll goes is not in the thing at all:
it is in the order of the tetrahedron's corners (`Roll.lean`, `step_fwd`). So
two electrons can go different ways, and the hand only says forward or back
along that way. In a line, forward and back are right and left, and Roll is
Zigzag.

## What is checked below

Everything Zigzag checks, now in space with no grid: Velcro's one law, so
charge, colour, baryon and lepton number are kept; a tick reads and changes
only what it locks, and locks only places at most a step apart (`near`); ticks
on separate places happen in either order (`no_global_now`); only the Higgs
turns matter back (`course`); the W touches only matter that rolls back
(`w_left`). Then light: a massless thing rolls straight, one lattice step for
every three tips, and back along the same line if it ever turns round.
-/

namespace RollWorld

open Velcro

/-! ## 1. Worlds and ticks -/

/-- A world: its things, each at a place (a tetrahedron). The order of the
list is bookkeeping. -/
abbrev World := List (Place × Thing)

/-- Forward round the ring is +1, backward −1. -/
def dir (fwd : Bool) : Int := if fwd then 1 else -1

/-- Matter rolls only the way its hand turns: right-handed forward round the
ring, left-handed backward; a force carrier either way. -/
def mayRoll (a : Thing) (fwd : Bool) : Bool := !a.isParticle || a.value == dir fwd

inductive Event where
  | join (i : Place) (a b : Thing)
  | part (i : Place) (c a : Thing)
  | pair (i : Place) (a : Thing)
  | roll (i : Place) (a : Thing) (fwd : Bool)
  deriving DecidableEq

namespace Event

/-- What a tick takes out of the world. -/
def takes : Event → World
  | join i a b => [(i, a), (i, b)]
  | part i c _ => [(i, c)]
  | pair _ _ => []
  | roll i a _ => [(i, a)]

/-- What a tick puts back. (A roll from a tetrahedron that is not proper never
happens; it is given a dummy outcome, in place, so that everything a tick
touches is among what it locks.) -/
def gives : Event → World
  | join i a b => [(i, a + b)]
  | part i c a => [(i, a), (i, c - a)]
  | pair i a => [(i, a), (i, -a)]
  | roll i a f => if i.proper then [(i.move f, a)] else [(i, a)]

/-- Whether the things involved allow it: Velcro's rules, and the hand. -/
def allowed : Event → Bool
  | join _ a b => (a + b).ok
  | part _ c a => a.ok && (c - a).ok
  | pair _ a => a.ok
  | roll i a f => i.proper && mayRoll a f

/-- The places a tick locks. -/
def locks : Event → List Place
  | join i .. | part i .. | pair i .. => [i]
  | roll i _ f => if i.proper then [i, i.move f] else [i]

theorem takes_locks (e : Event) : ∀ p ∈ e.takes, p.1 ∈ e.locks := by
  cases e with
  | roll i a f => simp only [takes, locks]; split <;> simp
  | _ => simp [takes, locks]

theorem gives_locks (e : Event) : ∀ p ∈ e.gives, p.1 ∈ e.locks := by
  cases e with
  | roll i a f => simp only [gives, locks]; split <;> simp
  | _ => simp [gives, locks]

end Event

/-- `t` fits in `w`: `w` holds everything in `t`, as often. -/
def fits (t w : World) : Bool := t.all fun p => t.count p ≤ w.count p

/-- Take each member of `t` out of `w`, once. -/
def remove (t w : World) : World := t.foldl List.erase w

/-- One tick; `none` means it can't happen here. -/
def step (w : World) (e : Event) : Option World :=
  if (e.allowed && fits e.takes w) = true then some (e.gives ++ remove e.takes w) else none

/-- What place `j` holds. -/
def cell (w : World) (j : Place) : List Thing := (w.filter (·.1 == j)).map (·.2)

/-- All the things in a world, wherever they are. -/
def things (w : World) : List Thing := w.map (·.2)

/-! ## 2. Counting -/

theorem fits_iff (t w : World) : fits t w = true ↔ ∀ p, t.count p ≤ w.count p := by
  simp only [fits, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun h p => ?_, fun h p _ => h p⟩
  by_cases hp : p ∈ t
  · exact h p hp
  · rw [List.count_eq_zero_of_not_mem hp]; omega

theorem count_remove (p : Place × Thing) (t w : World) :
    (remove t w).count p = w.count p - t.count p := by
  induction t generalizing w with
  | nil => simp [remove]
  | cons x t ih =>
    simp only [remove, List.foldl_cons] at ih ⊢
    rw [ih, List.count_erase, List.count_cons]
    omega

theorem count_step {w w' : World} {e : Event} (h : step w e = some w') :
    e.allowed = true ∧ (∀ p, e.takes.count p ≤ w.count p) ∧
      ∀ p, w'.count p = e.gives.count p + (w.count p - e.takes.count p) := by
  simp only [step] at h
  split at h
  · rename_i hc; cases h
    simp only [Bool.and_eq_true] at hc
    exact ⟨hc.1, (fits_iff _ _).mp hc.2, fun p => by rw [List.count_append, count_remove]⟩
  · cases h

theorem step_of {w : World} {e : Event} (ha : e.allowed = true)
    (hf : ∀ p, e.takes.count p ≤ w.count p) :
    step w e = some (e.gives ++ remove e.takes w) := by
  simp [step, ha, (fits_iff _ _).mpr hf]

theorem count_cell (w : World) (j : Place) (x : Thing) : (cell w j).count x = w.count (j, x) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    obtain ⟨i, y⟩ := p
    simp only [cell, List.filter_cons] at ih ⊢
    by_cases hi : i = j
    · subst hi
      simp only [beq_self_eq_true, ite_true, List.map_cons, List.count_cons, ih]
      by_cases hy : y = x <;> simp [hy]
    · simp only [show (i == j) = false by simpa using hi, Bool.false_eq_true, ite_false, ih,
        List.count_cons]
      simp [hi]

theorem perm_cell (w₁ w₂ : World) (j : Place) :
    (cell w₁ j).Perm (cell w₂ j) ↔ ∀ x, w₁.count (j, x) = w₂.count (j, x) := by
  rw [List.perm_iff_count]; simp only [count_cell]

/-- Nothing a tick takes or gives lies outside the places it locks. -/
theorem count_out (e : Event) (p : Place × Thing) (hp : p.1 ∉ e.locks) :
    e.takes.count p = 0 ∧ e.gives.count p = 0 :=
  ⟨List.count_eq_zero_of_not_mem fun h => hp (e.takes_locks p h),
   List.count_eq_zero_of_not_mem fun h => hp (e.gives_locks p h)⟩

/-! ## 3. Locality, and no global now -/

/-- A tick locks only neighbouring places: at most one step apart. -/
theorem near (e : Event) : ∀ i ∈ e.locks, ∀ j ∈ e.locks, Place.dist i j ≤ 1 := by
  have self : ∀ p, Place.dist p p ≤ 1 := fun p => by rw [Place.dist_self]; omega
  intro i hi j hj
  cases e with
  | roll k a f =>
    by_cases hk : k.proper = true
    · have := Place.dist_move hk f
      simp only [Event.locks, hk, ite_true, List.mem_cons, List.mem_nil_iff, or_false] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact self _
      · exact this.1
      · exact this.2
      · exact self _
    · have hk' : k.proper = false := by simpa using hk
      simp only [Event.locks, hk', Bool.false_eq_true, ite_false, List.mem_cons,
        List.mem_nil_iff, or_false] at hi hj
      subst hi hj; exact self _
  | _ =>
    simp only [Event.locks, List.mem_cons, List.mem_nil_iff, or_false] at hi hj
    subst hi hj; exact self _

theorem local_ {w w' : World} {e : Event} (h : step w e = some w') (j : Place) (hj : j ∉ e.locks) :
    (cell w' j).Perm (cell w j) := by
  rw [perm_cell]; intro x
  obtain ⟨_, _, hc⟩ := count_step h
  obtain ⟨h₁, h₂⟩ := count_out e (j, x) hj
  rw [hc, h₁, h₂]; omega

theorem reads (w₁ w₂ : World) (e : Event)
    (hag : ∀ j ∈ e.locks, (cell w₁ j).Perm (cell w₂ j)) :
    (step w₁ e).isSome = (step w₂ e).isSome ∧
    ∀ w₁' w₂', step w₁ e = some w₁' → step w₂ e = some w₂' →
      ∀ j ∈ e.locks, (cell w₁' j).Perm (cell w₂' j) := by
  have hag' : ∀ p : Place × Thing, p.1 ∈ e.locks → w₁.count p = w₂.count p :=
    fun ⟨j, x⟩ hj => (perm_cell w₁ w₂ j).mp (hag j hj) x
  have hfit : fits e.takes w₁ = fits e.takes w₂ := by
    apply Bool.eq_iff_iff.mpr
    rw [fits_iff, fits_iff]
    constructor <;> intro hf p <;> by_cases hp : p.1 ∈ e.locks
    · rw [← hag' p hp]; exact hf p
    · rw [(count_out e p hp).1]; omega
    · rw [hag' p hp]; exact hf p
    · rw [(count_out e p hp).1]; omega
  refine ⟨by simp only [step, hfit]; split <;> rfl, fun w₁' w₂' h₁ h₂ j hj => ?_⟩
  rw [perm_cell]; intro x
  rw [(count_step h₁).2.2, (count_step h₂).2.2, hag' (j, x) hj]

theorem no_global_now {w w₁ w₂ : World} {e f : Event} (hd : ∀ j ∈ e.locks, j ∉ f.locks)
    (h₁ : step w e = some w₁) (h₂ : step w₁ f = some w₂) :
    ∃ w₃ w₄, step w f = some w₃ ∧ step w₃ e = some w₄ ∧ ∀ p, w₄.count p = w₂.count p := by
  obtain ⟨ea, et, ec⟩ := count_step h₁
  obtain ⟨fa, ft, fc⟩ := count_step h₂
  -- For each place, one of the two ticks has nothing there.
  have split : ∀ p : Place × Thing,
      (e.takes.count p = 0 ∧ e.gives.count p = 0) ∨ (f.takes.count p = 0 ∧ f.gives.count p = 0) :=
    fun p => if hp : p.1 ∈ e.locks then .inr (count_out f p (hd _ hp)) else .inl (count_out e p hp)
  have ft' : ∀ p, f.takes.count p ≤ w.count p := fun p => by
    have := ft p; have := ec p; rcases split p with ⟨a, b⟩ | ⟨a, b⟩ <;> omega
  have et' : ∀ p, e.takes.count p ≤ (f.gives ++ remove f.takes w).count p := fun p => by
    rw [List.count_append, count_remove]
    have := et p; rcases split p with ⟨a, b⟩ | ⟨a, b⟩ <;> omega
  refine ⟨_, _, step_of fa ft', step_of ea et', fun p => ?_⟩
  simp only [List.count_append, count_remove, fc, ec]
  have := et p; have := ft p; have := ec p
  rcases split p with ⟨a, b⟩ | ⟨a, b⟩ <;> omega

/-- Each place's own clock: how many ticks of a history have locked it. There
is no other clock. -/
def clock (es : List Event) (j : Place) : Nat := es.countP fun e => decide (j ∈ e.locks)

/-- Swapping two neighbouring ticks in a history changes no place's clock. -/
theorem clock_swap (es es' : List Event) (e f : Event) (j : Place) :
    clock (es ++ e :: f :: es') j = clock (es ++ f :: e :: es') j := by
  simp only [clock, List.countP_append, List.countP_cons]; omega

/-! ## 4. Velcro's one law, in space -/

/-- A tick regroups what it takes into what it gives. -/
theorem perm_step {w w' : World} {e : Event} (h : step w e = some w') :
    (things w').Perm (things e.gives ++ things (remove e.takes w)) ∧
    (things w).Perm (things e.takes ++ things (remove e.takes w)) := by
  obtain ⟨_, ht, hc⟩ := count_step h
  unfold things
  rw [← List.map_append, ← List.map_append]
  refine ⟨(List.perm_iff_count.mpr fun p => ?_).map _, (List.perm_iff_count.mpr fun p => ?_).map _⟩
  · rw [hc, List.count_append, count_remove]
  · rw [List.count_append, count_remove]; have := ht p; omega

theorem sumOf_perm (q : Thing → Int) {l l' : List Thing} (h : l.Perm l') : sumOf q l = sumOf q l' :=
  Suite.perm_sum (h.map q)

theorem sumOf_append (q : Thing → Int) (l l' : List Thing) :
    sumOf q (l ++ l') = sumOf q l + sumOf q l' := by simp [sumOf]

/-- Everything a tick takes was in the world. -/
theorem mem_of_takes {w w' : World} {e : Event} (h : step w e = some w') :
    ∀ p ∈ e.takes, p ∈ w := fun p hp => by
  have := (count_step h).2.1 p
  have := List.count_pos_iff.mpr hp
  exact List.count_pos_iff.mp (by omega)

/-- A quantity is kept by every tick if a twin pair has none of it, and
whenever `a + b` may exist, `a` and `b` together have as much as `a + b`. -/
theorem step_keeps' (q : Thing → Int) (hpair : ∀ a, a.ok = true → q a + q (-a) = 0)
    (hjoin : ∀ a b, a.ok = true → b.ok = true → (a + b).ok = true → q a + q b = q (a + b))
    (w : World) (hw : ∀ p ∈ w, p.2.ok = true)
    {w' : World} {e : Event} (h : step w e = some w') :
    sumOf q (things w') = sumOf q (things w) := by
  obtain ⟨p₁, p₂⟩ := perm_step h
  rw [sumOf_perm q p₁, sumOf_perm q p₂, sumOf_append, sumOf_append]
  have hm := mem_of_takes h
  have ha := (count_step h).1
  congr 1
  cases e with
  | join i a b =>
    simp only [Event.takes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
      forall_eq] at hm
    simp only [Event.allowed] at ha
    simp only [things, Event.gives, Event.takes, List.map_cons, List.map_nil, sumOf_cons]
    rw [← hjoin a b (hw _ hm.1) (hw _ hm.2) ha]; simp [sumOf]
  | part i c a =>
    simp only [Event.takes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at hm
    simp only [Event.allowed, Bool.and_eq_true] at ha
    simp only [things, Event.gives, Event.takes, List.map_cons, List.map_nil, sumOf_cons]
    have := hjoin a (c - a) ha.1 ha.2 (by rw [Thing.add_sub]; exact hw _ hm)
    rw [Thing.add_sub] at this; simp [sumOf]; omega
  | pair i a =>
    simp only [Event.allowed] at ha
    simp only [things, Event.gives, Event.takes, List.map_cons, List.map_nil, sumOf_cons]
    have := hpair a ha; simp [sumOf]; omega
  | roll i a f => simp only [things, Event.gives, Event.takes]; split <;> simp

/-- Everything a tick leaves behind may exist, if everything before it could. -/
theorem step_ok {w w' : World} {e : Event} (hw : ∀ p ∈ w, p.2.ok = true)
    (h : step w e = some w') : ∀ p ∈ w', p.2.ok = true := by
  obtain ⟨ha, _, hc⟩ := count_step h
  have hm := mem_of_takes h
  intro p hp
  have hp' := List.count_pos_iff.mpr hp
  rw [hc] at hp'
  by_cases hg : p ∈ e.gives
  · cases e with
    | join i a b =>
      simp only [Event.gives, List.mem_cons, List.mem_nil_iff, or_false] at hg
      subst hg; exact ha
    | part i c a =>
      simp only [Event.allowed, Bool.and_eq_true] at ha
      simp only [Event.gives, List.mem_cons, List.mem_nil_iff, or_false] at hg
      rcases hg with rfl | rfl
      · exact ha.1
      · exact ha.2
    | pair i a =>
      simp only [Event.allowed] at ha
      simp only [Event.gives, List.mem_cons, List.mem_nil_iff, or_false] at hg
      rcases hg with rfl | rfl
      · exact ha
      · exact neg_ok a ha
    | roll i a f =>
      have : p.2 = a := by
        simp only [Event.gives] at hg; split at hg <;> simp at hg <;> rw [hg]
      rw [this]
      exact hw (i, a) (hm _ (by simp [Event.takes]))
  · rw [List.count_eq_zero_of_not_mem hg] at hp'
    exact hw p (List.count_pos_iff.mp (by omega))

/-- Every quantity that adds up, slot by slot, is kept by every tick, in any
world. -/
theorem step_keeps (q : Thing → Int) (hq : ∀ a b, q (a + b) = q a + q b)
    {w w' : World} {e : Event} (h : step w e = some w') :
    sumOf q (things w') = sumOf q (things w) := by
  have h0 : q 0 = 0 := by have := hq 0 0; rw [show (0 : Thing) + 0 = 0 by rfl] at this; omega
  obtain ⟨p₁, p₂⟩ := perm_step h
  rw [sumOf_perm q p₁, sumOf_perm q p₂, sumOf_append, sumOf_append]
  congr 1
  cases e with
  | join i a b => simp [things, Event.gives, Event.takes, sumOf, hq]
  | part i c a =>
    have := hq a (c - a); rw [Thing.add_sub] at this
    simp [things, Event.gives, Event.takes, sumOf]; omega
  | pair i a =>
    have := hq a (-a); rw [Thing.add_neg, h0] at this
    simp [things, Event.gives, Event.takes, sumOf]; omega
  | roll i a f => simp only [things, Event.gives, Event.takes]; split <;> simp

/-- **The one law.** No tick changes the world's total, slot by slot. -/
theorem step_total {w w' : World} {e : Event} (h : step w e = some w') :
    total (things w') = total (things w) := by
  simp only [total, step_keeps _ Thing.add_root h, step_keeps _ Thing.add_t₀ h,
    step_keeps _ Thing.add_t₁ h, step_keeps _ Thing.add_t₂ h, step_keeps _ Thing.add_hand h]

theorem step_charge {w w' : World} {e : Event} (h : step w e = some w') :
    sumOf Thing.charge (things w') = sumOf Thing.charge (things w) :=
  step_keeps _ (fun a b => by simp [Thing.charge, Thing.tips]; omega) h

theorem step_baryon {w w' : World} (hw : ∀ p ∈ w, p.2.ok = true) {e : Event}
    (h : step w e = some w') : sumOf baryon3 (things w') = sumOf baryon3 (things w) :=
  step_keeps' _ (fun a ha => by
    have := join_baryon a (-a) ha (neg_ok a ha) (by rw [Thing.add_neg]; decide)
    rw [Thing.add_neg] at this; exact this.trans (by decide))
    join_baryon w hw h

theorem step_lepton {w w' : World} (hw : ∀ p ∈ w, p.2.ok = true) {e : Event}
    (h : step w e = some w') : sumOf lepton (things w') = sumOf lepton (things w) :=
  step_keeps' _ (fun a ha => by
    have := join_lepton a (-a) ha (neg_ok a ha) (by rw [Thing.add_neg]; decide)
    rw [Thing.add_neg] at this; exact this.trans (by decide))
    join_lepton w hw h

/-! ## 5. Hands are ways round the ring -/

/-- Matter rolls only the way its hand turns. -/
theorem roll_hand {w w' : World} {i : Place} {a : Thing} {f : Bool}
    (h : step w (.roll i a f) = some w') (ha : a.isParticle = true) : a.value = dir f := by
  have := (count_step h).1
  simp only [Event.allowed, mayRoll, ha, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    beq_iff_eq] at this
  exact this.2

/-- **Only the Higgs turns matter around.** When the photon, a W or a gluon
joins a particle, the particle keeps its hand, and so the way it rolls; when the Higgs does, the
particle rolls back the way it came. A particle that never meets the Higgs
(massless) rolls straight; one that does (massive) zigzags. This is Velcro's
`inside_outside`, read in space. -/
theorem course : ∀ a ∈ particles, ∀ b ∈ carriers, (a + b).isParticle = true →
    ((a + b).value = a.value ↔ (b ≠ higgs ∧ b ≠ -higgs)) := inside_outside

/-- **The weak force touches only matter that rolls backward and antimatter
that rolls forward.** This is Velcro's `w_iff`, read in space: a particle whose
value is −1 rolls backward round the ring. -/
theorem w_left : ∀ a ∈ particles,
    ((a + wPlus).ok = true ∨ (a + -wPlus).ok = true) ↔
      ((a.value == -1 && isMatter a) || (a.value == 1 && !isMatter a)) = true := w_iff

/-! ## 6. Worked examples -/

/-- A history: ticks one after another. -/
def run (w : World) (es : List Event) : Option World := es.foldlM step w

/-- `n` rolls of the thing `a`, all the same way, from place `i`. -/
def rolls (i : Place) (a : Thing) (f : Bool) : Nat → List Event
  | 0 => []
  | n + 1 => .roll i a f :: rolls (i.move f) a f n

/-- A place moved by `t`. -/
def Place.shift (i : Place) (t : Pt) : Place := ⟨i.c₀ + t, i.c₁ + t, i.c₂ + t, i.c₃ + t⟩

/-- The tetrahedron at a corner of the unit cube: its seam is (−1, −1, −1). -/
def home : Place := ⟨⟨0, 0, 0⟩, ⟨1, 0, 0⟩, ⟨1, 1, 0⟩, ⟨1, 1, 1⟩⟩

theorem home_proper : home.proper = true := by decide

/-- A left-handed and a right-handed electron (Zigzag's). -/
def eL : Thing := ⟨-1, -1, -1, -1, -1⟩
def eR : Thing := ⟨-1, -1, -1, -1, 1⟩

/-- **Rolling straight.** A right-handed electron rolls forward: every three
tips it is the same tetrahedron again, one step along the cube's diagonal. -/
example : run [(home, eR)] (rolls home eR true 3) = some [(home.shift ⟨1, 1, 1⟩, eR)] := by
  decide
example : run [(home, eR)] (rolls home eR true 12) = some [(home.shift ⟨4, 4, 4⟩, eR)] := by
  decide

/-- A left-handed electron rolls back along the same line. -/
example : run [(home, eL)] (rolls home eL false 3) = some [(home.shift ⟨-1, -1, -1⟩, eL)] := by
  decide

/-- It can't roll forward. -/
example : step [(home, eL)] (.roll home eL true) = none := by decide

/-- **The zigzag, in 3D.** The electron rolls back three tips, takes in a
Higgs from a pair the vacuum lends, turns right-handed and rolls forward three
tips to where it started, then gives the Higgs off and rolls back again. -/
example : (run [(home, eL)]
      (rolls home eL false 3 ++
       [.pair (home.shift ⟨-1, -1, -1⟩) higgs, .join (home.shift ⟨-1, -1, -1⟩) eL higgs] ++
       rolls (home.shift ⟨-1, -1, -1⟩) eR true 3 ++
       [.part home eR eL] ++ rolls home eL false 1)).map (cell · (home.shift ⟨-1, -1, -1⟩)) =
    some [-higgs] := by decide

/-- Two rolls far apart, in either order, give the same world. -/
example : run [(home, eR), (home.shift ⟨5, 0, 0⟩, eL)]
      [.roll home eR true, .roll (home.shift ⟨5, 0, 0⟩) eL false] =
    (run [(home, eR), (home.shift ⟨5, 0, 0⟩, eL)]
      [.roll (home.shift ⟨5, 0, 0⟩) eL false, .roll home eR true]).map List.reverse := by
  decide

end RollWorld
