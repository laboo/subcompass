import Subcompass.VelcroSuite

/-!
# Zigzag: team 4's model, generation 0 (tag `t4g0`)

The plain-words version is `Zigzag.md`.

Velcro (team 3) is a bag of things with no space in it. Zigzag puts Velcro's
things in space, a line of cells, and makes them move. Each cell is a point of
space and holds a Velcro bag.

## Ticks

A *tick* is one event. It locks the cells it needs, does its work there, and
lets them go. There is no global clock: two ticks on different cells need not
come in any order.

* `join i a b`, `part i c a`, `pair i a`: Velcro's three events, inside cell
  `i`. They lock cell `i`.
* `hop i a r`: the thing `a` moves from cell `i` one cell to the right (`r`)
  or the left. It locks cell `i` and the cell it moves into.

## The one new rule

**Matter hops the way its hand points.** A particle's hand is the product of
its five points (Penta's and Velcro's value): ⊖ is left, ⊕ is right, and now
that is literally the direction it moves. A force carrier has no hand (its
product is 0), and hops either way. In a line, handedness and direction of
motion are one thing, as they are for massless particles in nature.

## What is checked below

* **Velcro's one law** still holds: no tick changes the world's total, slot
  by slot (`step_total`), so charge is kept (`step_charge`), and so are baryon
  and lepton number (`step_baryon`, `step_lepton`).
* **Locality** (`zigzag_Local`, `zigzag_ReadsLocks`, `zigzag_Near`): a tick
  reads and changes only the cells it locks, and those are neighbours.
* **No global now** (`zigzag_NoGlobalNow`): two ticks that lock no cell in
  common can happen in either order, with the same result in every cell.
* **The speed limit** (`zigzag_SpeedLimit`): after n ticks, what a cell holds
  depends only on what was within n cells of it.
* **Only the Higgs turns matter around** (`course`): the photon, a W or a
  gluon never changes a particle's direction; the Higgs always reverses it.
  A massless particle goes straight; a massive one zigzags.
* **The weak force touches only left-moving matter** (`w_left`) and
  right-moving antimatter.
-/

namespace Zigzag

open Velcro

/-! ## 1. Worlds and ticks -/

/-- A world: its things, each in a cell, numbered along a line. The order of
the list is bookkeeping. -/
abbrev World := List (Int × Thing)

/-- One cell over: to the right is +1, to the left −1. -/
def dir (right : Bool) : Int := if right then 1 else -1

/-- Matter hops only the way its hand points; a force carrier either way. -/
def mayHop (a : Thing) (right : Bool) : Bool := !a.isParticle || a.value == dir right

inductive Event where
  | join (i : Int) (a b : Thing)
  | part (i : Int) (c a : Thing)
  | pair (i : Int) (a : Thing)
  | hop (i : Int) (a : Thing) (right : Bool)
  deriving DecidableEq

namespace Event

/-- What a tick takes out of the world. -/
def takes : Event → World
  | join i a b => [(i, a), (i, b)]
  | part i c _ => [(i, c)]
  | pair _ _ => []
  | hop i a _ => [(i, a)]

/-- What a tick puts back. -/
def gives : Event → World
  | join i a b => [(i, a + b)]
  | part i c a => [(i, a), (i, c - a)]
  | pair i a => [(i, a), (i, -a)]
  | hop i a r => [(i + dir r, a)]

/-- Whether the things involved allow it: Velcro's rules, and the hand. -/
def allowed : Event → Bool
  | join _ a b => (a + b).ok
  | part _ c a => a.ok && (c - a).ok
  | pair _ a => a.ok
  | hop _ a r => mayHop a r

/-- The cells a tick locks. -/
def locks : Event → List Int
  | join i .. | part i .. | pair i .. => [i]
  | hop i _ r => [i, i + dir r]

theorem takes_locks (e : Event) : ∀ p ∈ e.takes, p.1 ∈ e.locks := by
  cases e <;> simp [takes, locks]

theorem gives_locks (e : Event) : ∀ p ∈ e.gives, p.1 ∈ e.locks := by
  cases e <;> simp [gives, locks]

end Event

/-- `t` fits in `w`: `w` holds everything in `t`, as often. -/
def fits (t w : World) : Bool := t.all fun p => t.count p ≤ w.count p

/-- Take each member of `t` out of `w`, once. -/
def remove (t w : World) : World := t.foldl List.erase w

/-- One tick; `none` means it can't happen here. -/
def step (w : World) (e : Event) : Option World :=
  if (e.allowed && fits e.takes w) = true then some (e.gives ++ remove e.takes w) else none

/-- What cell `j` holds. -/
def cell (w : World) (j : Int) : List Thing := (w.filter (·.1 == j)).map (·.2)

/-- All the things in a world, wherever they are. -/
def things (w : World) : List Thing := w.map (·.2)

/-! ## 2. Counting -/

theorem fits_iff (t w : World) : fits t w = true ↔ ∀ p, t.count p ≤ w.count p := by
  simp only [fits, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun h p => ?_, fun h p _ => h p⟩
  by_cases hp : p ∈ t
  · exact h p hp
  · rw [List.count_eq_zero_of_not_mem hp]; omega

theorem count_remove (p : Int × Thing) (t w : World) :
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

theorem count_cell (w : World) (j : Int) (x : Thing) : (cell w j).count x = w.count (j, x) := by
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

theorem perm_cell (w₁ w₂ : World) (j : Int) :
    (cell w₁ j).Perm (cell w₂ j) ↔ ∀ x, w₁.count (j, x) = w₂.count (j, x) := by
  rw [List.perm_iff_count]; simp only [count_cell]

/-- Nothing a tick takes or gives lies outside the cells it locks. -/
theorem count_out (e : Event) (p : Int × Thing) (hp : p.1 ∉ e.locks) :
    e.takes.count p = 0 ∧ e.gives.count p = 0 :=
  ⟨List.count_eq_zero_of_not_mem fun h => hp (e.takes_locks p h),
   List.count_eq_zero_of_not_mem fun h => hp (e.gives_locks p h)⟩

/-! ## 3. Locality, and no global now -/

/-- A tick locks only neighbouring cells. -/
theorem near (e : Event) : ∀ i ∈ e.locks, ∀ j ∈ e.locks, i - j ≤ 1 ∧ j - i ≤ 1 := by
  have hd : ∀ r, dir r = 1 ∨ dir r = -1 := fun r => by cases r <;> simp [dir]
  intro i hi j hj
  cases e with
  | hop k a r =>
    simp only [Event.locks, List.mem_cons, List.mem_nil_iff, or_false] at hi hj
    rcases hd r with h | h <;> omega
  | _ => simp only [Event.locks, List.mem_cons, List.mem_nil_iff, or_false] at hi hj; omega

theorem local_ {w w' : World} {e : Event} (h : step w e = some w') (j : Int) (hj : j ∉ e.locks) :
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
  have hag' : ∀ p : Int × Thing, p.1 ∈ e.locks → w₁.count p = w₂.count p :=
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
  have split : ∀ p : Int × Thing,
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

/-- Each cell's own clock: how many ticks of a history have locked it. There
is no other clock. -/
def clock (es : List Event) (j : Int) : Nat := es.countP fun e => decide (j ∈ e.locks)

/-- Swapping two neighbouring ticks in a history changes no cell's clock. -/
theorem clock_swap (es es' : List Event) (e f : Event) (j : Int) :
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
  | hop i a r => simp [things, Event.gives, Event.takes]

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
    | hop i a r =>
      simp only [Event.gives, List.mem_cons, List.mem_nil_iff, or_false] at hg
      subst hg
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
  | hop i a r => simp [things, Event.gives, Event.takes]

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

/-! ## 5. Hands are directions -/

/-- Matter hops only the way its hand points. -/
theorem hop_hand {w w' : World} {i : Int} {a : Thing} {r : Bool}
    (h : step w (.hop i a r) = some w') (ha : a.isParticle = true) : a.value = dir r := by
  have := (count_step h).1
  simp only [Event.allowed, mayHop, ha, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  exact this

/-- **Only the Higgs turns matter around.** When the photon, a W or a gluon
joins a particle, the particle keeps its direction; when the Higgs does, the
particle reverses. A particle that never meets the Higgs (massless) goes
straight; one that does (massive) zigzags. This is Velcro's `inside_outside`,
read in space. -/
theorem course : ∀ a ∈ particles, ∀ b ∈ carriers, (a + b).isParticle = true →
    ((a + b).value = a.value ↔ (b ≠ higgs ∧ b ≠ -higgs)) := inside_outside

/-- **The weak force touches only left-moving matter and right-moving
antimatter.** This is Velcro's `w_iff`, read in space: a particle whose value
is −1 moves left. -/
theorem w_left : ∀ a ∈ particles,
    ((a + wPlus).ok = true ∨ (a + -wPlus).ok = true) ↔
      ((a.value == -1 && isMatter a) || (a.value == 1 && !isMatter a)) = true := w_iff

/-! ## 6. Worked examples -/

/-- A history: ticks one after another. -/
def run (w : World) (es : List Event) : Option World := es.foldlM step w

/-- A left-handed electron. Its value is −1, so it moves left. -/
def eL : Thing := ⟨-1, -1, -1, -1, -1⟩
/-- A right-handed electron: the same, with the hand flipped. -/
def eR : Thing := ⟨-1, -1, -1, -1, 1⟩

/-- A left-handed electron goes left, one cell per hop. -/
example : run [(0, eL)] [.hop 0 eL false, .hop (-1) eL false, .hop (-2) eL false] =
    some [(-3, eL)] := by decide

/-- It can't go right. -/
example : step [(0, eL)] (.hop 0 eL true) = none := by decide

/-- **The zigzag.** The electron goes left, takes in a Higgs from a pair the
vacuum lends, turns right-handed and goes right, then gives the Higgs off,
turns left-handed again, and goes left. -/
example : (run [(0, eL)]
      [.hop 0 eL false, .pair (-1) higgs, .join (-1) eL higgs,
       .hop (-1) eR true, .part 0 eR eL, .hop 0 eL false]).map (cell · (-1)) =
    some [eL, -higgs] := by decide

/-- Two ticks far apart, in either order, give the same world, cell by cell. -/
example : (run [(0, eL), (5, eR)] [.hop 0 eL false, .hop 5 eR true]).map (cell · (-1)) =
    (run [(0, eL), (5, eR)] [.hop 5 eR true, .hop 0 eL false]).map (cell · (-1)) := by decide

end Zigzag
