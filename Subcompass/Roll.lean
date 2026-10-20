import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Abel

/-!
# Roll: team 5's model, generation 0 (tag `t5g0`), part 1: motion in any dimension

The plain-words version is `Roll.md`.

Zigzag (team 4) moves things along a line of cells, and gets stuck there: a
hand is one bit, and a line has two directions while 3D space has many. Roll
replaces the line by simplices that tip over their own faces, by one rule that
is the same in every dimension.

## The rule

A simplex in `d`-dimensional space has `d + 1` corners, which we keep in a
ring: corner `i` has a corner before it, `i - 1`, and one after it, `i + 1`,
counting round. Corners are points with whole-number coordinates. To **tip**
the simplex over the face opposite corner `i`, replace that corner by

  (the corner before it) + (the corner after it) − (itself).

Nothing else changes. Only addition is used.

## Shape

The *steps* of a simplex are the differences between neighbouring corners
round the ring, `step v k = v k - v (k - 1)`. They add up to zero. A *proper*
simplex is one whose `d + 1` steps are the `d + 1` directions `dirs`: the `d`
unit directions of space and the one that closes the loop, minus all of them.
Proper simplices are all the same shape, and they tile space with no gaps or
overlaps (Kuhn's triangulation, the alcoves of the group SU(d + 1)).

## What is checked below, for every dimension `d`

* **Tipping swaps two steps** (`step_tip`): the steps after `i` and at `i`
  trade places, and nothing else changes. So a proper simplex tips into a
  proper simplex (`Proper.tip`): every move keeps the shape.
* **It shares a face** (`tip_apply_ne`): every corner except `i` stays put.
* **Each move is one lattice step** (`tip_move`): the moving corner shifts by
  the difference of two different directions (`Proper.move`).
* **It can be undone** (`tip_tip`): tipping twice at the same corner gets back
  where you started, so every motion can be played backwards (`unroll`).
* **No order between far corners** (`tip_comm`): tips at two corners that are
  not neighbours give the same simplex in either order.
* **The braid law** (`tip_braid`): for neighbouring corners,
  tip `i`, tip `i + 1`, tip `i` is the same as tip `i + 1`, tip `i`,
  tip `i + 1`. With `tip_tip` and `tip_comm` these are the laws of the group of
  the alcoves of SU(d + 1) (the affine Weyl group).
-/

namespace Roll

/-- A point of `d`-dimensional space: `d` whole numbers. -/
abbrev Pt (d : Nat) := Fin d → Int

/-- A simplex: `d + 1` corners, round a ring. -/
abbrev Simplex (d : Nat) := Fin (d + 1) → Pt d

variable {d : Nat}

/-- **Tip** the simplex over the face opposite corner `i`. -/
def tip (v : Simplex d) (i : Fin (d + 1)) : Simplex d :=
  Function.update v i (v (i - 1) + v (i + 1) - v i)

/-- The step into corner `k` from the corner before it. -/
def step (v : Simplex d) (k : Fin (d + 1)) : Pt d := v k - v (k - 1)

/-- The `d + 1` directions: the `d` unit directions, then minus all of them. -/
def dirs (d : Nat) (a : Fin (d + 1)) : Pt d :=
  fun c => if a.val < d then (if c.val = a.val then 1 else 0) else -1

/-- A proper simplex: its steps are the directions, each once. -/
def Proper (v : Simplex d) : Prop :=
  ∃ σ : Equiv.Perm (Fin (d + 1)), ∀ k, step v k = dirs d (σ k)

/-! ## 1. Corners round the ring are different, in dimension 1 and up -/

section ring
variable (i : Fin (d + 1))

theorem succ_ne (hd : 1 ≤ d) : i + 1 ≠ i := by
  intro h
  have : (1 : Fin (d + 1)) = 0 := by simpa using congrArg (· - i) h
  rw [Fin.one_eq_zero_iff] at this; omega

theorem pred_ne (hd : 1 ≤ d) : i - 1 ≠ i := by
  intro h
  exact succ_ne (i - 1) hd (by rw [sub_add_cancel]; exact h.symm)

theorem two_ne (hd : 2 ≤ d) : (1 : Fin (d + 1)) + 1 ≠ 0 := by
  rw [Ne, Fin.ext_iff, Fin.val_add, Fin.val_one', Fin.val_zero, Nat.one_mod_eq_one.mpr (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- Two steps round the ring never get back, in dimension 2 and up. -/
theorem succ_succ_ne (hd : 2 ≤ d) : i + 1 + 1 ≠ i := by
  intro h
  apply two_ne hd
  have : i + (1 + 1) = i + 0 := by rw [add_zero, ← add_assoc]; exact h
  exact add_left_cancel this

theorem succ_ne_pred (hd : 2 ≤ d) : i + 1 ≠ i - 1 := by
  intro h
  exact succ_succ_ne (i - 1) hd (by rw [sub_add_cancel]; exact h)

end ring

/-! ## 2. What a tip does -/

theorem tip_apply_self (v : Simplex d) (i : Fin (d + 1)) :
    tip v i i = v (i - 1) + v (i + 1) - v i := by simp [tip]

/-- Every corner but `i` stays put: the old and new simplex share the face
opposite `i`. -/
theorem tip_apply_ne (v : Simplex d) {i k : Fin (d + 1)} (h : k ≠ i) : tip v i k = v k := by
  simp [tip, h]

/-- The moving corner shifts by the step after it minus the step into it. -/
theorem tip_move (v : Simplex d) (i : Fin (d + 1)) :
    tip v i i - v i = step v (i + 1) - step v i := by
  simp only [tip_apply_self, step, add_sub_cancel_right]; abel

/-- **Tipping swaps two steps**: the step into `i` and the step after it
trade places. -/
theorem step_tip (hd : 1 ≤ d) (v : Simplex d) (i : Fin (d + 1)) :
    step (tip v i) = step v ∘ Equiv.swap i (i + 1) := by
  funext k
  simp only [Function.comp, step]
  by_cases hk : k = i
  · subst hk
    rw [Equiv.swap_apply_left, tip_apply_self, tip_apply_ne _ (pred_ne k hd), add_sub_cancel_right]
    abel
  by_cases hk' : k = i + 1
  · subst hk'
    rw [Equiv.swap_apply_right, add_sub_cancel_right, tip_apply_self,
      tip_apply_ne _ (succ_ne i hd)]
    abel
  · rw [Equiv.swap_apply_of_ne_of_ne hk hk', tip_apply_ne _ hk,
      tip_apply_ne _ (fun h => hk' (by rw [← h, sub_add_cancel]))]

/-- **A proper simplex tips into a proper simplex.** -/
theorem Proper.tip (hd : 1 ≤ d) {v : Simplex d} (hv : Proper v) (i : Fin (d + 1)) :
    Proper (Roll.tip v i) := by
  obtain ⟨σ, hσ⟩ := hv
  exact ⟨(Equiv.swap i (i + 1)).trans σ, fun k => by
    rw [step_tip hd]; simp [hσ]⟩

/-- **Each move is one lattice step**: in a proper simplex the moving corner
shifts by the difference of two different directions. -/
theorem Proper.move (hd : 1 ≤ d) {v : Simplex d} (hv : Proper v) (i : Fin (d + 1)) :
    ∃ a b, a ≠ b ∧ Roll.tip v i i - v i = dirs d a - dirs d b := by
  obtain ⟨σ, hσ⟩ := hv
  exact ⟨σ (i + 1), σ i, fun h => succ_ne i hd (σ.injective h), by rw [tip_move, hσ, hσ]⟩

/-! ## 3. Reversible, no order between far corners, and the braid law -/

/-- **Tipping twice at the same corner undoes it.** -/
theorem tip_tip (hd : 1 ≤ d) (v : Simplex d) (i : Fin (d + 1)) : tip (tip v i) i = v := by
  funext k
  by_cases hk : k = i
  · subst hk
    rw [tip_apply_self, tip_apply_self, tip_apply_ne _ (pred_ne k hd),
      tip_apply_ne _ (succ_ne k hd)]
    abel
  · rw [tip_apply_ne _ hk, tip_apply_ne _ hk]

/-- **Tips at corners that are not neighbours can happen in either order.** -/
theorem tip_comm (v : Simplex d) {i j : Fin (d + 1)} (h : j ≠ i) (h₁ : j ≠ i + 1)
    (h₂ : j ≠ i - 1) : tip (tip v i) j = tip (tip v j) i := by
  have h₁' : j - 1 ≠ i := fun e => h₁ (by rw [← e, sub_add_cancel])
  have h₂' : j + 1 ≠ i := fun e => h₂ (by rw [← e, add_sub_cancel_right])
  have h₃ : i - 1 ≠ j := fun e => h₂' (by rw [← e, sub_add_cancel])
  have h₄ : i + 1 ≠ j := fun e => h₁' (by rw [← e, add_sub_cancel_right])
  funext k
  by_cases hi : k = i
  · subst hi
    simp only [tip_apply_ne _ (Ne.symm h), tip_apply_self, tip_apply_ne _ h₃, tip_apply_ne _ h₄]
  by_cases hj : k = j
  · subst hj
    simp only [tip_apply_ne _ hi, tip_apply_self, tip_apply_ne _ h₁', tip_apply_ne _ h₂']
  · rw [tip_apply_ne _ hj, tip_apply_ne _ hi, tip_apply_ne _ hi, tip_apply_ne _ hj]

/-- **The braid law**, for neighbouring corners, in dimension 2 and up. -/
theorem tip_braid (hd : 2 ≤ d) (v : Simplex d) (i : Fin (d + 1)) :
    tip (tip (tip v i) (i + 1)) i = tip (tip (tip v (i + 1)) i) (i + 1) := by
  have h1 : 1 ≤ d := by omega
  have a₁ : i + 1 ≠ i := succ_ne i h1
  have a₂ : i - 1 ≠ i := pred_ne i h1
  have a₃ : i - 1 ≠ i + 1 := (succ_ne_pred i hd).symm
  have a₄ : i + 1 + 1 ≠ i + 1 := succ_ne (i + 1) h1
  have a₅ : i + 1 + 1 ≠ i := succ_succ_ne i hd
  funext k
  by_cases hi : k = i
  · subst hi
    simp only [tip_apply_self, tip_apply_ne _ a₁, tip_apply_ne _ a₁.symm, tip_apply_ne _ a₂,
      tip_apply_ne _ a₃, tip_apply_ne _ a₅, add_sub_cancel_right]
    abel
  by_cases hk : k = i + 1
  · subst hk
    simp only [tip_apply_self, tip_apply_ne _ a₁, tip_apply_ne _ a₁.symm,
      tip_apply_ne _ a₃, tip_apply_ne _ a₄, tip_apply_ne _ a₅, add_sub_cancel_right]
    abel
  · simp only [tip_apply_ne _ hi, tip_apply_ne _ hk]

/-! ## 4. Rolling

To **roll** forward, tip at corner 0 and then count the corners from the next
one round the ring, so that the next tip is again at corner 0. Rolling back
undoes it. Corner 0's step, the *seam*, decides where the simplex goes:
a roll keeps the seam and turns every other step one place round the ring
(`step_fwd`). So after `d` rolls the steps are back where they started, and
the simplex is itself again, moved one lattice step: minus the seam
(`straight_1` to `straight_4`). Forward and back, each of the `d + 1`
directions can be the seam, so there are `2 (d + 1)` ways to roll straight:
2 in a line (Zigzag's left and right), 6 in a plane, 8 in space. -/

/-- Roll forward: tip at corner 0, then count from the next corner. -/
def fwd (v : Simplex d) : Simplex d := fun k => tip v 0 (k + 1)

/-- Roll back: count from the corner before, then tip at corner 0. -/
def back (v : Simplex d) : Simplex d := tip (fun k => v (k - 1)) 0

theorem back_fwd (hd : 1 ≤ d) (v : Simplex d) : back (fwd v) = v := by
  have : (fun k => fwd v (k - 1)) = tip v 0 := by funext k; simp [fwd]
  rw [back, this, tip_tip hd]

theorem fwd_back (hd : 1 ≤ d) (v : Simplex d) : fwd (back v) = v := by
  funext k; simp only [fwd, back, tip_tip hd, add_sub_cancel_right]

/-- **A roll keeps the seam and turns the other steps**: the new step `k` is
the old step `k + 1`, except that the seam (step 0) stays, and the old step 1
comes last. -/
theorem step_fwd (hd : 1 ≤ d) (v : Simplex d) (k : Fin (d + 1)) :
    step (fwd v) k = step v (Equiv.swap 0 1 (k + 1)) := by
  have := congrFun (step_tip hd v 0) (k + 1)
  simp only [Function.comp, zero_add] at this
  rw [← this]; simp only [step, fwd, sub_add_cancel, add_sub_cancel_right]

/-- The seam is kept. -/
theorem seam_fwd (hd : 1 ≤ d) (v : Simplex d) : step (fwd v) 0 = step v 0 := by
  rw [step_fwd hd, zero_add, Equiv.swap_apply_right]

/-! ## 5. Rolling straight, checked in dimensions 1 to 4 -/

/-- The simplex with corner 0 at the origin whose steps, from corner 1 on, are
the directions `l` (the seam is then what closes the loop). -/
def kuhn (d : Nat) (l : List (Fin (d + 1))) : Simplex d :=
  fun k => ((l.drop 1).take k.val).foldl (fun p a => p + dirs d a) 0

/-- Its seam: the direction `l` starts with. -/
def seam (d : Nat) (l : List (Fin (d + 1))) : Pt d := dirs d (l.headD 0)

/-- Every list of `k` labels. -/
def words (n : Nat) : Nat → List (List (Fin n))
  | 0 => [[]]
  | k + 1 => (words n k).flatMap fun w => (List.finRange n).map (· :: w)

/-- Every order of the `d + 1` directions: one proper simplex for each. -/
def orders (d : Nat) : List (List (Fin (d + 1))) := (words (d + 1) (d + 1)).filter (·.Nodup)

/-- Two simplices have the same corners (a check Lean can run). -/
def same (v w : Simplex d) : Bool :=
  (List.finRange (d + 1)).all fun k => (List.finRange d).all fun c => v k c == w k c

theorem same_iff (v w : Simplex d) : same v w = true ↔ v = w := by
  simp only [same, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
  exact ⟨fun h => funext fun k => funext fun c => h k c, fun h k c => by rw [h]⟩

/-- `d` rolls take every proper simplex to itself, moved by minus its seam. -/
def Straight (d : Nat) : Prop :=
  ∀ l ∈ orders d, fwd^[d] (kuhn d l) = fun k => kuhn d l k - seam d l

instance (d : Nat) : Decidable (Straight d) :=
  decidable_of_iff (∀ l ∈ orders d, same (fwd^[d] (kuhn d l)) (fun k => kuhn d l k - seam d l))
    (by simp only [Straight, same_iff])

theorem orders_length : (orders 1).length = 2 ∧ (orders 2).length = 6 ∧
    (orders 3).length = 24 ∧ (orders 4).length = 120 := by decide +kernel

/-- The steps of `kuhn d l` are the directions in `l`, in order, seam first:
each is a proper simplex. (Checked in dimension 3.) -/
theorem kuhn_steps : ∀ l ∈ orders 3, (List.finRange 4).all fun k =>
    (List.finRange 3).all fun c => step (kuhn 3 l) k c == dirs 3 (l.getD k 0) c := by
  decide +kernel

theorem straight_1 : Straight 1 := by decide +kernel
theorem straight_2 : Straight 2 := by decide +kernel
theorem straight_3 : Straight 3 := by decide +kernel
theorem straight_4 : Straight 4 := by decide +kernel

end Roll
