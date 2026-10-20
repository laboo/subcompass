import Subcompass.Roll

/-!
# Roll, part 1½: places in three dimensions

`Roll.lean` gives the motion in any dimension. Here it is written out for
three, with whole-number points `⟨x, y, z⟩`, so that Lean can run examples
quickly. A *place* is a tetrahedron: four corners round a ring, corner `c₀`
first. Its steps go round the ring; it is *proper* when they are the four
directions `dirs`, each once.

* `fwd` rolls forward: tip at `c₀` (Roll's rule, corner before + corner after
  − itself) and count from the next corner. `back` undoes it (`back_fwd`,
  `fwd_back`).
* The *distance* between places is how far apart their centres are, in whole
  steps of the lattice: half the spread of the coordinates of the difference
  of their corner sums, rounded up (`dist`). It obeys the triangle law
  (`dist_tri`), and a roll from a proper place moves exactly one step
  (`dist_move`).
-/

namespace RollWorld
/-- A point of 3D space. -/
@[ext]
structure Pt where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr

namespace Pt
instance : Zero Pt := ⟨⟨0, 0, 0⟩⟩
instance : Add Pt := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩⟩
instance : Sub Pt := ⟨fun a b => ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩⟩
@[simp] theorem add_def (a b : Pt) : a + b = ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩ := rfl
@[simp] theorem sub_def (a b : Pt) : a - b = ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩ := rfl
end Pt

/-- A tetrahedron: four corners round a ring, `c₀` first. -/
structure Place where
  c₀ : Pt
  c₁ : Pt
  c₂ : Pt
  c₃ : Pt
  deriving DecidableEq, Repr

namespace Place

/-- The four directions: three unit directions and minus all of them. -/
def dirs : List Pt := [⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩, ⟨-1, -1, -1⟩]
/-- The steps round the ring, into `c₀`, `c₁`, `c₂`, `c₃`. -/
def steps (P : Place) : List Pt := [P.c₀ - P.c₃, P.c₁ - P.c₀, P.c₂ - P.c₁, P.c₃ - P.c₂]
/-- Proper: the steps are the four directions, each once. -/
def proper (P : Place) : Bool := P.steps.all (· ∈ dirs) && decide P.steps.Nodup
/-- Tip over the face opposite `c₀`. -/
def tip (P : Place) : Place := { P with c₀ := P.c₃ + P.c₁ - P.c₀ }
/-- Roll forward: tip at `c₀`, then count from the next corner (`Roll.fwd`). -/
def fwd (P : Place) : Place := ⟨P.c₁, P.c₂, P.c₃, P.c₃ + P.c₁ - P.c₀⟩
/-- Roll back: count from the corner before, then tip at `c₀` (`Roll.back`). -/
def back (P : Place) : Place := tip ⟨P.c₃, P.c₀, P.c₁, P.c₂⟩
def move (P : Place) (f : Bool) : Place := if f then P.fwd else P.back
/-- The corners added up: four times the centre. -/
def sum (P : Place) : Pt := P.c₀ + P.c₁ + P.c₂ + P.c₃
/-- The spread of a point's coordinates, counting 0 as a coordinate: the
lattice's own length, the same for all four directions and their differences. -/
def hexN (p : Pt) : Int := max (max (max p.x p.y) p.z) 0 - min (min (min p.x p.y) p.z) 0
/-- How many lattice steps apart two places are. -/
def dist (P Q : Place) : Nat := ((hexN (P.sum - Q.sum)).toNat + 1) / 2

theorem back_fwd (P : Place) : P.fwd.back = P := by
  rcases P with ⟨⟨a, b, c⟩, ⟨d, e, f⟩, ⟨g, h, i⟩, ⟨j, k, l⟩⟩
  simp only [fwd, back, tip, Pt.add_def, Pt.sub_def, Place.mk.injEq, Pt.mk.injEq, and_true]
  omega

theorem fwd_back (P : Place) : P.back.fwd = P := by
  rcases P with ⟨⟨a, b, c⟩, ⟨d, e, f⟩, ⟨g, h, i⟩, ⟨j, k, l⟩⟩
  simp only [fwd, back, tip, Pt.add_def, Pt.sub_def, Place.mk.injEq, Pt.mk.injEq, true_and]
  omega
/-- The largest coordinate, or 0. -/
def hi (p : Pt) : Int := max (max (max p.x p.y) p.z) 0
/-- The smallest coordinate, or 0. -/
def lo (p : Pt) : Int := min (min (min p.x p.y) p.z) 0

theorem hexN_eq (p : Pt) : hexN p = hi p - lo p := rfl

theorem hi_add (p q : Pt) : hi (p + q) ≤ hi p + hi q := by
  have h₁ : p.x ≤ hi p ∧ p.y ≤ hi p ∧ p.z ≤ hi p ∧ 0 ≤ hi p := by simp only [hi]; omega
  have h₂ : q.x ≤ hi q ∧ q.y ≤ hi q ∧ q.z ≤ hi q ∧ 0 ≤ hi q := by simp only [hi]; omega
  simp only [hi, Pt.add_def]
  generalize hi p = a at h₁; generalize hi q = b at h₂
  omega

theorem lo_add (p q : Pt) : lo p + lo q ≤ lo (p + q) := by
  have h₁ : lo p ≤ p.x ∧ lo p ≤ p.y ∧ lo p ≤ p.z ∧ lo p ≤ 0 := by simp only [lo]; omega
  have h₂ : lo q ≤ q.x ∧ lo q ≤ q.y ∧ lo q ≤ q.z ∧ lo q ≤ 0 := by simp only [lo]; omega
  simp only [lo, Pt.add_def]
  generalize lo p = a at h₁; generalize lo q = b at h₂
  omega

theorem hexN_add (x y : Pt) : hexN (x + y) ≤ hexN x + hexN y := by
  simp only [hexN_eq]; have := hi_add x y; have := lo_add x y; omega

theorem hexN_nonneg (p : Pt) : 0 ≤ hexN p := by
  have : 0 ≤ hi p := by simp only [hi]; omega
  have : lo p ≤ 0 := by simp only [lo]; omega
  rw [hexN_eq]; omega
theorem dist_tri (P Q R : Place) : dist P R ≤ dist P Q + dist Q R := by
  have := hexN_add (P.sum - Q.sum) (Q.sum - R.sum)
  have e : P.sum - Q.sum + (Q.sum - R.sum) = P.sum - R.sum := by
    ext <;> simp only [Pt.add_def, Pt.sub_def] <;> omega
  rw [e] at this
  have := hexN_nonneg (P.sum - Q.sum); have := hexN_nonneg (Q.sum - R.sum)
  simp only [dist]; omega
/-- Two different directions are one step apart. -/
theorem hexN_root : ∀ x ∈ dirs, ∀ y ∈ dirs, x ≠ y → hexN (x - y) = 2 := by decide
theorem dist_self (P : Place) : dist P P = 0 := by
  have : P.sum - P.sum = 0 := by ext <;> simp only [Pt.sub_def, sub_self] <;> rfl
  simp only [dist, this]; decide

theorem proper_facts {P : Place} (h : P.proper = true) :
    P.c₀ - P.c₃ ∈ dirs ∧ P.c₁ - P.c₀ ∈ dirs ∧ P.c₃ - P.c₂ ∈ dirs ∧
      P.c₀ - P.c₃ ≠ P.c₁ - P.c₀ ∧ P.c₀ - P.c₃ ≠ P.c₃ - P.c₂ := by
  simp only [proper, steps, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, List.nodup_cons,
    not_or] at h
  exact ⟨h.1.1, h.1.2.1, h.1.2.2.2, h.2.1.1, h.2.1.2.2⟩

theorem dist_root {P Q : Place} {x y : Pt} (hx : x ∈ dirs) (hy : y ∈ dirs) (hxy : x ≠ y)
    (h : P.sum - Q.sum = x - y) : dist P Q = 1 := by
  simp only [dist, h, hexN_root x hx y hy hxy]; decide

/-- A tip moves a proper tetrahedron one step. -/
theorem dist_move {P : Place} (hP : P.proper = true) (f : Bool) :
    dist P (P.move f) ≤ 1 ∧ dist (P.move f) P ≤ 1 := by
  obtain ⟨h₀, h₁, h₃, n₁, n₃⟩ := proper_facts hP
  rcases P with ⟨⟨a, b, c⟩, ⟨d, e, f'⟩, ⟨g, h, i⟩, ⟨j, k, l⟩⟩
  cases f
  · refine ⟨Nat.le_of_eq (dist_root h₃ h₀ (Ne.symm n₃) ?_), Nat.le_of_eq (dist_root h₀ h₃ n₃ ?_)⟩ <;>
      ext <;> simp only [move, back, tip, sum, Pt.add_def, Pt.sub_def] <;> simp <;> omega
  · refine ⟨Nat.le_of_eq (dist_root h₀ h₁ n₁ ?_), Nat.le_of_eq (dist_root h₁ h₀ (Ne.symm n₁) ?_)⟩ <;>
      ext <;> simp only [move, fwd, sum, Pt.add_def, Pt.sub_def] <;> simp <;> omega

end Place
end RollWorld
