/-!
# OSM, our standard model, written out in Lean

Team 3, Generation 0 (3:0), for the Grader.
Checked with Lean 4.35.0 (`lake build` passes with no errors or warnings),
core library only (no Mathlib is needed). To check it yourself, see README.md.

## How to read this file

Lean is a programming language with a strict checker. It refuses any
definition that does not give an answer for every possible input, and any
proof that is not airtight. Text between `/-` and `-/`, and lines starting
with `--`, are plain English for people; everything else is for the checker.

Every rule below carries a tag:

* **[Model]**: stated in The Model file.
* **[Reading]**: what a sentence of The Model forces once it is written exactly.
* **[Gap k]**: something The Model leaves open, filled by Team 3's choice,
  numbered as in the list below. These are proposals: not approved, and not
  in The Model.

Nothing untagged decides anything; untagged code only reports (readouts) or
checks (theorems and examples).

## What The Model says (the starting point)

Points have one of two values, ⊕ = +1 and ⊖ = −1. The origin starts as a
loose bag of points, nothing bound. × binds points and carries a thing into
the next dimension; a thing in n dimensions is made of n + 1 points; order
counts, even for like points. In 1D the value is [+] or [−], as in The
Model's table. + joins things within a dimension. The anti-matter twin flips
every ⊕ and ⊖. Geometry is Euclidean, and every object has a container.

## The gaps and Team 3's fills

1. **× past 1D.** × binds a thing to one more point from the bag, which goes
   last in its order. A bag point counts as a 0D thing, so this is also how a
   segment is made. Why: × keeps every point, so this is the only reading that
   keeps both "× carries a thing into the next dimension" and "a thing in
   n dimensions is n + 1 points".
2. **Value.** A thing's value is the product of its points, (±1)ⁿ for an
   n-dimensional thing. Why: it is The Model's 1D table, unchanged.
3. **Hand.** Nothing is stored about which side a new point lands on; a
   thing's hand is its order, and its mirror image is the same points in an
   odd reordering. Why: The Model already gives order; a stored side would be
   a second property. Consequence: no rule below reads a thing's order, so
   in OSM the hand never changes what happens (section 10 proves this for
   undoing; for the other rules it can be seen by reading them).
4. **Containers.** There is a container for every dimension, with no top.
   Only which points share a place is kept, never distances or coordinates,
   so no √2 is ever computed. Why: The Model's "in general, n dimensions"
   names no limit, and a limit would be an added rule. Any pattern of shared
   places can be drawn with straight lines in the right container (a standard
   fact of geometry, not proved here), so nothing the rules use is lost.
5. **Touch.** Two points touch when they share a place. A thing's own points
   never share a place; a place lies in one container, so everything touching
   there has the same dimension; the bag's points are all together at the
   origin. Why: "addition joins things within a dimension", and n + 1 points
   spanning n dimensions can't have two at one spot.
6. **Addition.** + brings points of different things in one container to one
   place, any number of pairs at once (laying one thing on another). The
   place keeps every point, with no order among them; the sum is only its
   flattened total. Why: the Handoff's addition candidate.
7. **Undoing.** Right after any × or +, every bound point at a place holding
   both a ⊕ and a ⊖ comes unbound, all at once, and goes back to the bag; its
   thing drops one dimension per point lost, and a thing left with one point
   dissolves into the bag. Like points (⊕ + ⊕) stay joined. Why: the
   Handoff's annihilation candidate ("multiplication undone"); freed points
   go to the bag because unbound points are 0D, and 0D points live at the
   origin, so a (⊕ + ⊖) pair does not fly off as a separate object.
8. **Dynamics.** The only events are × and +, in whatever order a setup
   chooses, each followed at once by 7. Nothing happens by itself, and there
   is no clock, only the order of events. An event can happen exactly when its
   result is a world The Model allows. Why: × and + are the only operations
   The Model names, and the Handoff's decision that "the geometry itself must
   decide when contact triggers collapse".

Gaps the Lean work exposed, which the first list of eight missed:

9. **One thing per point.** A point is in at most one thing, so × takes only
   bag points; things share a corner by bringing two points together (6),
   never by sharing one point. Why: + keeps every part, so a shared corner
   holds two points.
10. **Joins hold (no subtraction).** Nothing pulls joined points apart except
    7, or a thing leaving its container (11). Why: The Model names no
    un-joining, and the Handoff has like points join.
11. **Changing container.** A thing that changes container, by × or by losing
    a point, arrives in the new one touching nothing. Why: a place lies in one
    container (5).

Readings, not choices:

* **Points are individuals**, each with its own name. "Order counts, even for
  ⊕ × ⊕ swapped" is only true if the two ⊕ can be told apart.
* **A world holds finitely many points** at any moment, as many as a setup
  wants; the origin's unlimited capacity is never used up.

## What is checked below

* Every world and every event has exactly one outcome, a new world or "can't
  happen", and nothing is assumed beyond Lean's own logic (section 11).
* The definitions match The Model's text: the 1D value table, order counting
  for all six 1D lines, × raising the dimension by one, twin of twin.
* Points are never made or destroyed, so the count and total sum of a world
  never change.
* Every event leaves a world The Model allows.
* After every event, no bound point shares a place with an opposite one: one
  round of unbinding always finishes the job, with nothing left to cascade.
* A world and its twin obey the same rules: whatever happens to one happens,
  flipped, to the other.
* Which points come unbound depends only on which signs share a place, never
  on any thing's order, so never on its hand.
* Worked examples: a segment laid on its twin, like ends joined, and a
  triangle touching an opposite point at one corner.
-/

namespace OSM

/-! ## 1. Points -/

/-- [Model] Every 0D point is ⊕ (`pos`, the value +1 = (+1)⁰) or ⊖ (`neg`,
the value −1 = (−1)⁰). -/
inductive Sign where
  | pos
  | neg
  deriving DecidableEq, Repr

namespace Sign

/-- A sign as an ordinary number: ⊕ is +1, ⊖ is −1. -/
def toInt : Sign → Int
  | pos => 1
  | neg => -1

/-- [Model] The twin flips ⊕ and ⊖. -/
def flip : Sign → Sign
  | pos => neg
  | neg => pos

/-- Multiplying two values. -/
def mul : Sign → Sign → Sign
  | pos, s => s
  | neg, s => s.flip

theorem flip_flip (s : Sign) : s.flip.flip = s := by cases s <;> rfl

/-- `mul` is ordinary multiplication of +1 and −1: this is plain arithmetic. -/
theorem toInt_mul (a b : Sign) : (a.mul b).toInt = a.toInt * b.toInt := by
  cases a <;> cases b <;> decide

end Sign

/-! ## 2. Worlds

[Reading] Points are individuals: point number `i` has sign `signs[i]`.
[Reading] A world holds finitely many points, as many as a setup wants. -/

/-- What is bound and what touches. -/
structure Shape where
  /-- [Model] Each thing is an ordered list of points bound by ×; order
  counts. A thing of n + 1 points is n-dimensional and lives in the
  n-dimensional container [Gap 4]. Points in no thing are in the bag. The
  order in which things are listed is bookkeeping; only the order inside a
  thing counts. -/
  things : List (List Nat)
  /-- [Gaps 5, 6] Each place lists the points brought to one location by +.
  A point in no place touches nothing; bag points are all at the origin and
  are never listed. The order inside a place is bookkeeping: no rule reads it. -/
  places : List (List Nat)
  deriving DecidableEq, Repr

/-- A world: the points and their signs, which never change, and its shape. -/
structure World where
  signs : List Sign
  shape : Shape
  deriving DecidableEq, Repr

/-- [Model] At the start the origin holds a loose bag of points, nothing bound. -/
def World.start (bag : List Sign) : World := ⟨bag, ⟨[], []⟩⟩

/-- [Model] The twin: every ⊕ and ⊖ flipped, everything else the same. -/
def World.twin (w : World) : World := { w with signs := w.signs.map Sign.flip }

/-- [Model, Gap 8] The two operations, the only events. -/
inductive Event where
  /-- `bind p q` is p × q [Gap 1]: bag point `q` is bound onto the thing that
  holds `p` (onto `p` itself if `p` is in the bag) and goes last. -/
  | bind (p q : Nat)
  /-- `join pairs` is + [Gap 6]: for every pair (a, b), a and b are brought to
  one place, all pairs at once. -/
  | join (pairs : List (Nat × Nat))
  deriving DecidableEq, Repr

/-! ## 3. What may exist -/

/-- What may exist in a world of `n` points. An event can happen only if its
result passes this test [Gap 8]. -/
abbrev WF (n : Nat) (sh : Shape) : Prop :=
  -- [Model] a thing is at least a segment (a lone point is a bag point)
  (∀ t ∈ sh.things, 2 ≤ t.length) ∧
  -- [Reading] every point named is one of the world's points
  (∀ t ∈ sh.things, ∀ i ∈ t, i < n) ∧
  -- [Gap 9] a point is in at most one thing, and appears in it once
  sh.things.flatten.Nodup ∧
  -- [Gap 6] a place holds at least two points
  (∀ g ∈ sh.places, 2 ≤ g.length) ∧
  -- [Gap 5] only bound points are at places (bag points are at the origin)
  (∀ g ∈ sh.places, ∀ i ∈ g, ∃ t ∈ sh.things, i ∈ t) ∧
  -- [Gap 5] a point is at one place only
  sh.places.flatten.Nodup ∧
  -- [Gap 5] a thing's own points never share a place
  (∀ g ∈ sh.places, ∀ t ∈ sh.things, ∀ i ∈ g, ∀ j ∈ g, i ∈ t → j ∈ t → i = j) ∧
  -- [Model "addition joins things within a dimension", Gap 5] a place lies in
  -- one container: everything touching there has the same dimension
  (∀ g ∈ sh.places, ∀ i ∈ g, ∀ j ∈ g, ∀ t ∈ sh.things, ∀ u ∈ sh.things,
    i ∈ t → j ∈ u → t.length = u.length)

-- The option below only lets Lean's instance search handle a conjunction of
-- eight parts; it changes no rule.
set_option synthInstance.maxSize 1024 in
/-- Each test above can be checked mechanically, so whether a world is allowed
is always decided. -/
instance instDecidableWF (n : Nat) (sh : Shape) : Decidable (WF n sh) := by
  unfold WF; infer_instance

/-! ## 4. The two operations, before undoing -/

/-- Keep the points of `l` that pass `keep`; if fewer than two are left, the
list is gone: a thing of one point is a bag point [Gap 7], and a place of one
point touches nothing [Gap 6]. -/
def shrink (keep : Nat → Bool) (l : List Nat) : Option (List Nat) :=
  if 2 ≤ (l.filter keep).length then some (l.filter keep) else none

/-- × [Gaps 1, 9, 11]: bag point `q` goes last onto the thing holding `p`
(or onto `p` itself). The grown thing is in a new container, so it arrives
touching nothing. -/
def Shape.bindRaw (sh : Shape) (p q : Nat) : Shape :=
  let base := (sh.things.find? fun t => decide (p ∈ t)).getD [p]
  let new := base ++ [q]
  { things := (sh.things.filter fun t => !decide (p ∈ t)) ++ [new]
    places := sh.places.filterMap (shrink fun i => !decide (i ∈ new)) }

/-- + for one pair [Gaps 6, 10]: the places of `a` and `b` become one place.
Joins hold, so everything already at either place comes along. -/
def Shape.joinPair (sh : Shape) (ab : Nat × Nat) : Shape :=
  let ga := (sh.places.find? fun g => decide (ab.1 ∈ g)).getD [ab.1]
  let gb := (sh.places.find? fun g => decide (ab.2 ∈ g)).getD [ab.2]
  if ab.2 ∈ ga then sh
  else { sh with places :=
    (sh.places.filter fun g => !decide (ab.1 ∈ g) && !decide (ab.2 ∈ g)) ++ [ga ++ gb] }

/-- + for several pairs at once [Gap 6]. -/
def Shape.joinRaw (sh : Shape) (pairs : List (Nat × Nat)) : Shape :=
  pairs.foldl Shape.joinPair sh

/-- The direct effect of an event, before undoing. -/
def Shape.raw (sh : Shape) : Event → Shape
  | .bind p q => sh.bindRaw p q
  | .join pairs => sh.joinRaw pairs

/-! ## 5. Undoing [Gap 7] -/

/-- `opp signs i j`: points `i` and `j` have opposite signs. -/
def opp (signs : List Sign) (i j : Nat) : Bool :=
  match signs[i]?, signs[j]? with
  | some a, some b => a != b
  | _, _ => false

/-- A place is mixed when it holds both a ⊕ and a ⊖. -/
def mixed (op : Nat → Nat → Bool) (g : List Nat) : Bool :=
  g.any fun i => g.any fun j => op i j

/-- [Gap 7] The struck points: every point at a mixed place. -/
def struck (op : Nat → Nat → Bool) (sh : Shape) : List Nat :=
  (sh.places.filter (mixed op)).flatten

/-- A thing is hit when it holds a struck point. -/
def hit (op : Nat → Nat → Bool) (sh : Shape) (t : List Nat) : Bool :=
  t.any fun i => decide (i ∈ struck op sh)

/-- Every point of a hit thing: it leaves its container [Gap 11]. -/
def moved (op : Nat → Nat → Bool) (sh : Shape) : List Nat :=
  (sh.things.filter (hit op sh)).flatten

/-- A point stays at its place unless it was struck or its thing moved. -/
def stays (op : Nat → Nat → Bool) (sh : Shape) (i : Nat) : Bool :=
  !decide (i ∈ struck op sh) && !decide (i ∈ moved op sh)

/-- [Gaps 7, 11] All struck points come unbound at once and go back to the
bag; each hit thing keeps its other points, in order, one dimension lower per
point lost, arriving touching nothing; with one point left it dissolves into
the bag. Unhit things and their places stay. -/
def settle (op : Nat → Nat → Bool) (sh : Shape) : Shape :=
  { things := sh.things.filterMap fun t =>
      if hit op sh t then shrink (fun i => !decide (i ∈ struck op sh)) t else some t
    places := sh.places.filterMap (shrink (stays op sh)) }

/-! ## 6. One step [Gap 8] -/

/-- An event happens exactly when its direct effect is a world The Model
allows; then undoing follows at once. `none` means "can't happen here". -/
def stepShape (n : Nat) (op : Nat → Nat → Bool) (sh : Shape) (e : Event) :
    Option Shape :=
  if WF n (sh.raw e) then some (settle op (sh.raw e)) else none

/-- One event in a world. Only the shape can change, never the points. -/
def World.step (w : World) (e : Event) : Option World :=
  (stepShape w.signs.length (opp w.signs) w.shape e).map fun sh => { w with shape := sh }

/-- A history: events one after another. There is no clock, only this order. -/
def World.run (w : World) : List Event → Option World
  | [] => some w
  | e :: es =>
    match w.step e with
    | none => none
    | some w' => w'.run es

/-! ## 7. Readouts (measurements of the model; no rule uses them) -/

/-- The signs of a list of points, in order. -/
def World.signsOf (w : World) (l : List Nat) : List Sign :=
  l.filterMap fun i => w.signs[i]?

/-- The points in the bag (bound in no thing). -/
def World.bag (w : World) : List Nat :=
  (List.range w.signs.length).filter fun i => !w.shape.things.any fun t => decide (i ∈ t)

/-- Dimension: a thing of n + 1 points is n-dimensional. -/
def dim (t : List Nat) : Nat := t.length - 1

/-- [Gap 2] Value: the product of a thing's signs, (±1)ⁿ. -/
def value (ss : List Sign) : Sign := ss.foldl Sign.mul .pos

/-- The flattened sum of a list of signs. -/
def total (ss : List Sign) : Int := (ss.map Sign.toInt).sum

/-- Each thing as its ordered signs. -/
def World.thingSigns (w : World) : List (List Sign) := w.shape.things.map w.signsOf

/-- Each place as the signs gathered there. -/
def World.placeSigns (w : World) : List (List Sign) := w.shape.places.map w.signsOf

/-- What an event releases: each mixed place, as the signs that came unbound
together there, for example a (⊕ + ⊖) pair. -/
def World.released (w : World) (e : Event) : List (List Sign) :=
  ((w.shape.raw e).places.filter (mixed (opp w.signs))).map w.signsOf

/-! ## 8. The template every team's model fills

A model is: its kind of world, its kind of event, how a world starts from a
loose bag of points, what one event does (`none` = can't happen), and what a
test may look at. OSM is one filling; every rival model is another, so a test that
looks at the bag and the things can be written once for every model. -/

structure ArithModel where
  World : Type
  Event : Type
  start : List Sign → World
  step : World → Event → Option World
  bag : World → List Sign
  things : World → List (List Sign)

/-- A history in any model. -/
def ArithModel.run (M : ArithModel) (w : M.World) : List M.Event → Option M.World
  | [] => some w
  | e :: es =>
    match M.step w e with
    | none => none
    | some w' => M.run w' es

/-- OSM as a filling of the template. -/
def osm : ArithModel where
  World := World
  Event := Event
  start := World.start
  step := World.step
  bag w := w.signsOf w.bag
  things w := w.thingSigns

/-! ## 9. Checks against The Model's text -/

section ModelChecks
open Sign

/-- [Model] The 1D table: ⊕×⊕ and ⊖×⊖ are [+], ⊕×⊖ and ⊖×⊕ are [−]. -/
example : value [pos, pos] = pos ∧ value [neg, neg] = pos ∧
    value [pos, neg] = neg ∧ value [neg, pos] = neg := by decide

/-- [Model] Order counts: from any two points, × makes two different things,
one per order, even when the signs are alike ("identical twins switching
places"). This covers all six lines of The Model's 1D list. -/
theorem order_counts (s t : Sign) :
    (World.start [s, t]).step (.bind 0 1) ≠ (World.start [s, t]).step (.bind 1 0) := by
  cases s <;> cases t <;> decide

/-- [Model] × makes a segment from two bag points. -/
example : (World.start [pos, neg]).step (.bind 0 1)
    = some ⟨[pos, neg], ⟨[[0, 1]], []⟩⟩ := by decide

/-- [Model, Gap 1] × carries a thing into the next dimension: a segment
(1D) bound to one more point becomes a triangle (2D), then a tetrahedron (3D). -/
example : ((World.start [neg, neg, neg, pos]).run [.bind 0 1, .bind 0 2, .bind 0 3]).map
      (fun w => w.shape.things.map dim) = some [3] := by decide

/-- [Model] The twin of the twin is the original. -/
theorem twin_twin (w : World) : w.twin.twin = w := by
  cases w with
  | mk signs shape =>
    simp only [World.twin, List.map_map]
    have : Sign.flip ∘ Sign.flip = id := funext Sign.flip_flip
    rw [this, List.map_id]

/-- [Gap 1] × always raises the dimension by exactly one. -/
theorem dim_bind (t : List Nat) (q : Nat) (h : t ≠ []) : dim (t ++ [q]) = dim t + 1 := by
  cases t with
  | nil => exact absurd rfl h
  | cons a l => simp [dim]

end ModelChecks

/-! ## 10. Proved properties -/

section Proofs

/-! ### Points are never made or destroyed -/

theorem step_signs {w w' : World} {e : Event} (h : w.step e = some w') :
    w'.signs = w.signs := by
  simp only [World.step, Option.map_eq_some_iff] at h
  obtain ⟨sh, _, rfl⟩ := h
  rfl

/-- So the number of points and their total sum never change. -/
theorem step_count_and_total {w w' : World} {e : Event} (h : w.step e = some w') :
    w'.signs.length = w.signs.length ∧ total w'.signs = total w.signs := by
  rw [step_signs h]; exact ⟨rfl, rfl⟩

/-! ### Matter and anti-matter obey the same rules -/

theorem opp_twin (signs : List Sign) (i j : Nat) :
    opp (signs.map Sign.flip) i j = opp signs i j := by
  unfold opp
  rw [List.getElem?_map, List.getElem?_map]
  cases signs[i]? with
  | none => rfl
  | some a =>
    cases signs[j]? with
    | none => rfl
    | some b => cases a <;> cases b <;> rfl

/-- Whatever an event does to a world, it does, flipped, to the twin. -/
theorem step_twin (w : World) (e : Event) : w.twin.step e = (w.step e).map World.twin := by
  have h : opp (w.signs.map Sign.flip) = opp w.signs := by
    funext i j; exact opp_twin w.signs i j
  simp only [World.step, World.twin, h, List.length_map, Option.map_map]
  rfl

/-! ### Which points come unbound never depends on order (or hand) -/

/-- The struck points are read off the places alone: replacing every thing,
or reordering any of them, changes nothing about what comes unbound. -/
theorem struck_ignores_things (op : Nat → Nat → Bool) (sh : Shape) (ts : List (List Nat)) :
    struck op { sh with things := ts } = struck op sh := rfl

/-! ### Helper facts about lists -/

theorem shrink_eq {keep : Nat → Bool} {l l' : List Nat} (h : shrink keep l = some l') :
    l' = l.filter keep ∧ 2 ≤ l'.length := by
  unfold shrink at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

theorem flatten_filterMap_sublist {f : List Nat → Option (List Nat)}
    (hf : ∀ x y, f x = some y → y.Sublist x) :
    ∀ l : List (List Nat), (l.filterMap f).flatten.Sublist l.flatten
  | [] => by simp
  | x :: xs => by
    have ih := flatten_filterMap_sublist hf xs
    rw [List.filterMap_cons]
    cases h : f x with
    | none =>
      simp only [List.flatten_cons]
      exact ih.trans (List.sublist_append_right x _)
    | some y =>
      simp only [List.flatten_cons]
      exact (hf x y h).append ih

theorem shrink_sublist (keep : Nat → Bool) (x y : List Nat) (h : shrink keep x = some y) :
    y.Sublist x := by
  rw [(shrink_eq h).1]; exact List.filter_sublist

theorem mixed_mono {op : Nat → Nat → Bool} {g g' : List Nat} (sub : ∀ x ∈ g', x ∈ g)
    (h : mixed op g' = true) : mixed op g = true := by
  simp only [mixed, List.any_eq_true] at h ⊢
  obtain ⟨i, hi, j, hj, hij⟩ := h
  exact ⟨i, sub i hi, j, sub j hj, hij⟩

theorem mem_struck {op : Nat → Nat → Bool} {sh : Shape} {g : List Nat} {i : Nat}
    (hg : g ∈ sh.places) (hm : mixed op g = true) (hi : i ∈ g) : i ∈ struck op sh := by
  simp only [struck, List.mem_flatten, List.mem_filter]
  exact ⟨g, ⟨hg, hm⟩, hi⟩

theorem mem_moved {op : Nat → Nat → Bool} {sh : Shape} {t : List Nat} {i : Nat}
    (ht : t ∈ sh.things) (hh : hit op sh t = true) (hi : i ∈ t) : i ∈ moved op sh := by
  simp only [moved, List.mem_flatten, List.mem_filter]
  exact ⟨t, ⟨ht, hh⟩, hi⟩

/-- A point that stays is not in a hit thing. -/
theorem not_hit_of_stays {op : Nat → Nat → Bool} {sh : Shape} {t : List Nat} {i : Nat}
    (ht : t ∈ sh.things) (hi : i ∈ t) (hs : stays op sh i = true) : hit op sh t = false := by
  cases hh : hit op sh t with
  | false => rfl
  | true =>
    have := mem_moved ht hh hi
    simp [stays, this] at hs

/-- Where each new thing came from: part of an old thing, or an old thing
left whole because it was not hit. -/
theorem mem_settle_things {op : Nat → Nat → Bool} {sh : Shape} {t' : List Nat}
    (h : t' ∈ (settle op sh).things) :
    ∃ t ∈ sh.things, t'.Sublist t ∧ (hit op sh t = false → t' = t) ∧
      (hit op sh t = true → 2 ≤ t'.length) := by
  simp only [settle, List.mem_filterMap] at h
  obtain ⟨t, ht, hf⟩ := h
  by_cases hh : hit op sh t = true
  · simp only [hh, ↓reduceIte] at hf
    refine ⟨t, ht, shrink_sublist _ _ _ hf, fun hf' => ?_, fun _ => (shrink_eq hf).2⟩
    rw [hh] at hf'; cases hf'
  · simp only [hh] at hf
    cases hf
    exact ⟨t', ht, List.Sublist.refl _, fun _ => rfl, fun h' => absurd h' hh⟩

/-- An old thing that was not hit is still there, whole. -/
theorem mem_settle_of_not_hit {op : Nat → Nat → Bool} {sh : Shape} {t : List Nat}
    (ht : t ∈ sh.things) (hh : hit op sh t = false) : t ∈ (settle op sh).things := by
  simp only [settle, List.mem_filterMap]
  exact ⟨t, ht, by simp [hh]⟩

/-- Where each new place came from: the points of an old place that stayed. -/
theorem mem_settle_places {op : Nat → Nat → Bool} {sh : Shape} {g' : List Nat}
    (h : g' ∈ (settle op sh).places) :
    ∃ g ∈ sh.places, g' = g.filter (stays op sh) ∧ 2 ≤ g'.length := by
  simp only [settle, List.mem_filterMap] at h
  obtain ⟨g, hg, hf⟩ := h
  exact ⟨g, hg, (shrink_eq hf).1, (shrink_eq hf).2⟩

/-! ### Undoing finishes in one round -/

/-- After undoing, no place is mixed. -/
theorem settle_unmixed (op : Nat → Nat → Bool) (sh : Shape) :
    ∀ g' ∈ (settle op sh).places, mixed op g' = false := by
  intro g' hg'
  obtain ⟨g, hg, rfl, hlen⟩ := mem_settle_places hg'
  cases hm : mixed op (g.filter (stays op sh)) with
  | false => rfl
  | true =>
    exfalso
    have hmg : mixed op g = true :=
      mixed_mono (fun x hx => (List.mem_filter.mp hx).1) hm
    have hnil : g.filter (stays op sh) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      simp [stays, mem_struck hg hmg ha]
    rw [hnil] at hlen
    simp at hlen

/-- After undoing, nothing is left to undo. -/
theorem settle_settled (op : Nat → Nat → Bool) (sh : Shape) :
    struck op (settle op sh) = [] := by
  have h : (settle op sh).places.filter (mixed op) = [] := by
    rw [List.filter_eq_nil_iff]
    intro g hg
    simp [settle_unmixed op sh g hg]
  simp only [struck, h, List.flatten_nil]

/-! ### Undoing never makes a world The Model forbids -/

theorem settle_things_sublist (op : Nat → Nat → Bool) (sh : Shape) :
    ∀ x y, (fun t => if hit op sh t then shrink (fun i => !decide (i ∈ struck op sh)) t
      else some t) x = some y → y.Sublist x := by
  intro x y h
  simp only at h
  split at h
  · exact shrink_sublist _ _ _ h
  · cases h; exact List.Sublist.refl _

theorem settle_wf {n : Nat} (op : Nat → Nat → Bool) {sh : Shape} (h : WF n sh) :
    WF n (settle op sh) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t' ht'
    obtain ⟨t, ht, -, hfalse, htrue⟩ := mem_settle_things ht'
    cases hh : hit op sh t
    · rw [hfalse hh]; exact h1 t ht
    · exact htrue hh
  · intro t' ht' i hi
    obtain ⟨t, ht, sub, -, -⟩ := mem_settle_things ht'
    exact h2 t ht i (sub.subset hi)
  · exact h3.sublist (flatten_filterMap_sublist (settle_things_sublist op sh) _)
  · intro g' hg'
    obtain ⟨g, -, -, hlen⟩ := mem_settle_places hg'
    exact hlen
  · intro g' hg' i hi
    obtain ⟨g, hg, rfl, -⟩ := mem_settle_places hg'
    obtain ⟨hig, hs⟩ := List.mem_filter.mp hi
    obtain ⟨t, ht, hit_⟩ := h5 g hg i hig
    exact ⟨t, mem_settle_of_not_hit ht (not_hit_of_stays ht hit_ hs), hit_⟩
  · exact h6.sublist (flatten_filterMap_sublist (shrink_sublist _) _)
  · intro g' hg' t' ht' i hi j hj hit' hjt'
    obtain ⟨g, hg, rfl, -⟩ := mem_settle_places hg'
    obtain ⟨t, ht, sub, -, -⟩ := mem_settle_things ht'
    exact h7 g hg t ht i (List.mem_filter.mp hi).1 j (List.mem_filter.mp hj).1
      (sub.subset hit') (sub.subset hjt')
  · intro g' hg' i hi j hj t' ht' u' hu' hit' hju'
    obtain ⟨g, hg, rfl, -⟩ := mem_settle_places hg'
    obtain ⟨hig, hsi⟩ := List.mem_filter.mp hi
    obtain ⟨hjg, hsj⟩ := List.mem_filter.mp hj
    obtain ⟨t, ht, subt, eqt, -⟩ := mem_settle_things ht'
    obtain ⟨u, hu, subu, equ, -⟩ := mem_settle_things hu'
    have hti : i ∈ t := subt.subset hit'
    have huj : j ∈ u := subu.subset hju'
    rw [eqt (not_hit_of_stays ht hti hsi), equ (not_hit_of_stays hu huj hsj)]
    exact h8 g hg i hig j hjg t ht u hu hti huj

/-! ### Every event, and every history, leaves an allowed, settled world -/

theorem stepShape_ok {n : Nat} {op : Nat → Nat → Bool} {sh sh' : Shape} {e : Event}
    (h : stepShape n op sh e = some sh') : WF n sh' ∧ struck op sh' = [] := by
  unfold stepShape at h
  split at h
  · cases h
    exact ⟨settle_wf op (by assumption), settle_settled op _⟩
  · cases h

/-- After any event, the world is one The Model allows, and no bound point
shares a place with an opposite one. -/
theorem step_ok {w w' : World} {e : Event} (h : w.step e = some w') :
    WF w'.signs.length w'.shape ∧ struck (opp w'.signs) w'.shape = [] := by
  simp only [World.step, Option.map_eq_some_iff] at h
  obtain ⟨sh, hsh, rfl⟩ := h
  exact stepShape_ok hsh

/-- The start is allowed. -/
theorem start_wf (bag : List Sign) : WF bag.length (World.start bag).shape := by
  simp [World.start, WF]

/-- Every world reached from an allowed world, by any history, is allowed. -/
theorem run_wf : ∀ (es : List Event) (w w' : World),
    WF w.signs.length w.shape → w.run es = some w' → WF w'.signs.length w'.shape
  | [], w, w', hw, h => by
    simp only [World.run, Option.some.injEq] at h
    subst h; exact hw
  | e :: es, w, w', _, h => by
    simp only [World.run] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      exact run_wf es w₁ w' (step_ok h₁).1 h

/-- In particular, every world any history makes from a loose bag is allowed. -/
theorem start_run_wf (bag : List Sign) (es : List Event) (w' : World)
    (h : (World.start bag).run es = some w') : WF w'.signs.length w'.shape :=
  run_wf es _ w' (start_wf bag) h

end Proofs

/-! ## 10b. Worked examples (each checked by running the rules) -/

section Examples
open Sign

/-- A ⊕×⊖ segment (points 0, 1) laid on its twin, a ⊖×⊕ segment (points
2, 3), ⊕ on ⊖ at both ends: all four points come unbound and go back to the
bag, released as two (⊕ + ⊖) pairs. -/
example : (World.start [pos, neg, neg, pos]).run
      [.bind 0 1, .bind 2 3, .join [(0, 2), (1, 3)]]
    = some ⟨[pos, neg, neg, pos], ⟨[], []⟩⟩ := by decide

example : ((World.start [pos, neg, neg, pos]).run [.bind 0 1, .bind 2 3]).map
      (fun w => w.released (.join [(0, 2), (1, 3)]))
    = some [[pos, neg], [neg, pos]] := by decide

/-- Two ⊕×⊖ segments joined ⊕ to ⊕: nothing comes unbound, and they stay joined. -/
example : (World.start [pos, neg, pos, neg]).run
      [.bind 0 1, .bind 2 3, .join [(0, 2)]]
    = some ⟨[pos, neg, pos, neg], ⟨[[0, 1], [2, 3]], [[0, 2]]⟩⟩ := by decide

/-- Two triangles touching ⊕ to ⊖ at one corner: only that corner comes
unbound on each, so each drops to a segment, arriving touching nothing. -/
example : (World.start [pos, pos, neg, neg, pos, pos]).run
      [.bind 0 1, .bind 0 2, .bind 3 4, .bind 3 5, .join [(0, 3)]]
    = some ⟨[pos, pos, neg, neg, pos, pos], ⟨[[1, 2], [4, 5]], []⟩⟩ := by decide

/-- + only within a dimension: a segment and a triangle can't be joined. -/
example : (World.start [pos, pos, pos, pos, pos]).run
      [.bind 0 1, .bind 2 3, .bind 2 4, .join [(0, 2)]] = none := by decide

/-- A bag point can't be joined: it is at the origin. -/
example : (World.start [pos, pos, pos]).run [.bind 0 1, .join [(0, 2)]] = none := by decide

/-- A point already bound can't be bound again [Gap 9]. -/
example : (World.start [pos, pos, pos]).run [.bind 0 1, .bind 2 1] = none := by decide

/-- A thing that rises leaves its joins behind [Gap 11]: two segments joined
⊕ to ⊕, then one takes a fifth point and becomes a triangle. -/
example : (World.start [pos, neg, pos, neg, pos]).run
      [.bind 0 1, .bind 2 3, .join [(0, 2)], .bind 0 4]
    = some ⟨[pos, neg, pos, neg, pos], ⟨[[2, 3], [0, 1, 4]], []⟩⟩ := by decide

end Examples

/-! ## 11. Audit

Each line below asks Lean to list everything the named result rests on
besides the definitions in this file. The answers are Lean's own standard
rules of logic (`propext`, `Quot.sound`, `Classical.choice`) or nothing at all;
no assumption about the model appears, and no proof is left unfinished
(Lean would print `sorryAx`). -/

#print axioms twin_twin
#print axioms order_counts
#print axioms step_signs
#print axioms step_count_and_total
#print axioms step_twin
#print axioms struck_ignores_things
#print axioms settle_settled
#print axioms settle_wf
#print axioms step_ok
#print axioms start_run_wf

end OSM
