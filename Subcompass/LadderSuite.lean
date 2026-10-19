import Subcompass.Ladder

/-!
# Ladder in our space (`d = 3`), and in the shared test suite

At `d = 3` a particle is a 4-simplex: a root, three tips and a hand, as in
Penta, and 6 × charge = 3 × root + tips. What Ladder adds here is the gluon
(`twist`).

Results (each a theorem below):

* passes `ChargeConserved`, `ChargeCarried`, `BaryonConserved`,
  `LeptonConserved`, `ProtonStable`, `BetaDecayAmong`, `Annihilation` and
  `MakesFamily 1`;
* fails `BetaDecay`: the vacuum makes particles only with their
  antiparticles, so no world holds a lone down quark (`ladder_not_BetaDecay`);
* passes the prediction tests, which read only Ladder's own charges and
  hands: `TwinFlipsHand`, `VectorlikeCharge`, `OneFamilyCharges`,
  `ThirdsComeInThrees` and `TwinIsAnti`;
* `MakesFamily 2` and `MakesFamily 3` are unproved: Ladder has only the first
  family.
-/

namespace Ladder

open Sign

/-! ## 1. The reading: which particle each 4-simplex is -/

/-- Root and number of ⊖ tips name the particle; the hand says which way it
turns, and the place of the odd tip is a quark's colour.

| root | no tip ⊖ | one ⊖ | two ⊖ | three ⊖ |
| --- | --- | --- | --- | --- |
| ⊕ | e⁺ | u | d̄ | ν |
| ⊖ | ν̄ | d | ū | e⁻ | -/
def Simplex.particle (t : Simplex 3) : Suite.Particle :=
  match t.root, t.negs with
  | .pos, 0 => .anti .electron
  | .pos, 1 => .matter .up
  | .pos, 2 => .anti .down
  | .pos, _ => .matter .nuE
  | .neg, 0 => .anti .nuE
  | .neg, 1 => .matter .down
  | .neg, 2 => .anti .up
  | .neg, _ => .matter .electron

/-- Matter, not antimatter. -/
def isMatter : Suite.Particle → Bool
  | .matter _ => true
  | _ => false

/-- Every particle has the measured charge: 6 × charge = 3 × root + tips. -/
theorem charge_eq_particle (t : Simplex 3) : t.charge = 2 * t.particle.charge3 := by
  revert t; decide

/-- The twin of a particle is its antiparticle... -/
theorem twin_is_anti (t : Simplex 3) : t.twin.particle = t.particle.antiOf := by
  revert t; decide

/-- ...with the opposite hand: five points is an odd number. -/
example (t : Simplex 3) : t.twin.value = -t.value := twin_flips_hand_iff.mpr (by decide) t

/-- The W touches exactly the left-handed particles and the right-handed
antiparticles, as in nature. -/
theorem active_iff (t : Simplex 3) :
    t.active = (t.value == -1 && isMatter t.particle || t.value == 1 && !isMatter t.particle) := by
  revert t; decide

/-- A gluon never changes which particle it is, only its colour. -/
theorem particle_twisted (t : Simplex 3) (i j : Fin 3) :
    (t.twisted i j).particle = t.particle := by
  revert t i j; decide

/-- Baryon number depends only on the ⊖ tips: one is a quark, two an antiquark. -/
theorem baryon_eq (t : Simplex 3) :
    t.particle.baryon3 = (match t.negs with | 1 => 1 | 2 => -1 | _ => 0) := by
  revert t; decide

/-- So does lepton number: none is an antilepton, three a lepton. -/
theorem lepton_eq (t : Simplex 3) :
    t.particle.lepton = (match t.negs with | 0 => -1 | 3 => 1 | _ => 0) := by
  revert t; decide

/-- Every event keeps a quantity that depends only on the tips, has none in a
twin pair, and isn't changed by a gluon. -/
theorem step_tips (q : Simplex 3 → Int) (hq : ∀ t s, q (t.withWeak s) = q t)
    (hf : ∀ t, q t.flipped = q t)
    (htwin : ∀ t, q t + q t.twin = 0) (htw : ∀ t i j, q (t.twisted i j) = q t)
    {w w' : World 3} {e : Event 3} (h : step w e = some w') : sumOf q w' = sumOf q w :=
  step_keeps q htwin (fun s t => by rw [hq, hq]) hf (fun s t i j _ => by rw [htw, htw]) h

theorem step_baryon {w w' : World 3} {e : Event 3} (h : step w e = some w') :
    sumOf (fun t => t.particle.baryon3) w' = sumOf (fun t => t.particle.baryon3) w :=
  step_tips _ (fun t s => by rw [baryon_eq, baryon_eq]; rfl)
    (fun t => by rw [baryon_eq, baryon_eq]; rfl)
    (fun t => by revert t; decide) (fun t i j => by rw [particle_twisted]) h

theorem step_lepton {w w' : World 3} {e : Event 3} (h : step w e = some w') :
    sumOf (fun t => t.particle.lepton) w' = sumOf (fun t => t.particle.lepton) w :=
  step_tips _ (fun t s => by rw [lepton_eq, lepton_eq]; rfl)
    (fun t => by rw [lepton_eq, lepton_eq]; rfl)
    (fun t => by revert t; decide) (fun t i j => by rw [particle_twisted]) h

/-! ## 2. Worked examples -/

/-- A left-handed down quark of colour 0 (its ⊖ tip is at place 0). -/
def down : Simplex 3 := ⟨neg, ![neg, pos, pos], neg⟩
/-- The same quark, colour 1. -/
def down₁ : Simplex 3 := ⟨neg, ![pos, neg, pos], neg⟩
/-- A left-handed neutrino. -/
def nu : Simplex 3 := ⟨pos, ![neg, neg, neg], pos⟩

/-- β decay: the vacuum lends a neutrino and an antineutrino; the down quark
swaps roots with the neutrino. The down becomes a left-handed up (same
colour), the neutrino a left-handed electron. -/
example : (List.foldlM step [down] [Event.pair nu, Event.swap down nu]).map
      (·.map fun t => (t.particle, t.value))
    = some [(.matter .up, -1), (.matter .electron, -1), (.anti .nuE, 1)] := by decide

/-- A gluon: two down quarks of colours 0 and 1 trade colours. -/
example : step [down, down₁] (.twist down down₁ 0 1) = some [down₁, down] := by decide

/-- A gluon: a down quark and its antiquark change colour together, from 0 to 2,
and stay a colourless pair. -/
example : step [down, down.twin] (.twist down down.twin 0 2) =
    some [⟨neg, ![pos, pos, neg], neg⟩, (⟨neg, ![pos, pos, neg], neg⟩ : Simplex 3).twin] := by
  decide

/-- No quark can change colour beside a lepton: a gluon needs a partner whose
colour moves the other way. -/
theorem no_lone_colour (q t : Simplex 3) (i j : Fin 3) (hq : q.tip i ≠ q.tip j)
    (ht : t.tip i = t.tip j) : q.glues t i j = false := by
  have hinj : ∀ a b : Sign, a.toInt = b.toInt → a = b := by decide
  simp only [Simplex.glues, ht, beq_eq_false_iff_ne]
  intro h; exact hq (hinj _ _ (by omega))

/-! ## 3. The shared suite -/

/-- Ladder at `d = 3` plugged into the suite. Charge is counted in sixths of e. -/
abbrev suiteModel : Suite.Model where
  World := World 3
  Event := Event 3
  step := step
  vacuum := []
  particles w := w.map Simplex.particle
  chargeUnit := 6
  charge := charge

theorem conserves {q : Suite.Particle → Int}
    (hq : ∀ {w w' : World 3} {e : Event 3}, step w e = some w' →
      sumOf (fun t => q t.particle) w' = sumOf (fun t => q t.particle) w) :
    Suite.Conserves q suiteModel := by
  intro _ w e w' _ h
  show ((w'.map Simplex.particle).map q).sum = ((w.map Simplex.particle).map q).sum
  rw [List.map_map, List.map_map]
  exact hq h

theorem ladder_ChargeConserved : Suite.ChargeConserved suiteModel :=
  fun _ _ _ h => step_charge h

/-- No loose points: every world's charge is all in its particles. -/
theorem ladder_ChargeCarried : Suite.ChargeCarried suiteModel := by
  intro es w h
  clear h es
  show 6 * ((w.map Simplex.particle).map Suite.Particle.charge3).sum = 3 * charge w
  induction w with
  | nil => rfl
  | cons t w ih =>
    simp only [List.map_cons, List.sum_cons, charge, sumOf_cons] at ih ⊢
    rw [charge_eq_particle]
    omega

theorem ladder_BaryonConserved : Suite.BaryonConserved suiteModel := conserves step_baryon

theorem ladder_LeptonConserved : Suite.LeptonConserved suiteModel := conserves step_lepton

theorem ladder_ProtonStable : Suite.ProtonStable suiteModel :=
  Suite.ProtonStable.of_baryonConserved ladder_BaryonConserved

theorem ladder_BetaDecayAmong : Suite.BetaDecayAmong suiteModel :=
  ⟨[.anti .down], [.pair down], [.pair nu, .swap down nu], by decide⟩

theorem ladder_not_BetaDecay : ¬ Suite.BetaDecay suiteModel := by
  intro ⟨es₀, _, hc⟩
  simp only [Suite.Model.check] at hc
  split at hc
  · cases hc
  · rename_i w h₀
    simp only [Bool.and_eq_true] at hc
    have hw := Suite.perm_sum ((List.isPerm_iff.mp hc.1).map Suite.Particle.baryon3)
    have := ladder_BaryonConserved.reach h₀
    simp only [Suite.Model.total] at this
    rw [this] at hw
    exact absurd hw (by decide)

/-- A left-handed electron. -/
def electron : Simplex 3 := ⟨neg, ![neg, neg, neg], neg⟩

theorem ladder_Annihilation : Suite.Annihilation suiteModel :=
  ⟨[], by simp, [.pair electron], [.annihilate electron], by decide⟩

theorem ladder_MakesFamily1 : Suite.MakesFamily 1 suiteModel := by
  intro f hf hfam
  simp only [Suite.Flavor.all, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Suite.Flavor.family] at hfam
  · exact ⟨[], [.pair electron], by decide⟩
  · exact ⟨[], [.pair nu], by decide⟩
  · exact ⟨[], [.pair ⟨pos, ![neg, pos, pos], pos⟩], by decide⟩
  · exact ⟨[], [.pair down], by decide⟩

/-! ## 4. Predictions: what Ladder's arithmetic alone says -/

/-- All 32 four-simplices. -/
def all : List (Simplex 3) :=
  let ss := [pos, neg]
  ss.flatMap fun r => ss.flatMap fun a => ss.flatMap fun b => ss.flatMap fun c =>
    ss.map fun h => ⟨r, ![a, b, c], h⟩

/-- Ladder's spectrum at `d = 3`: the charge (in sixths, always even) and the
hand its rules give. No particle names are used. -/
abbrev spectrum : Suite.Spectrum where
  Kind := Simplex 3
  kinds := all
  charge3 t := t.charge / 2
  left t := t.value == -1
  twin := Simplex.twin

theorem ladder_TwinFlipsHand : Suite.TwinFlipsHand spectrum := by
  unfold Suite.TwinFlipsHand; decide

theorem ladder_VectorlikeCharge : Suite.VectorlikeCharge spectrum := by
  unfold Suite.VectorlikeCharge; decide

theorem ladder_OneFamilyCharges : Suite.OneFamilyCharges spectrum := by
  unfold Suite.OneFamilyCharges; decide

theorem ladder_ThirdsComeInThrees : Suite.ThirdsComeInThrees spectrum := by
  unfold Suite.ThirdsComeInThrees; decide

theorem ladder_TwinIsAnti : Suite.TwinIsAnti spectrum := by
  unfold Suite.TwinIsAnti; decide

/-! ## 5. Audit -/

#print axioms step_charge
#print axioms step_colour
#print axioms colours
#print axioms colour_count
#print axioms denominator_dvd
#print axioms twin_flips_hand_iff
#print axioms ladder_ChargeConserved
#print axioms ladder_ChargeCarried
#print axioms ladder_BaryonConserved
#print axioms ladder_LeptonConserved
#print axioms ladder_ProtonStable
#print axioms ladder_BetaDecayAmong
#print axioms ladder_not_BetaDecay
#print axioms ladder_Annihilation
#print axioms ladder_MakesFamily1
#print axioms ladder_TwinFlipsHand
#print axioms ladder_VectorlikeCharge
#print axioms ladder_OneFamilyCharges
#print axioms ladder_ThirdsComeInThrees
#print axioms ladder_TwinIsAnti

end Ladder
