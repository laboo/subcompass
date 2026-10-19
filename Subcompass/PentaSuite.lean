import Subcompass.Suite
import Subcompass.Penta

/-!
# Penta in the shared test suite

Results (each a theorem below):

* passes `ChargeConserved`, `ChargeCarried`, `BaryonConserved`,
  `LeptonConserved`, `ProtonStable`, `BetaDecayAmong`, `Annihilation` and
  `MakesFamily 1`;
* fails `BetaDecay`: the vacuum makes particles only with their
  antiparticles, so no world holds a lone down quark (`penta_not_BetaDecay`).
  `BetaDecayAmong` is the same decay with the quark's antiquark partner
  looking on;
* passes the prediction tests, which read only Penta's own charges and
  hands: `TwinFlipsHand`, `VectorlikeCharge`, `OneFamilyCharges` and
  `ThirdsComeInThrees`;
* `MakesFamily 2` and `MakesFamily 3` are unproved: Penta has only the first
  family.
-/

namespace Penta

/-- Penta plugged into the suite. Charge is counted in sixths of e. -/
abbrev suiteModel : Suite.Model where
  World := World
  Event := Event
  step := step
  vacuum := []
  particles w := w.map Pent.particle
  chargeUnit := 6
  charge := charge

/-- Every event, in every world: a model-level fact behind the suite's
`Conserves` tests. -/
theorem conserves {q : Suite.Particle → Int}
    (hq : ∀ {w w' : World} {e : Event}, step w e = some w' →
      sumOf (fun t => q t.particle) w' = sumOf (fun t => q t.particle) w) :
    Suite.Conserves q suiteModel := by
  intro _ w e w' _ h
  show ((w'.map Pent.particle).map q).sum = ((w.map Pent.particle).map q).sum
  rw [List.map_map, List.map_map]
  exact hq h

theorem penta_ChargeConserved : Suite.ChargeConserved suiteModel :=
  fun _ _ _ h => step_charge h

/-- No loose points: every world's charge is all in its particles. -/
theorem penta_ChargeCarried : Suite.ChargeCarried suiteModel := by
  intro es w h
  clear h es
  show 6 * ((w.map Pent.particle).map Suite.Particle.charge3).sum = 3 * charge w
  induction w with
  | nil => rfl
  | cons t w ih =>
    simp only [List.map_cons, List.sum_cons, charge, sumOf_cons] at ih ⊢
    rw [charge6_eq]
    omega

theorem penta_BaryonConserved : Suite.BaryonConserved suiteModel := conserves step_baryon

theorem penta_LeptonConserved : Suite.LeptonConserved suiteModel := conserves step_lepton

theorem penta_ProtonStable : Suite.ProtonStable suiteModel :=
  Suite.ProtonStable.of_baryonConserved penta_BaryonConserved

/-- A down quark and its antiquark from the vacuum; then a neutrino pair, and
the down swaps roots with the neutrino: u, e⁻ and ν̄, with the anti-down
looking on. -/
theorem penta_BetaDecayAmong : Suite.BetaDecayAmong suiteModel :=
  ⟨[.anti .down], [.pair down], [.pair nu, .swap down nu], by decide⟩

/-- No world made from the vacuum holds a lone down quark: its baryon number
would be 1, and the vacuum's is 0. -/
theorem penta_not_BetaDecay : ¬ Suite.BetaDecay suiteModel := by
  intro ⟨es₀, _, hc⟩
  simp only [Suite.Model.check] at hc
  split at hc
  · cases hc
  · rename_i w h₀
    simp only [Bool.and_eq_true] at hc
    have hw := Suite.perm_sum ((List.isPerm_iff.mp hc.1).map Suite.Particle.baryon3)
    have := penta_BaryonConserved.reach h₀
    simp only [Suite.Model.total] at this
    rw [this] at hw
    exact absurd hw (by decide)

/-- An electron and a positron from the vacuum, then annihilated. -/
theorem penta_Annihilation : Suite.Annihilation suiteModel :=
  ⟨[], by simp, [.pair ⟨.neg, .neg, .neg, .neg, .neg⟩], [.annihilate ⟨.neg, .neg, .neg, .neg, .neg⟩],
    by decide⟩

theorem penta_MakesFamily1 : Suite.MakesFamily 1 suiteModel := by
  intro f hf hfam
  simp only [Suite.Flavor.all, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Suite.Flavor.family] at hfam
  · exact ⟨[], [.pair ⟨.neg, .neg, .neg, .neg, .neg⟩], by decide⟩
  · exact ⟨[], [.pair nu], by decide⟩
  · exact ⟨[], [.pair ⟨.pos, .pos, .pos, .neg, .pos⟩], by decide⟩
  · exact ⟨[], [.pair down], by decide⟩

#print axioms penta_ChargeConserved
#print axioms penta_ChargeCarried
#print axioms penta_BaryonConserved
#print axioms penta_LeptonConserved
#print axioms penta_ProtonStable
#print axioms penta_BetaDecayAmong
#print axioms penta_not_BetaDecay
#print axioms penta_Annihilation
#print axioms penta_MakesFamily1

/-! ## Predictions: what Penta's arithmetic alone says -/

/-- Penta's spectrum: all 32 four-simplices, with the charge (6 × charge is
always even, so this is exact) and the hand (the value) its rules give. No
particle names are used. -/
abbrev spectrum : Suite.Spectrum where
  Kind := Pent
  kinds := Pent.all
  charge3 t := t.charge6 / 2
  left t := t.value == .neg
  twin := Pent.twin

theorem penta_TwinFlipsHand : Suite.TwinFlipsHand spectrum := by
  unfold Suite.TwinFlipsHand; decide

theorem penta_VectorlikeCharge : Suite.VectorlikeCharge spectrum := by
  unfold Suite.VectorlikeCharge; decide

theorem penta_OneFamilyCharges : Suite.OneFamilyCharges spectrum := by
  unfold Suite.OneFamilyCharges; decide

theorem penta_ThirdsComeInThrees : Suite.ThirdsComeInThrees spectrum := by
  unfold Suite.ThirdsComeInThrees; decide

#print axioms penta_TwinFlipsHand
#print axioms penta_VectorlikeCharge
#print axioms penta_OneFamilyCharges
#print axioms penta_ThirdsComeInThrees

end Penta
