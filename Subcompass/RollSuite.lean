import Subcompass.RollWorld

/-!
# Roll in the shared test suite

Results (each a theorem below):

* passes the tests for space in any dimension: `LocalIn`, `ReadsLocksIn`,
  `NearIn`, `NoGlobalNowIn`, and so `SpeedLimitIn`. (Section 9's tests are for
  a line of cells, and Roll's space is not a line.)
* passes everything Velcro and Zigzag pass: `ChargeConserved`, `ChargeCarried`,
  `BaryonConserved`, `LeptonConserved`, `ProtonStable`, `BetaDecayAmong`,
  `Annihilation`, `MakesFamily 1`, `AnnihilatesToLight`, `BetaDecayViaW`, and
  `MakesBoson` for the photon, the gluon, the W⁺, the W⁻ and the Higgs;
* fails what Velcro fails, for the same reasons: `MakesBoson .z`
  (`roll_not_MakesBoson_z`) and `BetaDecay` (`roll_not_BetaDecay`);
* its things are Velcro's, so its spectrum is Velcro's, and it passes the
  prediction tests by Velcro's proofs.
-/

namespace RollWorld

open Velcro Suite.Particle Suite.Flavor

/-! ## 1. Roll plugged in -/

/-- Roll as a model with space. Charge is counted in sixths of e. -/
abbrev space : Suite.Space where
  World := World
  Event := Event
  step := step
  vacuum := []
  particles w := (things w).map Thing.name
  chargeUnit := 6
  charge w := sumOf Thing.charge (things w)
  Place := Place
  Stuff := Thing
  cell := cell
  locks := Event.locks
  dist := Place.dist
  dist_tri := Place.dist_tri

abbrev model : Suite.Model := space.toModel

/-! ## 2. Space and time -/

theorem roll_LocalIn : Suite.LocalIn space :=
  fun _ _ _ h j hj => local_ h j hj

theorem roll_ReadsLocksIn : Suite.ReadsLocksIn space := reads

theorem roll_NearIn : Suite.NearIn space := near

theorem roll_NoGlobalNowIn : Suite.NoGlobalNowIn space := by
  intro w e f w₁ w₂ hd h₁ h₂
  obtain ⟨w₃, w₄, h₃, h₄, hc⟩ := no_global_now hd h₁ h₂
  exact ⟨w₃, w₄, h₃, h₄, fun j => (perm_cell _ _ j).mpr fun x => hc _⟩

theorem roll_SpeedLimitIn : Suite.SpeedLimitIn space :=
  Suite.SpeedLimitIn.of roll_LocalIn roll_ReadsLocksIn roll_NearIn

/-! ## 3. Everything that exists may exist -/

theorem reach_ok : ∀ (es : List Event) (w : World), (∀ p ∈ w, p.2.ok = true) →
    ∀ w', model.run w es = some w' → ∀ p ∈ w', p.2.ok = true := by
  intro es
  induction es with
  | nil => intro w hw w' h; simp [Suite.Model.run] at h; subst h; exact hw
  | cons e es ih =>
    intro w hw w' h
    simp only [Suite.Model.run] at h
    split at h
    · cases h
    · rename_i w₁ h₁; exact ih w₁ (step_ok hw h₁) w' h

theorem reach {es : List Event} {w : World} (h : model.run [] es = some w) :
    ∀ p ∈ w, p.2.ok = true := reach_ok es [] (by simp) w h

theorem things_ok {w : World} (hw : ∀ p ∈ w, p.2.ok = true) : ∀ t ∈ things w, t.ok = true := by
  intro t ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
  exact hw p hp

theorem total_eq (q : Suite.Particle → Int) (q' : Thing → Int)
    (hq : ∀ a ∈ Velcro.things, q' a = q a.name) (w : World) (hw : ∀ p ∈ w, p.2.ok = true) :
    model.total q w = sumOf q' (things w) :=
  Velcro.total_eq q q' hq (things w) (things_ok hw)

/-! ## 4. Conservation -/

theorem roll_ChargeConserved : Suite.ChargeConserved model :=
  fun _ _ _ h => step_charge h

theorem roll_ChargeCarried : Suite.ChargeCarried model := by
  intro es w h
  have := total_eq (fun p => 2 * p.charge3) Thing.charge
    (fun a ha => charge_name a ha) w (reach h)
  simp only [Suite.Model.total, sum_two] at this
  show (6 : Int) * (((things w).map Thing.name).map Suite.Particle.charge3).sum =
    3 * sumOf Thing.charge (things w)
  rw [← this]; omega

theorem reach_charge : ∀ (es : List Event) (w : World), sumOf Thing.charge (things w) = 0 →
    ∀ w', model.run w es = some w' → sumOf Thing.charge (things w') = 0 := by
  intro es
  induction es with
  | nil => intro w hw w' h; simp [Suite.Model.run] at h; subst h; exact hw
  | cons e es ih =>
    intro w hw w' h
    simp only [Suite.Model.run] at h
    split at h
    · cases h
    · rename_i w₁ h₁; exact ih w₁ ((roll_ChargeConserved w e w₁ h₁).trans hw) w' h

theorem roll_BaryonConserved : Suite.BaryonConserved model := by
  intro es w e w' h₀ h
  have hw := reach h₀
  rw [total_eq _ baryon3 baryon_name w' (step_ok hw h), total_eq _ baryon3 baryon_name w hw]
  exact step_baryon hw h

theorem roll_LeptonConserved : Suite.LeptonConserved model := by
  intro es w e w' h₀ h
  have hw := reach h₀
  rw [total_eq _ lepton lepton_name w' (step_ok hw h), total_eq _ lepton lepton_name w hw]
  exact step_lepton hw h

theorem roll_ProtonStable : Suite.ProtonStable model :=
  Suite.ProtonStable.of_baryonConserved roll_BaryonConserved

/-! ## 5. Processes, all at one place -/

theorem roll_BetaDecayViaW : Suite.BetaDecayViaW model :=
  ⟨⟨[anti .down], [.pair home down], [.part home down up], by decide⟩,
   ⟨[boson .wPlus], [.pair home (-wPlus)], [.part home (-wPlus) electron], by decide⟩⟩

theorem roll_BetaDecayAmong : Suite.BetaDecayAmong model :=
  ⟨[anti .down], [.pair home down], [.part home down up, .part home (-wPlus) electron], by decide⟩

theorem roll_AnnihilatesToLight : Suite.AnnihilatesToLight model :=
  ⟨[.pair home Velcro.electron],
   [.join home Velcro.electron (-Velcro.electron), .part home photon photon], by decide⟩

theorem roll_Annihilation : Suite.Annihilation model :=
  ⟨[boson .photon], by decide, [.pair home Velcro.electron],
   [.join home Velcro.electron (-Velcro.electron)], by decide⟩

theorem roll_MakesFamily_1 : Suite.MakesFamily 1 model := by
  intro f hf h1
  simp only [Suite.Flavor.all, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd h1 (by decide)
    | exact ⟨[], [.pair home Velcro.electron], by decide⟩
    | exact ⟨[], [.pair home ⟨1, -1, -1, -1, 1⟩], by decide⟩
    | exact ⟨[], [.pair home up], by decide⟩
    | exact ⟨[], [.pair home down], by decide⟩

theorem roll_MakesBoson_photon : Suite.MakesBoson .photon model :=
  ⟨[], [.pair home photon], by decide⟩
theorem roll_MakesBoson_gluon : Suite.MakesBoson .gluon model :=
  ⟨[], [.pair home ⟨0, 2, -2, 0, 0⟩], by decide⟩
theorem roll_MakesBoson_wPlus : Suite.MakesBoson .wPlus model :=
  ⟨[], [.pair home wPlus], by decide⟩
theorem roll_MakesBoson_wMinus : Suite.MakesBoson .wMinus model :=
  ⟨[], [.pair home (-wPlus)], by decide⟩
theorem roll_MakesBoson_higgs : Suite.MakesBoson .higgs model :=
  ⟨[], [.pair home higgs], by decide⟩

theorem roll_not_MakesBoson_z : ¬ Suite.MakesBoson .z model := by
  rintro ⟨es₀, es, hc⟩
  simp only [Suite.Model.check] at hc
  split at hc
  · cases hc
  · simp only [Bool.and_eq_true] at hc
    obtain ⟨_, hc⟩ := hc
    split at hc
    · cases hc
    · rename_i w' _
      have hm : Suite.Particle.boson .z ∈ (things w').map Thing.name :=
        (List.isPerm_iff.mp hc).symm.subset (by simp [Suite.Particle.antiOf])
      obtain ⟨a, _, ha⟩ := List.mem_map.mp hm
      exact name_ne_z a ha

theorem roll_not_BetaDecay : ¬ Suite.BetaDecay model := by
  rintro ⟨es₀, es, hc⟩
  simp only [Suite.Model.check] at hc
  split at hc
  · cases hc
  · rename_i w h₀
    simp only [Bool.and_eq_true] at hc
    have hp := Suite.perm_sum ((List.isPerm_iff.mp hc.1).map Suite.Particle.charge3)
    have hc' := roll_ChargeCarried es₀ w h₀
    have h0 := reach_charge es₀ [] rfl w h₀
    dsimp only at hc'
    rw [hp, h0] at hc'
    simp [Suite.Particle.charge3, Suite.Flavor.charge3] at hc'

/-! ## 6. Prediction tests: the same things as Velcro -/

theorem roll_TwinIsAnti : Suite.TwinIsAnti spectrum := velcro_TwinIsAnti
theorem roll_TwinFlipsHand : Suite.TwinFlipsHand spectrum := velcro_TwinFlipsHand
theorem roll_VectorlikeCharge : Suite.VectorlikeCharge spectrum := velcro_VectorlikeCharge
theorem roll_OneFamilyCharges : Suite.OneFamilyCharges spectrum := velcro_OneFamilyCharges
theorem roll_ThirdsComeInThrees : Suite.ThirdsComeInThrees spectrum :=
  velcro_ThirdsComeInThrees

/-! ## 7. Audit: only the standard axioms -/

#print axioms step_total
#print axioms course
#print axioms w_left
#print axioms roll_LocalIn
#print axioms roll_ReadsLocksIn
#print axioms roll_NearIn
#print axioms roll_NoGlobalNowIn
#print axioms roll_SpeedLimitIn
#print axioms roll_ChargeConserved
#print axioms roll_ChargeCarried
#print axioms roll_BaryonConserved
#print axioms roll_LeptonConserved
#print axioms roll_ProtonStable
#print axioms roll_BetaDecayViaW
#print axioms roll_BetaDecayAmong
#print axioms roll_AnnihilatesToLight
#print axioms roll_Annihilation
#print axioms roll_MakesFamily_1
#print axioms roll_MakesBoson_photon
#print axioms roll_MakesBoson_gluon
#print axioms roll_MakesBoson_wPlus
#print axioms roll_MakesBoson_wMinus
#print axioms roll_MakesBoson_higgs
#print axioms roll_not_MakesBoson_z
#print axioms roll_not_BetaDecay

end RollWorld
