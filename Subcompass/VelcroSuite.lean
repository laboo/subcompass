import Subcompass.Velcro

/-!
# Velcro in the shared test suite

Results (each a theorem below):

* passes `ChargeConserved`, `ChargeCarried`, `BaryonConserved`,
  `LeptonConserved`, `ProtonStable`, `BetaDecayAmong`, `Annihilation` and
  `MakesFamily 1`;
* passes the force-carrier tests: `AnnihilatesToLight`, `BetaDecayViaW`, and
  `MakesBoson` for the photon, the gluon, the W⁺, the W⁻ and the Higgs;
* fails `MakesBoson .z`: the empty container stands for every neutral
  carrier at once, and is read as the photon, so no world ever holds a Z
  (`velcro_not_MakesBoson_z`);
* fails `BetaDecay`: the vacuum makes things only with their twins, so no
  world holds a lone down quark (`velcro_not_BetaDecay`);
* passes the prediction tests, which read only Velcro's own charges and
  hands: `TwinFlipsHand`, `VectorlikeCharge`, `OneFamilyCharges`,
  `ThirdsComeInThrees` and `TwinIsAnti`;
* `MakesFamily 2` and `MakesFamily 3` are unproved: Velcro has only the first
  family.
-/

namespace Velcro

open Suite.Particle Suite.Flavor

/-! ## 1. The reading: which particle each thing is -/

/-- The force carriers by their slots; matter by its root and the sum of its
tips, as in Penta and Ladder.

| root | tips +3 | +1 | −1 | −3 |
| --- | --- | --- | --- | --- |
| ⊕ | e⁺ | u | d̄ | ν |
| ⊖ | ν̄ | d | ū | e⁻ | -/
def Thing.name (a : Thing) : Suite.Particle :=
  if a = photon then boson .photon
  else if a = wPlus then boson .wPlus
  else if a = -wPlus then boson .wMinus
  else if a = higgs ∨ a = -higgs then boson .higgs
  else if a ∈ gluons then boson .gluon
  else if a.root = 1 then
    (if a.tips = 3 then anti .electron else if a.tips = 1 then matter .up
     else if a.tips = -1 then anti .down else matter .nuE)
  else
    (if a.tips = 3 then anti .nuE else if a.tips = 1 then matter .down
     else if a.tips = -1 then anti .up else matter .electron)

/-- The twin of a thing is its antiparticle. -/
theorem name_neg : ∀ a ∈ things, (-a).name = a.name.antiOf := by decide

/-- Every thing carries its measured charge: 6 × charge = 3 × root + tips. -/
theorem charge_name : ∀ a ∈ things, a.charge = 2 * a.name.charge3 := by decide

/-- Baryon and lepton number, read from the slots, are the measured ones. -/
theorem baryon_name : ∀ a ∈ things, baryon3 a = a.name.baryon3 := by decide
theorem lepton_name : ∀ a ∈ things, lepton a = a.name.lepton := by decide

/-- Nothing is ever read as a Z. -/
theorem name_ne_z (a : Thing) : a.name ≠ boson .z := by
  unfold Thing.name; repeat' split
  all_goals decide

/-! ## 2. Everything that may exist is in the list -/

theorem mem_particles (a : Thing) (h : a.isParticle = true) : a ∈ particles := by
  obtain ⟨r, a₀, a₁, a₂, hd⟩ := a
  simp only [Thing.isParticle, Bool.and_eq_true, isSign_iff] at h
  obtain ⟨⟨⟨⟨hr | hr, h₀ | h₀⟩, h₁ | h₁⟩, h₂ | h₂⟩, hh | hh⟩ := h <;> subst_vars <;> decide

theorem mem_of_ok (a : Thing) (h : a.ok = true) : a ∈ things := by
  simp only [Thing.ok, Bool.or_eq_true, List.contains_iff_mem] at h
  rcases h with h | h
  · exact List.mem_append_left _ (mem_particles a h)
  · exact List.mem_append_right _ h

/-! ## 3. Worked examples -/

/-- A left-handed down quark of colour 0 (its ⊖ tip is at place 0). -/
def down : Thing := ⟨-1, -1, 1, 1, -1⟩
/-- A left-handed up quark of colour 0. -/
def up : Thing := ⟨1, -1, 1, 1, 1⟩
/-- A left-handed electron. -/
def electron : Thing := ⟨-1, -1, -1, -1, -1⟩

/-- β decay as its Feynman diagram: d → u + W⁻, then W⁻ → e⁻ + ν̄. The
down quark's antiquark looks on, since the vacuum makes things in pairs. -/
example : (List.foldlM step [down, -down] [.part down up, .part (-wPlus) electron]).map
      (·.map Thing.name)
    = some [matter .electron, anti .nuE, matter .up, anti .down] := by decide

/-- A right-handed down quark can't give off a W. -/
example : step [⟨-1, -1, 1, 1, 1⟩] (.part ⟨-1, -1, 1, 1, 1⟩ ⟨1, -1, 1, 1, 3⟩) = none := by decide

/-- An up quark and a down antiquark join into a W⁺, as at a collider. -/
example : step [up, -down] (.join up (-down)) = some [wPlus] := by decide

/-- A quark trades colour with another through a gluon: the colour-0 down
gives off a gluon and becomes colour 1, and a colour-1 down absorbs it and
becomes colour 0. -/
example : (List.foldlM step [down, ⟨-1, 1, -1, 1, -1⟩]
      [.part down ⟨-1, 1, -1, 1, -1⟩, .join ⟨0, -2, 2, 0, 0⟩ ⟨-1, 1, -1, 1, -1⟩]) =
    some [down, ⟨-1, 1, -1, 1, -1⟩] := by decide

/-- The Higgs turns a left-handed electron right-handed: mass. -/
example : step [electron, higgs] (.join electron higgs) = some [⟨-1, -1, -1, -1, 1⟩] := by decide

/-! ## 4. The shared suite -/

/-- Velcro plugged into the suite. Charge is counted in sixths of e. -/
abbrev suiteModel : Suite.Model where
  World := World
  Event := Event
  step := step
  vacuum := []
  particles w := w.map Thing.name
  chargeUnit := 6
  charge := sumOf Thing.charge

/-- Everything in a world made from the vacuum may exist. -/
theorem reach_ok : ∀ (es : List Event) (w : World), (∀ t ∈ w, t.ok = true) →
    ∀ w', suiteModel.run w es = some w' → ∀ t ∈ w', t.ok = true := by
  intro es
  induction es with
  | nil => intro w hw w' h; simp [Suite.Model.run] at h; subst h; exact hw
  | cons e es ih =>
    intro w hw w' h
    simp only [Suite.Model.run] at h
    split at h
    · cases h
    · rename_i w₁ h₁; exact ih w₁ (step_things hw h₁) w' h

theorem reach {es : List Event} {w : World} (h : suiteModel.run [] es = some w) :
    ∀ t ∈ w, t.ok = true := reach_ok es [] (by simp) w h

/-- The total of a quantity over a world's names is its total over the
things, if the two agree on everything that may exist. -/
theorem total_eq (q : Suite.Particle → Int) (q' : Thing → Int)
    (hq : ∀ a ∈ things, q' a = q a.name) (w : World) (hw : ∀ t ∈ w, t.ok = true) :
    suiteModel.total q w = sumOf q' w := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    simp only [Suite.Model.total, List.map_cons, List.sum_cons] at ih ⊢
    rw [sumOf_cons, ← ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)),
      hq t (mem_of_ok t (hw t (List.mem_cons_self ..)))]

theorem velcro_ChargeConserved : Suite.ChargeConserved suiteModel :=
  fun _ _ _ h => step_charge h

theorem sum_two (l : List Suite.Particle) :
    (l.map fun p => 2 * p.charge3).sum = 2 * (l.map Suite.Particle.charge3).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem velcro_ChargeCarried : Suite.ChargeCarried suiteModel := by
  intro es w h
  have := total_eq (fun p => 2 * p.charge3) Thing.charge
    (fun a ha => charge_name a ha) w (reach h)
  simp only [Suite.Model.total, sum_two] at this
  show (6 : Int) * ((w.map Thing.name).map Suite.Particle.charge3).sum = 3 * sumOf Thing.charge w
  rw [← this]; omega

/-- Every world made from the vacuum has total charge 0. -/
theorem reach_charge : ∀ (es : List Event) (w : World), sumOf Thing.charge w = 0 →
    ∀ w', suiteModel.run w es = some w' → sumOf Thing.charge w' = 0 := by
  intro es
  induction es with
  | nil => intro w hw w' h; simp [Suite.Model.run] at h; subst h; exact hw
  | cons e es ih =>
    intro w hw w' h
    simp only [Suite.Model.run] at h
    split at h
    · cases h
    · rename_i w₁ h₁; exact ih w₁ ((step_charge h₁).trans hw) w' h

theorem velcro_BaryonConserved : Suite.BaryonConserved suiteModel := by
  intro es w e w' h₀ h
  have hw := reach h₀
  have hw' : ∀ t ∈ w', t.ok = true := step_things hw h
  rw [total_eq _ baryon3 baryon_name w' hw', total_eq _ baryon3 baryon_name w hw]
  exact step_baryon hw h

theorem velcro_LeptonConserved : Suite.LeptonConserved suiteModel := by
  intro es w e w' h₀ h
  have hw := reach h₀
  have hw' : ∀ t ∈ w', t.ok = true := step_things hw h
  rw [total_eq _ lepton lepton_name w' hw', total_eq _ lepton lepton_name w hw]
  exact step_lepton hw h

theorem velcro_ProtonStable : Suite.ProtonStable suiteModel :=
  Suite.ProtonStable.of_baryonConserved velcro_BaryonConserved

theorem velcro_BetaDecayViaW : Suite.BetaDecayViaW suiteModel :=
  ⟨⟨[anti .down], [.pair down], [.part down up], by decide⟩,
   ⟨[boson .wPlus], [.pair (-wPlus)], [.part (-wPlus) electron], by decide⟩⟩

theorem velcro_BetaDecayAmong : Suite.BetaDecayAmong suiteModel :=
  ⟨[anti .down], [.pair down], [.part down up, .part (-wPlus) electron], by decide⟩

theorem velcro_AnnihilatesToLight : Suite.AnnihilatesToLight suiteModel :=
  ⟨[.pair electron], [.join electron (-electron), .part photon photon], by decide⟩

theorem velcro_Annihilation : Suite.Annihilation suiteModel :=
  ⟨[boson .photon], by decide, [.pair electron], [.join electron (-electron)], by decide⟩

theorem velcro_MakesFamily_1 : Suite.MakesFamily 1 suiteModel := by
  intro f hf h1
  simp only [Suite.Flavor.all, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd h1 (by decide)
    | exact ⟨[], [.pair electron], by decide⟩
    | exact ⟨[], [.pair ⟨1, -1, -1, -1, 1⟩], by decide⟩
    | exact ⟨[], [.pair up], by decide⟩
    | exact ⟨[], [.pair down], by decide⟩

theorem velcro_MakesBoson_photon : Suite.MakesBoson .photon suiteModel :=
  ⟨[], [.pair photon], by decide⟩
theorem velcro_MakesBoson_gluon : Suite.MakesBoson .gluon suiteModel :=
  ⟨[], [.pair ⟨0, 2, -2, 0, 0⟩], by decide⟩
theorem velcro_MakesBoson_wPlus : Suite.MakesBoson .wPlus suiteModel :=
  ⟨[], [.pair wPlus], by decide⟩
theorem velcro_MakesBoson_wMinus : Suite.MakesBoson .wMinus suiteModel :=
  ⟨[], [.pair (-wPlus)], by decide⟩
theorem velcro_MakesBoson_higgs : Suite.MakesBoson .higgs suiteModel :=
  ⟨[], [.pair higgs], by decide⟩

/-- A world's names never include a Z, so no process can end with one. -/
theorem velcro_not_MakesBoson_z : ¬ Suite.MakesBoson .z suiteModel := by
  rintro ⟨es₀, es, hc⟩
  simp only [Suite.Model.check] at hc
  split at hc
  · cases hc
  · simp only [Bool.and_eq_true] at hc
    obtain ⟨_, hc⟩ := hc
    split at hc
    · cases hc
    · rename_i w' _
      have hm : Suite.Particle.boson .z ∈ w'.map Thing.name :=
        (List.isPerm_iff.mp hc).symm.subset (by simp [Suite.Particle.antiOf])
      obtain ⟨a, _, ha⟩ := List.mem_map.mp hm
      exact name_ne_z a ha

/-- No world made from the vacuum holds a lone down quark: its total charge
would be −1/3, and the vacuum's is 0. -/
theorem velcro_not_BetaDecay : ¬ Suite.BetaDecay suiteModel := by
  rintro ⟨es₀, es, hc⟩
  simp only [Suite.Model.check] at hc
  split at hc
  · cases hc
  · rename_i w h₀
    simp only [Bool.and_eq_true] at hc
    have hp := Suite.perm_sum ((List.isPerm_iff.mp hc.1).map Suite.Particle.charge3)
    have hc' := velcro_ChargeCarried es₀ w h₀
    have h0 := reach_charge es₀ [] rfl w h₀
    dsimp only at hc'
    rw [hp, h0] at hc'
    simp [Suite.Particle.charge3, Suite.Flavor.charge3] at hc'

/-! ## 5. Prediction tests: Velcro's own charges and hands -/

/-- The 32 particles, with the charge and hand Velcro's arithmetic gives
each (charge in thirds of e: (3 × root + tips) / 2). -/
abbrev spectrum : Suite.Spectrum where
  Kind := Thing
  kinds := particles
  charge3 a := a.charge / 2
  left a := a.value == -1
  twin a := -a

theorem velcro_TwinIsAnti : Suite.TwinIsAnti spectrum := by
  unfold Suite.TwinIsAnti; decide
theorem velcro_TwinFlipsHand : Suite.TwinFlipsHand spectrum := by
  unfold Suite.TwinFlipsHand; decide
theorem velcro_VectorlikeCharge : Suite.VectorlikeCharge spectrum := by
  unfold Suite.VectorlikeCharge; decide
theorem velcro_OneFamilyCharges : Suite.OneFamilyCharges spectrum := by
  unfold Suite.OneFamilyCharges; decide
theorem velcro_ThirdsComeInThrees : Suite.ThirdsComeInThrees spectrum := by
  unfold Suite.ThirdsComeInThrees; decide

/-! ## 6. Audit: only the standard axioms -/

#print axioms step_total
#print axioms step_baryon
#print axioms w_iff
#print axioms inside_outside
#print axioms velcro_ChargeConserved
#print axioms velcro_ChargeCarried
#print axioms velcro_BaryonConserved
#print axioms velcro_LeptonConserved
#print axioms velcro_ProtonStable
#print axioms velcro_BetaDecayViaW
#print axioms velcro_BetaDecayAmong
#print axioms velcro_AnnihilatesToLight
#print axioms velcro_Annihilation
#print axioms velcro_MakesFamily_1
#print axioms velcro_MakesBoson_photon
#print axioms velcro_MakesBoson_gluon
#print axioms velcro_MakesBoson_wPlus
#print axioms velcro_MakesBoson_wMinus
#print axioms velcro_MakesBoson_higgs
#print axioms velcro_not_MakesBoson_z
#print axioms velcro_not_BetaDecay
#print axioms velcro_TwinIsAnti
#print axioms velcro_TwinFlipsHand
#print axioms velcro_VectorlikeCharge
#print axioms velcro_OneFamilyCharges
#print axioms velcro_ThirdsComeInThrees

end Velcro
