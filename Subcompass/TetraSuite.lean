import Subcompass.Suite
import Subcompass.Tetra

/-!
# Tetra in the shared test suite

Results (each a theorem below):

* passes `ChargeConserved`, `ChargeCarried`, `BaryonConserved`,
  `LeptonConserved`, `ProtonStable`, `BetaDecayAmong`, `Annihilation` and
  `MakesFamily 1`;
* fails `BetaDecay`: the vacuum makes particles only with their
  antiparticles, so no world holds a lone down quark (`tetra_not_BetaDecay`).
  `BetaDecayAmong` is the same decay with the quark's antiquark partner
  looking on;
* `MakesFamily 2` and `MakesFamily 3` are unproved: Tetra has only the first
  family.
-/

namespace Tetra

/-- Tetra plugged into the suite. Charge is counted in sixths of e. -/
abbrev suiteModel : Suite.Model where
  World := World
  Event := Event
  step := step
  vacuum := []
  particles w := w.map Tet.particle
  chargeUnit := 6
  charge := charge

/-- Every event, in every world: a model-level fact behind the suite's
`Conserves` tests. -/
theorem conserves {q : Suite.Particle → Int}
    (hq : ∀ {w w' : World} {e : Event}, step w e = some w' →
      sumOf (fun t => q t.particle) w' = sumOf (fun t => q t.particle) w) :
    Suite.Conserves q suiteModel := by
  intro _ w e w' _ h
  show ((w'.map Tet.particle).map q).sum = ((w.map Tet.particle).map q).sum
  rw [List.map_map, List.map_map]
  exact hq h

theorem tetra_ChargeConserved : Suite.ChargeConserved suiteModel :=
  fun _ _ _ h => step_charge h

/-- No loose points: every world's charge is all in its particles. -/
theorem tetra_ChargeCarried : Suite.ChargeCarried suiteModel := by
  intro es w h
  clear h es
  show 6 * ((w.map Tet.particle).map Suite.Particle.charge3).sum = 3 * charge w
  induction w with
  | nil => rfl
  | cons t w ih =>
    simp only [List.map_cons, List.sum_cons, charge, sumOf_cons] at ih ⊢
    rw [charge6_eq]
    omega

theorem tetra_BaryonConserved : Suite.BaryonConserved suiteModel := conserves step_baryon

theorem tetra_LeptonConserved : Suite.LeptonConserved suiteModel := conserves step_lepton

theorem tetra_ProtonStable : Suite.ProtonStable suiteModel :=
  Suite.ProtonStable.of_baryonConserved tetra_BaryonConserved

/-- A down quark and its antiquark from the vacuum; then a neutrino pair, and
the down swaps roots with the neutrino: u, e⁻ and ν̄, with the anti-down
looking on. -/
theorem tetra_BetaDecayAmong : Suite.BetaDecayAmong suiteModel :=
  ⟨[.anti .down], [.pair down], [.pair nu, .swap down nu], by decide⟩

/-- No world made from the vacuum holds a lone down quark: its baryon number
would be 1, and the vacuum's is 0. -/
theorem tetra_not_BetaDecay : ¬ Suite.BetaDecay suiteModel := by
  intro ⟨es₀, _, hc⟩
  simp only [Suite.Model.check] at hc
  split at hc
  · cases hc
  · rename_i w h₀
    simp only [Bool.and_eq_true] at hc
    have hw := Suite.perm_sum ((List.isPerm_iff.mp hc.1).map Suite.Particle.baryon3)
    have := tetra_BaryonConserved.reach h₀
    simp only [Suite.Model.total] at this
    rw [this] at hw
    exact absurd hw (by decide)

/-- An electron and a positron from the vacuum, then annihilated. -/
theorem tetra_Annihilation : Suite.Annihilation suiteModel :=
  ⟨[], by simp, [.pair ⟨.neg, .neg, .neg, .neg⟩], [.annihilate ⟨.neg, .neg, .neg, .neg⟩],
    by decide⟩

theorem tetra_MakesFamily1 : Suite.MakesFamily 1 suiteModel := by
  intro f hf hfam
  simp only [Suite.Flavor.all, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Suite.Flavor.family] at hfam
  · exact ⟨[], [.pair ⟨.neg, .neg, .neg, .neg⟩], by decide⟩
  · exact ⟨[], [.pair ⟨.pos, .neg, .neg, .neg⟩], by decide⟩
  · exact ⟨[], [.pair ⟨.pos, .pos, .pos, .neg⟩], by decide⟩
  · exact ⟨[], [.pair down], by decide⟩

#print axioms tetra_ChargeConserved
#print axioms tetra_ChargeCarried
#print axioms tetra_BaryonConserved
#print axioms tetra_LeptonConserved
#print axioms tetra_ProtonStable
#print axioms tetra_BetaDecayAmong
#print axioms tetra_not_BetaDecay
#print axioms tetra_Annihilation
#print axioms tetra_MakesFamily1

end Tetra
