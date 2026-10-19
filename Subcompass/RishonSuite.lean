import Subcompass.Suite
import Subcompass.Rishon

/-!
# Rishon in the shared test suite

Results (each a theorem below):

* passes `ChargeConserved`, `BetaDecay`, `Annihilation`, `MakesFamily 1`;
* fails `ChargeCarried`: a loose point in the bag carries charge but is no
  particle, so making an electron from the vacuum leaves its partners' charge
  loose (`rishon_not_ChargeCarried`);
* `MakesFamily 2` and `MakesFamily 3` are unproved: Rishon has only the first
  family.
-/

namespace Rishon
open OSM

/-- Rishon's particle names in the suite's catalog. -/
def Particle.toSuite : Particle → Suite.Particle
  | .positron => .anti .electron
  | .up => .matter .up
  | .antidown => .anti .down
  | .neutrino => .matter .nuE
  | .electron => .matter .electron
  | .antiup => .anti .up
  | .down => .matter .down
  | .antineutrino => .anti .nuE

/-- Rishon plugged into the suite. Charge is counted in sixths of e: the sum
of every sign in the world, loose points included. -/
def suiteModel : Suite.Model where
  World := World
  Event := Event
  step := step
  vacuum := World.start []
  particles w := (particles w).map Particle.toSuite
  chargeUnit := 6
  charge w := total w.signs

/-- The events that tie three segments, (root, tip) each, into a tripod. -/
def tripod (a b c : Nat × Nat) : List Event :=
  [.osm (.bind a.1 a.2), .osm (.bind b.1 b.2), .osm (.bind c.1 c.2),
   .osm (.join [(a.1, b.1), (a.1, c.1)])]

/-- Six pairs from the vacuum: points 0 to 11, even ⊕, odd ⊖. -/
def sixPairs : List Event := List.replicate 6 .pair

theorem rishon_ChargeConserved : Suite.ChargeConserved suiteModel :=
  fun _ _ _ h => step_total h

/-- From the vacuum, four pairs (points 0 to 7) make a down quark T̄V̄V̄,
leaving 4 and 6 loose. Six more pairs (8 to 19) arrive; a V stick from one is
laid on the quark's roots, everything there comes apart, and the loose points
are tied into u, e⁻ and ν̄ (16 and 18 stay loose). -/
theorem rishon_BetaDecay : Suite.BetaDecay suiteModel :=
  ⟨List.replicate 4 .pair ++ tripod (1, 3) (5, 0) (7, 2),
   List.replicate 6 .pair ++ [.osm (.bind 8 9), .osm (.join [(8, 1)])] ++
     tripod (0, 2) (4, 6) (8, 1) ++ tripod (3, 5) (7, 9) (11, 13) ++
     tripod (15, 10) (17, 12) (19, 14),
   by decide +kernel⟩

/-- An electron (roots 1, 5, 9) and a positron (roots 0, 4, 8), hubs laid
together: every root comes apart, leaving loose points and no particles. -/
theorem rishon_Annihilation : Suite.Annihilation suiteModel :=
  ⟨[], by simp, sixPairs ++ tripod (1, 3) (5, 7) (9, 11) ++ tripod (0, 2) (4, 6) (8, 10),
    [.osm (.join [(1, 0)])], by decide +kernel⟩

theorem rishon_MakesFamily1 : Suite.MakesFamily 1 suiteModel := by
  intro f hf hfam
  simp only [Suite.Flavor.all, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Suite.Flavor.family] at hfam
  -- electron T̄T̄T̄ and positron TTT
  · exact ⟨[], sixPairs ++ tripod (1, 3) (5, 7) (9, 11) ++ tripod (0, 2) (4, 6) (8, 10),
      by decide +kernel⟩
  -- neutrino VVV and antineutrino V̄V̄V̄
  · exact ⟨[], sixPairs ++ tripod (0, 1) (2, 3) (4, 5) ++ tripod (7, 6) (9, 8) (11, 10),
      by decide +kernel⟩
  -- up TTV and anti-up T̄T̄V̄
  · exact ⟨[], sixPairs ++ tripod (0, 2) (4, 6) (8, 1) ++ tripod (3, 5) (7, 9) (11, 10),
      by decide +kernel⟩
  -- down T̄V̄V̄ and anti-down TVV
  · exact ⟨[], sixPairs ++ tripod (1, 3) (5, 0) (7, 2) ++ tripod (4, 6) (8, 9) (10, 11),
      by decide +kernel⟩

/-- An electron made from six pairs leaves six loose ⊕: the world's charge
is 0, but its one particle has charge −1. -/
theorem rishon_not_ChargeCarried : ¬ Suite.ChargeCarried suiteModel := by
  intro h
  have := h (sixPairs ++ tripod (1, 3) (5, 7) (9, 11))
  revert this
  decide +kernel

#print axioms rishon_ChargeConserved
#print axioms rishon_BetaDecay
#print axioms rishon_Annihilation
#print axioms rishon_MakesFamily1
#print axioms rishon_not_ChargeCarried

end Rishon
