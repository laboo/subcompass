/-!
# The shared test suite

Every model in the contest can plug into this file, and every team may add to
it. Passing it is for information only: votes decide the best model.

## How a model plugs in

A model fills in `Suite.Model`: its kind of world and of event, what one event
does (`none` = can't happen), an empty world to start from (`vacuum`), and two
readouts: which Standard Model particles a world holds, and its total electric
charge in units the model chooses (`chargeUnit` of them make one e). A model
that has no notion of particles yet can read none (`fun _ => []`); it then
simply fails the tests that need them.

## How a test works

A test is a statement about a model, `Suite.Model → Prop`. A team proves, in
its own file on its own branch, the tests its model passes, and may also prove
the negation of tests it fails; both are worth knowing. Name them
`<model>_<Test>` and `<model>_not_<Test>` so the results are easy to find.
Many tests say a process is possible; those are proved by giving the events
(see `Allows`), which Lean then runs.

## Units

Charge is in thirds of e (an electron is −3, an up quark +2), and baryon
number in thirds (a quark is 1), so every number here is an integer. Spin is
in halves (an electron is 1, a photon 2).
-/

namespace Suite

/-! ## 1. The particles of the Standard Model, with measured quantum numbers -/

/-- The twelve kinds of matter particle (fermion), three families of four. -/
inductive Flavor where
  | electron | nuE | up | down
  | muon | nuMu | charm | strange
  | tau | nuTau | top | bottom
  deriving DecidableEq, Repr

/-- The force carriers and the Higgs. -/
inductive Boson where
  | photon | gluon | wPlus | wMinus | z | higgs
  deriving DecidableEq, Repr

inductive Particle where
  | matter (f : Flavor)
  | anti (f : Flavor)
  | boson (b : Boson)
  deriving DecidableEq, Repr

namespace Flavor

/-- Family 1, 2 or 3. -/
def family : Flavor → Nat
  | electron | nuE | up | down => 1
  | muon | nuMu | charm | strange => 2
  | tau | nuTau | top | bottom => 3

/-- Electric charge, in thirds of e. -/
def charge3 : Flavor → Int
  | electron | muon | tau => -3
  | nuE | nuMu | nuTau => 0
  | up | charm | top => 2
  | down | strange | bottom => -1

/-- Baryon number, in thirds. -/
def baryon3 : Flavor → Int
  | up | down | charm | strange | top | bottom => 1
  | _ => 0

/-- Lepton number. -/
def lepton : Flavor → Int
  | electron | nuE | muon | nuMu | tau | nuTau => 1
  | _ => 0

def all : List Flavor :=
  [electron, nuE, up, down, muon, nuMu, charm, strange, tau, nuTau, top, bottom]

end Flavor

namespace Particle

def charge3 : Particle → Int
  | matter f => f.charge3
  | anti f => -f.charge3
  | boson .wPlus => 3
  | boson .wMinus => -3
  | boson _ => 0

def baryon3 : Particle → Int
  | matter f => f.baryon3
  | anti f => -f.baryon3
  | boson _ => 0

def lepton : Particle → Int
  | matter f => f.lepton
  | anti f => -f.lepton
  | boson _ => 0

/-- Spin, in halves. -/
def spin2 : Particle → Nat
  | matter _ | anti _ => 1
  | boson .higgs => 0
  | boson _ => 2

def isBoson : Particle → Bool
  | boson _ => true
  | _ => false

def antiOf : Particle → Particle
  | matter f => anti f
  | anti f => matter f
  | boson .wPlus => boson .wMinus
  | boson .wMinus => boson .wPlus
  | boson b => boson b

end Particle

/-! ## 2. What a model provides -/

structure Model where
  World : Type
  Event : Type
  step : World → Event → Option World
  /-- An empty world, before anything happens. -/
  vacuum : World
  /-- The Standard Model particles a world holds, in any order. -/
  particles : World → List Particle
  /-- How many of the model's charge units make one e. -/
  chargeUnit : Nat
  /-- The world's total electric charge, everything in it counted. -/
  charge : World → Int

namespace Model

/-- A history: events one after another; `none` if one can't happen. -/
def run (M : Model) (w : M.World) : List M.Event → Option M.World
  | [] => some w
  | e :: es =>
    match M.step w e with
    | none => none
    | some w' => M.run w' es

/-- `check before after es₀ es`: starting from the vacuum, the events `es₀`
make a world holding exactly the particles `before`, and the events `es` then
turn it into a world holding exactly `after` (in any order). -/
def check (M : Model) (before after : List Particle) (es₀ es : List M.Event) : Bool :=
  match M.run M.vacuum es₀ with
  | none => false
  | some w =>
    (M.particles w).isPerm before &&
    match M.run w es with
    | none => false
    | some w' => (M.particles w').isPerm after

end Model

/-! ## 3. The tests -/

/-- A process is possible: some world made from the vacuum holds exactly
`before`, and some history turns it into a world holding exactly `after`.
Prove it with `⟨es₀, es, by decide⟩` (or `by decide +kernel` for long runs). -/
def Allows (M : Model) (before after : List Particle) : Prop :=
  ∃ es₀ es, M.check before after es₀ es = true

open Particle Flavor

/-- Electric charge is never made or destroyed, by any event. -/
def ChargeConserved (M : Model) : Prop :=
  ∀ w e w', M.step w e = some w' → M.charge w' = M.charge w

/-- All charge is carried by particles: in every world made from the vacuum,
the particles' charges add up to the world's total. (Nothing unnamed, such as
a loose piece, carries charge.) -/
def ChargeCarried (M : Model) : Prop :=
  ∀ es w, M.run M.vacuum es = some w →
    (M.chargeUnit : Int) * ((M.particles w).map Particle.charge3).sum = 3 * M.charge w

/-- β decay, the process behind much radioactivity: d → u + e⁻ + ν̄. -/
def BetaDecay (M : Model) : Prop :=
  Allows M [matter .down] [matter .up, matter .electron, anti .nuE]

/-- An electron and a positron can annihilate, leaving no matter behind
(in nature, two or more photons). -/
def Annihilation (M : Model) : Prop :=
  ∃ bs, (∀ b ∈ bs, b.isBoson = true) ∧ Allows M [matter .electron, anti .electron] bs

/-- Every matter particle of family `n` can be made from the vacuum together
with its antiparticle (as in pair production). -/
def MakesFamily (n : Nat) (M : Model) : Prop :=
  ∀ f ∈ Flavor.all, f.family = n → Allows M [] [matter f, anti f]

/-! ## 4. Checks of the catalog itself -/

/-- Each family's charges add to zero, counting three colours per quark: the
cancellation the Standard Model needs to be consistent. -/
example : ∀ n ∈ [1, 2, 3],
    ((Flavor.all.filter (·.family = n)).map fun f =>
      (if f.baryon3 = 1 then 3 else 1) * f.charge3).sum = 0 := by decide

/-- Charge comes out right for familiar composites: proton uud = +1, neutron
udd = 0 (in thirds: 3 and 0). -/
example : (matter .up).charge3 + (matter .up).charge3 + (matter .down).charge3 = 3 ∧
    (matter .up).charge3 + (matter .down).charge3 + (matter .down).charge3 = 0 := by decide

/-! ## 5. Conservation, and processes among onlookers (added by 1:0)

The Standard Model never changes the total baryon number or the total lepton
number. `BaryonConserved` and `LeptonConserved` ask the same of a model, event
by event, in every world made from the vacuum. `ProtonStable` asks only about
the outcome of one process, so a model can pass it while failing the stricter
tests. -/

/-- A sum over a list of integers doesn't depend on the order. -/
theorem perm_sum {l l' : List Int} (h : l.Perm l') : l.sum = l'.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

namespace Model

/-- The total of a quantity over a world's particles. -/
def total (M : Model) (q : Particle → Int) (w : M.World) : Int :=
  ((M.particles w).map q).sum

theorem run_append (M : Model) (w : M.World) (es es' : List M.Event) :
    M.run w (es ++ es') = (M.run w es).bind (M.run · es') := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
    simp only [List.cons_append, run]
    split <;> simp_all

end Model

/-- No event, in any world made from the vacuum, changes the total of `q`
over the world's particles. -/
def Conserves (q : Particle → Int) (M : Model) : Prop :=
  ∀ es w e w', M.run M.vacuum es = some w → M.step w e = some w' →
    M.total q w' = M.total q w

def BaryonConserved (M : Model) : Prop := Conserves Particle.baryon3 M

def LeptonConserved (M : Model) : Prop := Conserves Particle.lepton M

/-- A process is possible among onlookers: some world made from the vacuum
holds exactly `before` plus some other particles, and some history turns it
into a world holding exactly `after` plus those same others. In nature nothing
happens in an empty universe; a model that makes particles only in pairs (and
so conserves baryon number) can never hold a lone quark, but it can turn one
quark into others while its partner looks on. -/
def AllowsAmong (M : Model) (before after : List Particle) : Prop :=
  ∃ others es₀ es, M.check (before ++ others) (after ++ others) es₀ es = true

theorem Allows.among {M : Model} {before after : List Particle} (h : Allows M before after) :
    AllowsAmong M before after := by
  obtain ⟨es₀, es, hc⟩ := h
  exact ⟨[], es₀, es, by simpa using hc⟩

/-- β decay among onlookers: `BetaDecay` implies it (`Allows.among`). -/
def BetaDecayAmong (M : Model) : Prop :=
  AllowsAmong M [matter .down] [matter .up, matter .electron, anti .nuE]

/-- A proton (u u d), among any onlookers, never becomes anything with a
different baryon number. Experiments have watched for proton decay for decades
and never seen it: the proton lives longer than 10³⁴ years. -/
def ProtonStable (M : Model) : Prop :=
  ∀ after, AllowsAmong M [matter .up, matter .up, matter .down] after →
    (after.map Particle.baryon3).sum = 3

/-- If a model conserves `q`, every history from a world made from the vacuum
keeps the total of `q`. -/
theorem Conserves.run {q : Particle → Int} {M : Model} (hq : Conserves q M) :
    ∀ es w w', (∃ es₀, M.run M.vacuum es₀ = some w) →
      M.run w es = some w' → M.total q w' = M.total q w := by
  intro es
  induction es with
  | nil => intro w w' _ h; simp [Model.run] at h; rw [h]
  | cons e es ih =>
    intro w w' ⟨es₀, h₀⟩ h
    simp only [Model.run] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      have r₁ : M.run M.vacuum (es₀ ++ [e]) = some w₁ := by
        rw [Model.run_append, h₀]; simp [Model.run, h₁]
      rw [ih w₁ w' ⟨_, r₁⟩ h, hq es₀ w e w₁ h₀ h₁]

/-- In particular, every world made from the vacuum has the vacuum's total. -/
theorem Conserves.reach {q : Particle → Int} {M : Model} (hq : Conserves q M)
    {es : List M.Event} {w : M.World} (h : M.run M.vacuum es = some w) :
    M.total q w = M.total q M.vacuum :=
  hq.run es M.vacuum w ⟨[], rfl⟩ h

/-- If a model conserves `q`, every process it allows keeps the total of `q`. -/
theorem Conserves.among {q : Particle → Int} {M : Model} (hq : Conserves q M)
    {before after : List Particle} (h : AllowsAmong M before after) :
    (before.map q).sum = (after.map q).sum := by
  obtain ⟨others, es₀, es, hc⟩ := h
  simp only [Model.check] at hc
  split at hc
  · cases hc
  · rename_i w h₀
    simp only [Bool.and_eq_true] at hc
    obtain ⟨hb, hc⟩ := hc
    split at hc
    · cases hc
    · rename_i w' h₁
      have pb := perm_sum ((List.isPerm_iff.mp hb).map q)
      have pa := perm_sum ((List.isPerm_iff.mp hc).map q)
      have := hq.run es w w' ⟨es₀, h₀⟩ h₁
      simp only [Model.total] at this
      simp only [List.map_append, List.sum_append] at pb pa
      omega

theorem ProtonStable.of_baryonConserved {M : Model} (h : BaryonConserved M) :
    ProtonStable M :=
  fun _ ha => (Conserves.among h ha).symm.trans (by decide)

end Suite
