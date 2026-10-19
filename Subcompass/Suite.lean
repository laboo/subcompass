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

end Suite
