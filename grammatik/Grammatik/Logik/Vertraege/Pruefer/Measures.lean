module

public import Grammatik.Logik.Vertraege.Pruefer.Duties
public import Grammatik.Logik.Terminierung.Mass

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC Invarianten.Pruefer

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

/-- Measure syntax reads parameters only. After complete typed parameter
    selection the tuple is constant. The surrounding path VC still decides
    whether a call with a false decrease is reachable. The anchor is the
    unit's actual initial world, not an assumed inhabitant of memory. -/
def measurePolicy (program : Programm D) (measure : Mass D) (cycle : D.Fn → Bool)
    (anchor : World D) (entry : List Nat) : CallPolicy program where
  holds := fun f world locals => ReqAmEintritt program f world locals ∧
    (cycle f = true → lexLt (measure.wert f world locals) entry = true)
  requires := fun _ _ _ h => h.1
  encode := fun f locals => do
    let requires ← translate (program.requires f) locals
    let decreases := !cycle f || lexLt (measure.wert f anchor locals) entry
    return ⟨conj (lower requires.payload) (if decreases then .tru else .fls), fun world => by
      rw [conj_denote]
      apply and_congr ((lower_denote _ _).trans (requires.bool_iff world).symm)
      have same := measure.wert_welt f anchor world locals
      dsimp only [decreases]
      rw [same]
      cases cycle f <;> cases lexLt (measure.wert f world locals) entry <;> simp [QF.denote]⟩

/-- The same checked WP proves MassPflicht when instantiated with massTor.
    The source cycle and all recursive call sites are the canonical ones. -/
theorem massPflicht_of_execution (measure : Mass D) (cycle : D.Fn → D.Fn → Bool)
    (anchor : World D) (f : D.Fn)
    (checked : ∀ locals, CheckedEnvironment (S := S)
      (measurePolicy program measure (cycle f) anchor (measure.wert f anchor locals)) f locals)
    (free : atomicFreeB program f = true)
    (passes : Nat) (Q : AxEns D) (shared : D.Tab ⊕ D.Glob → Prop)
    (subset : ∀ carrier, shared carrier → AtomarAusgenommen carrier) :
    MassPflicht program passes Q S shared measure cycle f := by
  intro O frame local hardware U havoc A atomic R respects noDecrease noPre world locals requires g inCycle returned
  let entry := measure.wert f anchor locals
  let policy := measurePolicy program measure (cycle f) anchor entry
  have gated : RespektiertRahmen program (massTor measure (cycle f) entry R) := by
    let gate := fun g next args => !(cycle f g && !(lexLt (measure.wert g next args) entry))
    have same : (fun g next args => if gate g next args then R g next args else .logik (Logik.abstieg g)) =
        massTor measure (cycle f) entry R := by
      funext g next args
      dsimp only [gate, massTor]
      cases cycle f g && !(lexLt (measure.wert g next args) entry) <;> rfl
    rw [← same]
    exact respectsGate R respects gate Logik.abstieg
  have errors : ∀ h next args, policy.holds h next args → ∀ error,
      massTor measure (cycle f) entry R h next args = .logik error →
      ∀ g, error ≠ Logik.abstieg g := by
    intro h next args obligation error reply
    have disabled : cycle f h && !(lexLt (measure.wert h next args) entry) = false := by
      cases tested : cycle f h with
      | false => simp only [tested, Bool.false_and]
      | true => simp only [tested, obligation.2 tested, Bool.not_true, Bool.and_false]
    simp only [massTor, disabled, Bool.false_eq_true, ↓reduceIte] at reply
    exact fun g => noDecrease h next args g reply
  have valid := checkedEnvironment_atomic policy f locals (checked locals) free shared subset
    O local passes U havoc A atomic (massTor measure (cycle f) entry R) gated
    (fun error => ∀ g, error ≠ Logik.abstieg g) errors world requires
  have same := measure.wert_welt f anchor world locals
  dsimp only [entry] at valid
  rw [same, returned] at valid
  exact valid g rfl

/-- A measure check is a finite family of decideB-backed path VCs. -/
def checkMeasure (program : Programm D) (S : SperrInv D) (sources : LockSources S)
    (budget : VCBudget) (hint : Option (QF (Observation D)))
    (measure : Mass D) (cycle : D.Fn → D.Fn → Bool) (anchor : World D) (f : D.Fn) :
    Except Refusal (PLift (∀ passes Q shared,
      (∀ carrier, shared carrier → AtomarAusgenommen carrier) →
      MassPflicht program passes Q S shared measure cycle f)) := do
  if free : atomicFreeB program f = true then
    let domain ← environments (D := D) budget.expansion (D.params f)
    let invariants ← invariantFormula program (D.invs.filter (schuldet f))
    let executions ← collect domain.values
      (fun locals => CheckedEnvironment (S := S)
        (measurePolicy program measure (cycle f) anchor (measure.wert f anchor locals)) f locals)
      (fun locals => checkEnvironment program S
        (measurePolicy program measure (cycle f) anchor (measure.wert f anchor locals)) sources budget hint f invariants locals)
    return ⟨massPflicht_of_execution measure cycle anchor f
      (fun locals => executions.down locals (domain.complete locals)) free⟩
  else .error (.unsupported "decreases body reads atomic memory outside the checked VC fragment")

/-- Public Bool for the source decreases obligation of one function. -/
def MassGeprueftB (program : Programm D) (S : SperrInv D) (sources : LockSources S)
    (budget : VCBudget) (hint : Option (QF (Observation D)))
    (measure : Mass D) (cycle : D.Fn → D.Fn → Bool) (anchor : World D) (f : D.Fn) : Bool :=
  (checkMeasure program S sources budget hint measure cycle anchor f).toOption.isSome

theorem MassGeprueftB_iff (program : Programm D) (S : SperrInv D) (sources : LockSources S)
    (budget : VCBudget) (hint : Option (QF (Observation D)))
    (measure : Mass D) (cycle : D.Fn → D.Fn → Bool) (anchor : World D) (f : D.Fn) :
    MassGeprueftB program S sources budget hint measure cycle anchor f = true ↔
      ∃ certificate, checkMeasure program S sources budget hint measure cycle anchor f = .ok certificate := by
  unfold MassGeprueftB
  cases checkMeasure program S sources budget hint measure cycle anchor f <;> simp

end Gabbro.Grammatik.Vertraege.Pruefer
