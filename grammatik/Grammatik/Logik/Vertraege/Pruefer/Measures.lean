module

public import Grammatik.Logik.Vertraege.Pruefer.Duties
public import Grammatik.Logik.Vertraege.Pruefer.Control.Measure

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC Invarianten.Pruefer

open Invarianten.Frag.Symbolic Symbolic

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

/-- Semantic decrease obligations keep their original runtime meaning. -/
def measurePolicy (program : Programm D) (measure : Mass D) (cycle : D.Fn → Bool)
    (anchor : World D) (entry : List Nat) : CallObligation program where
  holds := fun f world locals => ReqAmEintritt program f world locals ∧
    (cycle f = true → lexLt (measure.wert f world locals) entry = true)
  requires := fun _ _ _ h => h.1

def measureEncoding (program : Programm D) (measure : Mass D) (cycle : D.Fn → Bool)
    (anchor : World D) (f : D.Fn) (symbols : SymEnv D Nat (D.params f))
    (bounded : symbols.Bounded next) (refined : Option (PLift (PtrVerfeinert program)) := none)
    (acyclic : Option (PLift (∀ g n, D.passt g n = true → cycle g = false)) := none) :
    CallPolicy program (entryContext symbols bounded) where
  semantic := fun item => measurePolicy program measure cycle anchor (measure.wert f anchor item.2)
  encode := fun _ _ g args _ => do
    let requires ← Invarianten.Frag.Symbolic.translate (program.requires g) args
    let outgoing ← measureTerms args (measure g)
    let incoming ← measureTerms symbols (measure f)
    return ⟨.and requires.payload (if cycle g then lexFormula outgoing.val incoming.val else .tru),
      fun valuation item present world actual realized => by
        have a := outgoing.property valuation world actual realized
        have entryRealized := (symbols.realizes_world item.2 valuation item.1 world).mp present
        have b := incoming.property valuation world item.2 entryRealized
        have a' : outgoing.val.map (fun term => term.denote (values valuation world)) =
            (measure.wert g world actual).map (fun n : Nat => (n : Int)) := by
          simpa only [Mass.wert, List.map_map, Function.comp_def] using a
        have b' : incoming.val.map (fun term => term.denote (values valuation world)) =
            (measure.wert f world item.2).map (fun n : Nat => (n : Int)) := by
          simpa only [Mass.wert, List.map_map, Function.comp_def] using b
        change (_ ∧ _) ↔ (_ ∧ _)
        apply and_congr (requires.bool_iff valuation world actual realized).symm
        rw [measure.wert_welt f anchor world item.2]
        cases selected : cycle g with
        | false => simp only [selected, Bool.false_eq_true, ↓reduceIte, LProp.denote, false_implies]
        | true =>
            simp only [selected, ↓reduceIte, true_implies]
            exact lexFormula_denote outgoing.val incoming.val (values valuation world) _ _ a' b'⟩
  -- A pointer target outside the cycle owes no descent: its requires is the whole obligation.
  indirect := match refined, acyclic with
    | some checked, some outside => some ⟨⟨checked.down, fun _ g n target _ _ required =>
        ⟨required, fun inCycle => by rw [outside.down g n target] at inCycle; cases inCycle⟩⟩⟩
    | _, _ => none

/-- The same checked WP proves MassPflicht when instantiated with massTor.
    The source cycle and all recursive call sites are the canonical ones. -/
theorem massPflicht_of_execution (measure : Mass D) (cycle : D.Fn → D.Fn → Bool)
    (anchor : World D) (f : D.Fn)
    (checked : ∀ locals, CheckedEnvironment (S := S)
      (measurePolicy program measure (cycle f) anchor (measure.wert f anchor locals)) f locals)
    (replay : AtomicReplay program f)
    (passes : Nat) (Q : AxEns D) (shared : D.Tab ⊕ D.Glob → Prop)
    (subset : ∀ carrier, shared carrier → AtomarAusgenommen carrier) :
    MassPflicht program passes Q S shared measure cycle f := by
  intro O frame locality hardware U havoc A atomic R respects noDecrease noPre world locals requires g inCycle returned
  let entry := measure.wert f anchor locals
  let policy := measurePolicy program measure (cycle f) anchor entry
  have gated : RespektiertRahmen program (massTor measure (cycle f) entry R) := by
    let gate := fun g next args => !(cycle f g && !(lexLt (measure.wert g next args) entry))
    have same : (fun g next args => if gate g next args then R g next args else .logik (Logik.abstieg g)) =
        massTor measure (cycle f) entry R := by
      funext g next args
      by_cases blocked : (cycle f g && !(lexLt (measure.wert g next args) entry)) = true
      · simp only [gate, massTor, blocked, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      · have declined : (cycle f g && !(lexLt (measure.wert g next args) entry)) = false :=
          Bool.eq_false_iff.mpr blocked
        simp only [gate, massTor, declined, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    rw [← same]
    exact respectsGate R respects gate Logik.abstieg
  have errors : ∀ h next args, policy.holds h next args → ∀ error,
      massTor measure (cycle f) entry R h next args = .logik error →
      ∀ g, error ≠ Logik.abstieg g := by
    intro h next args obligation error reply
    have disabled : (cycle f h && !(lexLt (measure.wert h next args) entry)) = false := by
      cases tested : cycle f h with
      | false => simp only [tested, Bool.false_and]
      | true => simp only [tested, obligation.2 tested, Bool.not_true, Bool.and_false]
    simp only [massTor, disabled, Bool.false_eq_true, ↓reduceIte] at reply
    intro g forbidden
    subst error
    exact noDecrease h next args g reply
  have valid := checkedEnvironment_atomic policy f locals (checked locals) replay shared subset
    O locality passes U havoc A atomic (massTor measure (cycle f) entry R) gated
    (fun error => ∀ g, error ≠ Logik.abstieg g) errors world requires
  have same := measure.wert_welt f anchor world locals
  dsimp only [entry] at valid
  rw [same, returned] at valid
  exact valid g rfl

/-- Unconditional totality also excludes every descent-gate error. This is
    independent of the measure and does not assume any oracle contract. -/
theorem massPflicht_of_basic (f : D.Fn) (checked : Basic.EndSafe S (program.rumpf f))
    (measure : Mass D) (cycle : D.Fn → D.Fn → Bool)
    (passes : Nat) (Q : AxEns D) (shared : D.Tab ⊕ D.Glob → Prop) :
    MassPflicht program passes Q S shared measure cycle f := by
  intro O _ _ _ U _ A _ R _ _ _ world locals _ g _
  exact Basic.noLogic checked O U A passes
    (massTor measure (cycle f) (measure.wert f world locals) R) world locals (.abstieg g)

/-- A totality certificate carries the descent duty directly. Other bodies
    retain the finite family of decideB-backed path VCs. -/
def checkMeasure (program : Programm D) (S : SperrInv D) (sources : LockSources S)
    (budget : VCBudget) (hint : Option (QF (Observation D)))
    (measure : Mass D) (cycle : D.Fn → D.Fn → Bool) (anchor : World D) (f : D.Fn)
    (refined : Option (PLift (PtrVerfeinert program)) := none)
    (acyclic : Option (PLift (∀ g n, D.passt g n = true → cycle f g = false)) := none) :
    Except Frag.Refusal (PLift (∀ passes Q shared,
      (∀ carrier, shared carrier → AtomarAusgenommen carrier) →
      MassPflicht program passes Q S shared measure cycle f)) :=
  match Basic.ending S sources budget.depth (program.rumpf f) with
  | some checked => .ok ⟨fun passes Q shared _ =>
      massPflicht_of_basic f checked.down measure cycle passes Q shared⟩
  | none => do
      if let some replay := atomicReplay? program f then
        let domain ← parameters (D := D) budget.expansion 0 (D.params f)
        let invariants ← invariantFormula program (D.invs.filter (schuldet f))
        let executions ← collect domain.templates.attach _ (fun entry =>
          checkEnvironment program S entry.val (domain.bounded entry.val entry.property)
            (measureEncoding program measure (cycle f) anchor f entry.val (domain.bounded entry.val entry.property)
              refined acyclic)
            sources budget hint invariants)
        return ⟨massPflicht_of_execution measure cycle anchor f
          (fun locals runtime world allowed safe required => by
            obtain ⟨symbols, member, valuation, realized, _⟩ := domain.cover world locals (fun _ => 0)
            exact (executions.down ⟨symbols, member⟩ (List.mem_attach _ _)) valuation (world, locals) realized
              runtime allowed safe required) replay.down⟩
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
  cases checkMeasure program S sources budget hint measure cycle anchor f <;> simp [Except.toOption]

end Gabbro.Grammatik.Vertraege.Pruefer
