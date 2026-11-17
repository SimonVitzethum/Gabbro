module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Composition
public import Grammatik.Logik.Vertraege.Pruefer.Witness.Symbolic

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.SymbolicBindingWitness

open Invarianten Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic
open Pruefer.Symbolic

abbrev declaration := SymbolicWitness.declaration
abbrev u32 := SymbolicWitness.u32
abbrev symbols := SymbolicWitness.symbols
abbrev context := SymbolicWitness.frozenContext

def initializer : Expr declaration [u32] [] (.int 0 10) :=
  .glob false (fun _ member => (List.not_mem_nil member).elim)

def returned : ErgExpr declaration [.int 0 10, u32] [] (some u32) :=
  .val (.widen (by decide) (by decide) (.var .here))

def tailCode : Endblock declaration (vertragVon declaration ()) false [.int 0 10, u32] [] :=
  .ret returned (List.Perm.refl _)

def body : Endblock declaration (vertragVon declaration ()) false [u32] [] :=
  .bind initializer tailCode

def postcondition : Expr declaration [u32, u32] [] .bool :=
  .le (.var .here) (.add (.var (.there .here))
    (.glob false (fun _ member => (List.not_mem_nil member).elim)))

/-- All 2^32 parameter values are admitted; the read result varies with memory.
    The post is value-dependent and needs the parameter's proved lower bound. -/
def program : Programm declaration :=
  { SymbolicWitness.program with
    requires := fun _ => .tru
    ensures := fun _ => postcondition
    rumpf := fun _ => body }

def post : Continuation (program := program) (S := SperrInv.leer declaration) context [u32] where
  holds := fun entry _ world actual => (actual.get .here).n ≤ (entry.get .here).n + (world.globs false).n
  encode := fun _ _ resultSymbols _ => do
    let encoded ← encodeValue (resultSymbols.get .here)
    return {
      formula := .le encoded.val (.add (.var (.inr 0)) (.var (.inl (.glob false))))
      sound := fun valuation entry present _ world valid actual realized => by
        change symbols.Realizes valuation _ entry at present
        have input : valuation 0 = (entry.get .here).n := by cases entry; exact present.1
        have selected := resultSymbols.realizes_get actual valuation world .here realized
        have number := encoded.property valuation world (actual.get .here) selected
        change encoded.val.denote (values valuation world) = (actual.get .here).n at number
        change encoded.val.denote (values valuation world) ≤ valuation 0 + (world.globs false).n at valid
        change (actual.get .here).n ≤ _
        rw [← number, ← input]
        exact valid }

def goals : Pruefer.Symbolic.Goals (program := program) (S := SperrInv.leer declaration)
    context (vertragVon declaration ()) [u32] where
  normal := Continuation.truth context
  escape := Continuation.truth context
  again := Continuation.truth context
  returned := post
  reason := Continuation.truth context

def candidate : Except Frag.Refusal (Pruefer.Symbolic.EndCondition (fun _ => requiresObligation program) body symbols goals) :=
  bindEndCondition (V := vertragVon declaration ()) (l := false)
  (fun _ => requiresObligation program) symbols SymbolicWitness.bounded_zeuge initializer tailCode goals
  (fun _more larger symbol bounded =>
    retEndCondition (V := vertragVon declaration ()) (l := false)
      (fun _ => requiresObligation program) (.cons symbol symbols)
      ⟨bounded, symbols.bounded_mono SymbolicWitness.bounded_zeuge larger⟩
      returned (List.Perm.refl _) ((goals.weaken larger).shrink (.int 0 10)))

theorem candidate_present_zeuge : candidate.toOption.isSome = true := by rfl
def certificate : Pruefer.Symbolic.EndCondition (fun _ => requiresObligation program) body symbols goals :=
  candidate.toOption.get candidate_present_zeuge

def inputBounds : Frag.LProp (Key declaration Nat) :=
  .and (.le (.konst 0) (.var (.inr 0))) (.le (.var (.inr 0)) (.konst (2 ^ 32 - 1)))

/-- This is the actual quantified binding/return VC and the verified Cooper
    verdict, not a specialized run on a selected parameter inhabitant. -/
theorem quantified_binding_vc_zeuge :
    decideB (VC.close (VC.lower (.imp inputBounds certificate.formula))) (VC.close_closed _) = true := by
  apply (VC.close_decide_true_iff _).mpr
  intro values
  apply (VC.lower_denote _ values).mpr
  change (0 ≤ values (.inr 0) ∧ values (.inr 0) ≤ 2 ^ 32 - 1) →
    ∀ first : Int, ((0 ≤ first ∧ first ≤ 10) ∧ first = values (.inl (.glob false))) →
    ∀ second : Int, ((0 ≤ second ∧ second ≤ 2 ^ 32 - 1) ∧ second = first) →
      second ≤ values (.inr 0) + values (.inl (.glob false))
  intro bounds first initialized second returned
  have nonnegative := bounds.1
  have memory := initialized.2
  have value := returned.2
  omega

theorem post_correspondence_zeuge (entry : Env declaration [u32])
    (runtime : VC.Runtime program (fun _ => []) (SperrInv.leer declaration)) (old : World declaration)
    (allowed : Logik declaration → Prop) (outcome : EndAusgang (vertragVon declaration ()) false [u32])
    (valid : goals.endHolds entry runtime allowed outcome) : EndPost program () old entry allowed outcome := by
  cases outcome with
  | zurueck world value =>
      refine ⟨?_, ?_⟩
      · change value.n ≤ (entry.get .here).n + (world.globs false).n at valid
        change decide (value.n ≤ (entry.get .here).n + (world.globs false).n) = true
        exact decide_eq_true valid
      · intro item
        cases item
  | why world reason => intro item; cases item
  | leave impossible _ _ => cases impossible
  | next impossible _ _ => cases impossible
  | logik error => exact valid
  | hardware error => trivial

/-- Acceptance of the quantified VC implies the original runtime WP for every
    typed u32 parameter, memory world and admitted runtime. No Env is enumerated. -/
theorem runtime_binding_wp_zeuge (runtime : VC.Runtime program (fun _ => []) (SperrInv.leer declaration))
    (world : World declaration) (actual : Env declaration [u32]) (allowed : Logik declaration → Prop)
    (safe : HandlerSafe (requiresObligation program) runtime allowed) :
    runtime.wpE body (EndPost program () world actual allowed) world actual := by
  let valuation : Frag.Assignment Nat := fun _ => (actual.get .here).n
  have realized : symbols.Realizes valuation world actual := by
    cases actual with
    | cons value tail => cases tail; exact ⟨rfl, trivial⟩
  have frozen : context.holds valuation actual :=
    (symbols.realizes_world actual valuation world SymbolicWitness.world).mp realized
  have bounds : inputBounds.denote (values valuation world) :=
    ⟨(actual.get .here).lo_le, (actual.get .here).le_hi⟩
  have closed := (VC.lower_denote (.imp inputBounds certificate.formula) (values valuation world)).mp
    (VC.close_sound (VC.lower (.imp inputBounds certificate.formula))
      quantified_binding_vc_zeuge (values valuation world))
  have ready := certificate.sound valuation actual frozen runtime world (closed bounds) actual realized allowed safe
  exact post_correspondence_zeuge actual runtime world allowed _ ready

open SelectionWitness Invarianten.VC

def productionInvariants : InvariantFormula program (declaration.invs.filter (schuldet ())) :=
  (invariantFormula program []).toOption.get (by rfl)

def productionCompiled := ending (requiresPolicy program (entryContext symbols SymbolicWitness.bounded_zeuge))
  (S := SperrInv.leer declaration) (Invarianten.Pruefer.lockFormula (SperrInv.leer declaration) (fun _ => none)) { expansion := 0 } none 128 body
  symbols SymbolicWitness.bounded_zeuge (contractGoals program () symbols SymbolicWitness.bounded_zeuge productionInvariants)

theorem productionCompiled_present : productionCompiled.toOption.isSome = true := by with_unfolding_all rfl

def productionCertificate := productionCompiled.toOption.get productionCompiled_present

theorem productionCompiled_result : productionCompiled = .ok productionCertificate := by with_unfolding_all rfl

theorem production_vc_valid (values : Frag.Assignment (Key declaration Nat)) :
    (entryVC symbols .tru productionCertificate.formula).denote values := by
  intro _ input _
  change (0 ≤ values (.inr 0) ∧ values (.inr 0) ≤ 2 ^ 32 - 1) ∧ True at input
  with_unfolding_all
    change ∀ value : Int, ((0 ≤ value ∧ value ≤ 10) ∧ value = values (.inl (.glob false))) →
      ∀ returned : Int, ((0 ≤ returned ∧ returned ≤ 2 ^ 32 - 1) ∧ returned = value) →
        (returned ≤ values (.inr 0) + values (.inl (.glob false)) ∧ True)
    intro value guarded returned selected
    exact ⟨by omega, trivial⟩

attribute [local irreducible] entryVC productionCertificate

theorem production_decided :
    decideB (VC.close (VC.lower (entryVC symbols .tru productionCertificate.formula)))
      (VC.close_closed _) = true := by
  apply (VC.close_decide_true_iff (VC.lower (entryVC symbols .tru productionCertificate.formula))).mpr
  intro values
  exact (VC.lower_denote (entryVC symbols .tru productionCertificate.formula) values).mpr (production_vc_valid values)

/-- The production entry gate accepts the real binder/return program with a
    nonliteral, parameter-dependent post and zero enumeration budget. -/
theorem production_u32_acceptance_zeuge :
    (checkExecution program (SperrInv.leer declaration) (fun _ => none)
      { expansion := 0 } none ()).toOption.isSome = true := by
  with_unfolding_all
    apply execution_success program (SperrInv.leer declaration) (fun _ => none) { expansion := 0 } none ()
      (by rfl) productionInvariants (by rfl)
      ((parameters (D := declaration) 0 0 [u32]).toOption.get (by with_unfolding_all rfl)) (by with_unfolding_all rfl)
    · change 1 ≤ 16384
      decide
    · intro entry
      rcases entry with ⟨selected, member⟩
      change selected ∈ [symbols] at member
      have same := List.mem_singleton.mp member
      subst selected
      let requirement := (Invarianten.Frag.Symbolic.translate (program.requires ()) symbols).toOption.get (by rfl)
      exact environment_success (D := declaration) (f := ()) (next := 1) program (SperrInv.leer declaration) symbols SymbolicWitness.bounded_zeuge
        (requiresPolicy program _) (fun _ => none) { expansion := 0 } none productionInvariants (by rfl)
        requirement (by rfl) productionCertificate productionCompiled_result production_decided

#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel

end Gabbro.Grammatik.Vertraege.Pruefer.SymbolicBindingWitness
