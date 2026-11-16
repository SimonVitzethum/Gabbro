module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Memory
public import Grammatik.Logik.Vertraege.Pruefer.Control.Results
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Parameters
public import Grammatik.Logik.Vertraege.Pruefer.Witness.Control

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.SymbolicWitness

open Invarianten Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic
open Pruefer.Symbolic

abbrev declaration := Witness.u32Declaration
abbrev program := Witness.u32Program
abbrev u32 : Ty := .int 0 (2 ^ 32 - 1)
abbrev sumType : Ty := .int 0 (2 ^ 32 - 1 + 10)

def world : World declaration where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun _ => ⟨0, by decide, by decide⟩
  spur := []

def seven : Wert declaration u32 := ⟨7, by decide, by decide⟩
def actual : Env declaration [u32] := .cons seven .nil
def symbols : SymEnv declaration Nat [u32] := .cons (.integer (.var 0)) .nil
def valuation : Frag.Assignment Nat := fun _ => 7

theorem bounded_zeuge : symbols.Bounded 1 :=
  ⟨fun key member => by have same := List.mem_singleton.mp member; subst key; decide, trivial⟩

theorem realizes_zeuge : symbols.Realizes valuation world actual := ⟨rfl, trivial⟩

def context : Context Unit 1 := Context.empty.weaken (by decide)

def initializer : Expr declaration [u32] [] sumType :=
  let argument : Expr declaration [u32] [] u32 := .var .here
  let memory : Expr declaration [u32] [] (.int 0 10) :=
    .glob false (fun _ member => (List.not_mem_nil member).elim)
  .add argument memory

def target (actual : Env declaration [u32]) (value : Wert declaration sumType)
    (_ : Unit) (_ : VC.Runtime program (fun _ => []) (SperrInv.leer declaration)) (world : World declaration) : Prop :=
  value.n = (actual.get .here).n + (world.globs false).n

def compiler : SelectCompiler context symbols sumType target :=
  fun _ _ symbol _ => do
    let encoded ← encodeValue symbol
    return {
      formula := .eq encoded.val (.add (.var (.inr 0)) (.var (.inl (.glob false))))
      sound := fun valuation _ _ _ world valid actual realized value selected => by
        have head : valuation 0 = (actual.get .here).n := by
          cases actual
          exact realized.1
        have number := encoded.property valuation world value selected
        change encoded.val.denote (values valuation world) = value.n at number
        change encoded.val.denote (values valuation world) = valuation 0 + (world.globs false).n at valid
        change value.n = _
        exact number.symm.trans (valid.trans (congrArg (· + (world.globs false).n) head)) }

def selected := Pruefer.Symbolic.selectValue symbols bounded_zeuge initializer target compiler

/-- A full-width parameter and a memory-dependent defining relation exercise
    the scalar continuation. No integer-domain budget is present in this API. -/
theorem selection_present_zeuge : selected.toOption.isSome = true := by rfl

def selection := selected.toOption.get selection_present_zeuge

/-- The real Cooper decision accepts the quantified relation, independently
    of both the u32 range cardinality and the actual memory observation. -/
theorem selection_decides_zeuge :
    decideB (VC.close (VC.lower selection.formula)) (VC.close_closed _) = true := by
  apply (VC.close_decide_true_iff _).mpr
  intro values
  apply (VC.lower_denote _ values).mpr
  change ∀ value : Int,
    ((0 ≤ value ∧ value ≤ 2 ^ 32 - 1 + 10) ∧
      value = values (.inr 0) + values (.inl (.glob false))) →
    value = values (.inr 0) + values (.inl (.glob false))
  exact fun _ guarded => guarded.2

def parameterDomain : Parameters declaration 0 [u32] :=
  (parameters 0 0 [u32]).toOption.get (by rfl)

theorem parameter_u32_no_enumeration_zeuge :
    parameterDomain.next = 1 ∧ parameterDomain.templates.length = 1 := by constructor <;> rfl

theorem parameter_coverage_zeuge (actual : Env declaration [u32]) (incoming : Frag.Assignment Nat) :
    ∃ symbols ∈ parameterDomain.templates, ∃ valuation,
      symbols.Realizes valuation world actual ∧ ∀ key, key < 0 → valuation key = incoming key :=
  parameterDomain.cover world actual incoming

theorem known_environment_zeuge :
    (SymEnv.ofEnv actual : SymEnv declaration Nat [u32]).concrete?.isSome = true := by rfl

theorem world_correspondence_zeuge :
    symbols.Realizes valuation world actual ↔
      symbols.Realizes valuation (world.schreibGlob false [] ⟨9, by decide, by decide⟩) actual :=
  symbols.realizes_world actual valuation _ _

theorem bounded_get_zeuge : (symbols.get .here).Bounded 1 :=
  symbols.bounded_get 1 bounded_zeuge .here

theorem value_bounded_mono_zeuge : (symbols.get .here).Bounded 2 :=
  (symbols.get .here).bounded_mono bounded_get_zeuge (by decide)

theorem environment_bounded_mono_zeuge : symbols.Bounded 2 :=
  symbols.bounded_mono bounded_zeuge (by decide)

theorem value_realizes_congr_zeuge :
    (symbols.get .here).Realizes valuation world seven ↔
      (symbols.get .here).Realizes (valuation.bind 1 9) world seven :=
  (symbols.get .here).realizes_congr 1 bounded_get_zeuge valuation (valuation.bind 1 9)
    (by
      intro key inside
      have same : key = 0 := by omega
      subst key
      rfl) world world seven

theorem environment_realizes_congr_zeuge :
    symbols.Realizes valuation world actual ↔ symbols.Realizes (valuation.bind 1 9) world actual :=
  symbols.realizes_congr 1 bounded_zeuge valuation (valuation.bind 1 9)
    (by
      intro key inside
      have same : key = 0 := by omega
      subst key
      rfl) world world actual

theorem values_bind_zeuge :
    values (valuation.bind 1 9) world = (values valuation world).bind (.inr 1) 9 :=
  values_bind valuation world 1 9

theorem values_read_zeuge : values valuation (world.lese [] [.inr false]) = values valuation world :=
  values_read valuation world [] [.inr false]

def predicate : Expr declaration [u32] [] .bool := .lt (.var .here) (.lit 10)
def predicateEncoding := (Invarianten.Frag.Symbolic.translate predicate symbols).toOption.get (by rfl)

theorem bool_iff_zeuge :
    wahr? (eval world predicate world actual) = true ↔ predicateEncoding.payload.denote (values valuation world) :=
  predicateEncoding.bool_iff valuation world actual realizes_zeuge

theorem liftPayload_represents_zeuge :
    Represents valuation world u32
      (liftPayload u32 (.add (.var (.glob false)) (.konst 7))) seven ↔
      Frag.Represents world u32 (.add (.var (.glob false)) (.konst 7)) seven :=
  liftPayload_represents u32 _ valuation world seven

def predicateContinuation : Continuation (program := program) (S := SperrInv.leer declaration) context [u32] where
  holds := fun _ _ world actual => wahr? (eval world predicate world actual) = true
  encode := fun _ _ symbols _ => do
    let encoded ← Invarianten.Frag.Symbolic.translate predicate symbols
    return {
      formula := encoded.payload
      sound := fun valuation _ _ _ world valid actual realized =>
        (encoded.bool_iff valuation world actual realized).mpr valid }

def goals : Pruefer.Symbolic.Goals (program := program) (S := SperrInv.leer declaration)
    context (vertragVon declaration ()) [u32] where
  normal := predicateContinuation
  escape := predicateContinuation
  again := predicateContinuation
  returned := predicateContinuation
  reason := {
    holds := fun _ _ _ _ => True
    encode := fun _ _ _ _ => .ok {
      formula := .tru
      sound := fun _ _ _ _ _ _ _ _ => trivial } }

theorem goals_holds_shrink_zeuge (runtime : VC.Runtime program (fun _ => []) (SperrInv.leer declaration)) :
    (goals.shrink u32).holds (l := false) () runtime (fun _ => False) (.ok world (.cons seven actual)) ↔
      goals.holds (l := false) () runtime (fun _ => False) (.ok world actual) :=
  goals.holds_shrink u32 () runtime (fun _ => False) (.ok world (.cons seven actual))

theorem goals_endHolds_shrink_zeuge (runtime : VC.Runtime program (fun _ => []) (SperrInv.leer declaration)) :
    (goals.shrink u32).endHolds (l := false) () runtime (fun _ => False)
      (.zurueck world seven : EndAusgang (vertragVon declaration ()) false [u32, u32]) ↔
      goals.endHolds (l := false) () runtime (fun _ => False) (.zurueck world seven) :=
  goals.endHolds_shrink u32 () runtime (fun _ => False) (.zurueck world seven)

def nine : Wert declaration (.int 0 10) := ⟨9, by decide, by decide⟩

def storeTarget (_ : Unit) (_ : VC.Runtime program (fun _ => []) (SperrInv.leer declaration))
    (world : World declaration) (actual : Env declaration [u32]) : Prop :=
  (world.globs false).n = 9 ∧ (actual.get .here).n = 7

def storePost : Certificate context (fun valuation item runtime world => ∀ actual,
    symbols.Realizes valuation world actual → storeTarget item runtime world actual) where
  formula := .and (.eq (.var (.inl (.glob false))) (.konst 9)) (.eq (.var (.inr 0)) (.konst 7))
  sound := fun valuation _ _ _ world valid actual realized => by
    have head : valuation 0 = (actual.get .here).n := by cases actual; exact realized.1
    change (world.globs false).n = 9 ∧ valuation 0 = 7 at valid
    exact ⟨valid.1, head.symm.trans valid.2⟩

def stored := storeCondition symbols bounded_zeuge (.known nine) trivial (.glob false)
  (fun world value => world.schreibGlob false [] value)
  (fun world value => VC.assignment_schreibGlob world false [] value) storeTarget storePost

theorem store_formula_zeuge : stored.formula.denote (values valuation world) := by
  change ∀ value : Int, value = 9 → value = 9 ∧ (7 : Int) = 7
  exact fun _ same => ⟨same, rfl⟩

theorem store_correspondence_zeuge (runtime : VC.Runtime program (fun _ => []) (SperrInv.leer declaration)) :
    storeTarget () runtime (world.schreibGlob false [] nine) actual :=
  stored.sound valuation () trivial runtime world store_formula_zeuge actual realizes_zeuge nine rfl

theorem swapKey_twice_zeuge :
    swapKey (.inl (.glob false)) (.inr 1)
      (swapKey (.inl (.glob false)) (.inr 1) (.inl (.glob true) : Key declaration Nat)) = .inl (.glob true) :=
  swapKey_twice _ _ _

theorem swapKey_injective_zeuge :
    swapKey (.inl (.glob false)) (.inr 1) (.inl (.glob false) : Key declaration Nat) ≠
      swapKey (.inl (.glob false)) (.inr 1) (.inl (.glob true)) := by
  intro same
  have impossible := swapKey_injective _ _ same
  cases impossible

theorem values_store_swap_zeuge :
    values (valuation.bind 1 9) world ∘ swapKey (.inl (.glob false)) (.inr 1) =
      values (valuation.bind 1 (Frag.assignment world (.glob false))) (world.schreibGlob false [] nine) :=
  values_store_swap valuation world (world.schreibGlob false [] nine) 1 (.glob false) 9
    (VC.assignment_schreibGlob world false [] nine)

def frozenContext : Context (Env declaration [u32]) 1 where
  holds := fun valuation entry => symbols.Realizes valuation world entry
  stable := fun valuation other entry agree =>
    symbols.realizes_congr 1 bounded_zeuge valuation other agree world world entry

theorem frozen_context_extension_zeuge :
    frozenContext.holds (valuation.bind 1 9) actual := by
  apply (frozenContext.stable valuation (valuation.bind 1 9) actual _).mp realizes_zeuge
  intro key inside
  have same : key = 0 := by omega
  subst key
  rfl

def mixedDomain : Parameters declaration 2 [u32, .bool, u32] :=
  (parameters 2 2 [u32, .bool, u32]).toOption.get (by rfl)

theorem mixed_parameter_cases_zeuge : mixedDomain.next = 5 ∧ mixedDomain.templates.length = 2 := by
  constructor <;> rfl

theorem mixed_parameter_coverage_zeuge :
    ∃ symbols ∈ mixedDomain.templates, ∃ valuation,
      symbols.Realizes valuation world (.cons seven (.cons true (.cons seven .nil))) ∧
      ∀ key, key < 2 → valuation key = 42 :=
  mixedDomain.cover world (.cons seven (.cons true (.cons seven .nil))) (fun _ => 42)

def resultPost : Expr declaration (ErgCtx [u32] (some u32)) [] .bool :=
  .eq (.var .here) (.var (.there .here))

def resultProgram : Programm declaration :=
  { program with
    ensures := fun _ => resultPost
    rumpf := fun _ => .ret (.val (.var .here)) (List.Perm.refl _) }

def resultTarget (value : ErgVal declaration (some u32)) (entry : Env declaration [u32])
    (_ : VC.Runtime resultProgram (fun _ => []) (SperrInv.leer declaration)) (_ : World declaration) : Prop :=
  value.n = (entry.get .here).n

def resultCompiler : ResultCompiler frozenContext (some u32) resultTarget :=
  fun _ _ resultSymbols _ => do
    let encoded ← encodeValue (resultSymbols.get .here)
    return {
      formula := .eq encoded.val (.var (.inr 0))
      sound := fun valuation entry present _ world valid value realized => by
        change symbols.Realizes valuation _ entry at present
        have input : valuation 0 = (entry.get .here).n := by cases entry; exact present.1
        have selected := resultSymbols.realizes_get (ergEnv (some u32) value .nil) valuation world .here realized
        have number := encoded.property valuation world value selected
        change encoded.val.denote (values valuation world) = value.n at number
        change encoded.val.denote (values valuation world) = valuation 0 at valid
        exact number.symm.trans (valid.trans input) }

def resultCandidate := resultCondition symbols bounded_zeuge 0 (some u32)
  (resultProgram.ensures ()) resultTarget resultCompiler

theorem result_present_zeuge : resultCandidate.toOption.isSome = true := by rfl
def resultCertificate : Certificate frozenContext
    (fun valuation entry (runtime : VC.Runtime resultProgram (fun _ => []) (SperrInv.leer declaration)) world =>
      ∀ old actual, symbols.Realizes valuation old actual → ∀ value,
      wahr? (eval old (resultProgram.ensures ()) world (ergEnv (some u32) value actual)) = true →
      resultTarget value entry runtime world) :=
  resultCandidate.toOption.get result_present_zeuge

/-- A genuine identity contract over all u32 answers is discharged with one
    quantified result. This witnesses the result rule, not the pending gate switch. -/
theorem result_decides_zeuge :
    decideB (VC.close (VC.lower resultCertificate.formula)) (VC.close_closed _) = true := by
  apply (VC.close_decide_true_iff _).mpr
  intro values
  apply (VC.lower_denote _ values).mpr
  change ∀ value : Int, ((0 ≤ value ∧ value ≤ 2 ^ 32 - 1) ∧ value = values (.inr 0)) →
    value = values (.inr 0)
  exact fun _ guarded => guarded.2

theorem result_correspondence_zeuge
    (runtime : VC.Runtime resultProgram (fun _ => []) (SperrInv.leer declaration)) :
    resultTarget seven actual runtime world :=
  resultCertificate.sound valuation actual realizes_zeuge runtime world
    ((VC.lower_denote resultCertificate.formula (values valuation world)).mp
      (VC.close_sound (VC.lower resultCertificate.formula) result_decides_zeuge (values valuation world)))
    world actual realizes_zeuge seven rfl

end Gabbro.Grammatik.Vertraege.Pruefer.SymbolicWitness
