module

public import Grammatik.Logik.Vertraege.Pruefer.Control.CallBinding
public import Grammatik.Logik.Vertraege.Pruefer.Control.Symbolic

@[expose] public section

/-!
# Calls through a function pointer

A call `p(args)` reaches some target `f` conforming to the pointer's interface `n`; the
target is not known to the checker. The certificate quantifies over every conforming target:
the interface precondition is checked at the call, the interface postcondition is assumed at
the return, and the post-state is havoced over the interface's declared frame, which contains
every conforming target's frame (`SigPasst.schreibt`). Soundness uses the checked interface
refinement (`PtrVerfeinert`, decided by `checkPointers`) carried by the policy; without that
evidence the call is refused.
-/

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Symbolic

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}

/-- The observations an interface may change: its declared table and global frame. -/
def writtenSig (n : Nat) : Observation D → Bool
  | .glob name => (D.sigNr n).gschreibt name
  | .slot table _ _ => (D.sigNr n).schreibt table

/-- A conforming target changes nothing outside its interface's frame. -/
theorem frame_observation_sig {f : D.Fn} {n : Nat} (hf : D.passt f n = true) (world next : World D)
    (frame : Rahmen (D.schreibt f) (D.gschreibt f) world next)
    (key : Observation D) (unchanged : writtenSig n key = false) :
    assignment world key = assignment next key := by
  apply frame_observation f world next frame key
  cases key with
  | glob name =>
      show D.gschreibt f name = false
      cases written : D.gschreibt f name with
      | false => rfl
      | true =>
          have wider : (D.sigNr n).gschreibt name = true := (D.passt_sig hf).gschreibt name written
          simp only [writtenSig, wider] at unchanged
          cases unchanged
  | slot table field index =>
      show D.schreibt f table = false
      cases written : D.schreibt f table with
      | false => rfl
      | true =>
          have wider : (D.sigNr n).schreibt table = true := (D.passt_sig hf).schreibt table written
          simp only [writtenSig, wider] at unchanged
          cases unchanged

/-- The outcomes of a call through interface `n`, for every conforming target: a normal
    return meets the interface post over the interface frame, a reason may leave any world. -/
def indirectOutcomes {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) (n : Nat) (args : SymEnv D Nat (D.sigNr n).params) (argsBounded : args.Bounded next)
    (caller : SymEnv D Nat Γ) (callerBounded : caller.Bounded next)
    (target : Env D Γ → ErgVal D (D.sigNr n).erg → A → Runtime program (fun _ => []) S → World D → Prop)
    (failure : Env D Γ → Fin (D.sigNr n).gruende → A → Runtime program (fun _ => []) S → World D → Prop)
    (compile : ResultCompiler context caller (D.sigNr n).erg target)
    (compileFailure : ∀ reason, Except Frag.Refusal (Certificate context (fun valuation item runtime world =>
      ∀ actual, caller.Realizes valuation world actual → failure actual reason item runtime world)))
    (shared : Option (SharedResult context caller (D.sigNr n).erg target) := none) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      caller.Realizes valuation world actual → ∀ supplied, args.Realizes valuation world supplied →
      ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      ∀ f (hf : D.passt f n = true),
      match runtime.calls f world (umsig hf supplied) with
      | .ok after value => target actual (ptrResult hf value) item runtime after
      | .why after reason => failure actual (grundSig hf reason) item runtime after
      | .logik error => allowed error
      | .hardware _ => True)) := do
  let some evidence := policy.indirect
    | .error (.unsupported "contract indirect call needs checked interface refinement")
  let pre ← translate (program.ptrVertrag n).pre args
  let normal ← resultCondition args argsBounded caller callerBounded budget (D.sigNr n).erg
    (program.ptrVertrag n).post target compile shared none
  let failures ← allCertificates context (List.finRange (D.sigNr n).gruende)
    (fun reason valuation item runtime world => ∀ actual, caller.Realizes valuation world actual →
      ∀ after, failure actual reason item runtime after)
    (fun reason => do
      let tail ← compileFailure reason
      return {
        formula := havocFormula (fun _ => true) tail.formula
        sound := fun valuation item present runtime world valid actual realized after =>
          tail.sound valuation item present runtime after
            (havocFormula_sound (fun _ => true) tail.formula valuation world after valid
              (fun _ impossible => Bool.noConfusion impossible)) actual
            ((caller.realizes_world actual valuation world after).mp realized) })
  return {
    formula := .and pre.payload (.and (havocFormula (writtenSig n) normal.formula) failures.formula)
    sound := fun valuation item present runtime world valid actual realized supplied suppliedRealized
        allowed safe f hf => by
      have interfacePre : (program.ptrVertrag n).preHolds world supplied :=
        (pre.bool_iff valuation world supplied suppliedRealized).mpr valid.1
      have required : ReqAmEintritt program f world (umsig hf supplied) :=
        (evidence.down.refined f n hf).1 world supplied interfacePre
      have obligation := evidence.down.obliged item f n hf world (umsig hf supplied) required
      cases reply : runtime.calls f world (umsig hf supplied) with
      | ok after value =>
          have ensured : EnsAmRueck program f world after (umsig hf supplied) value :=
            safe.1.1 f world (umsig hf supplied) required after value reply
          have post := (evidence.down.refined f n hf).2 world after supplied value interfacePre ensured
          have transferred := havocFormula_sound (writtenSig n) normal.formula valuation world after valid.2.1
            (fun key unchanged => frame_observation_sig hf world after
              (runtime.evidence.frame f world (umsig hf supplied) after value reply) key unchanged)
          exact normal.sound valuation item present runtime after transferred world supplied
            suppliedRealized trivial actual ((caller.realizes_world actual valuation world after).mp realized)
            (ptrResult hf value) post
      | why after reason =>
          exact failures.sound valuation item present runtime world valid.2.2 (grundSig hf reason)
            (List.mem_finRange _) actual realized after
      | logik error => exact safe.2 f world (umsig hf supplied) obligation error reply
      | hardware error => trivial }

/-- The outcomes of a call through interface `n` without reasons, for every conforming target. -/
def indirectCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) (n : Nat) (args : SymEnv D Nat (D.sigNr n).params) (argsBounded : args.Bounded next)
    (caller : SymEnv D Nat Γ) (callerBounded : caller.Bounded next) (noReasons : (D.sigNr n).gruende = 0)
    (target : Env D Γ → ErgVal D (D.sigNr n).erg → A → Runtime program (fun _ => []) S → World D → Prop)
    (compile : ResultCompiler context caller (D.sigNr n).erg target)
    (shared : Option (SharedResult context caller (D.sigNr n).erg target) := none) :
    Except Frag.Refusal (Certificate context (fun valuation item runtime world => ∀ actual,
      caller.Realizes valuation world actual → ∀ supplied, args.Realizes valuation world supplied →
      ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      ∀ f (hf : D.passt f n = true),
      match runtime.calls f world (umsig hf supplied) with
      | .ok after value => target actual (ptrResult hf value) item runtime after
      | .why _ _ => False
      | .logik error => allowed error
      | .hardware _ => True)) :=
  indirectOutcomes policy budget n args argsBounded caller callerBounded target (fun _ _ _ _ _ => False)
    compile (fun reason => (Fin.cast noReasons reason).elim0) shared

/-- `p(args);`: the target is read from the operand world; every conforming target is covered. -/
def callIndCondition {context : Context A next} (policy : CallPolicy program context)
    (budget : Nat) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
    (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.StatementCondition (l := l) policy.semantic
      (.callInd p args hp hr) symbols goals) := do
  let pre ← Symbolic.arguments budget args symbols bounded
    (fun actual supplied item runtime world => ∀ allowed, HandlerSafe (policy.semantic item) runtime allowed →
      ∀ f (hf : D.passt f n = true),
      match runtime.calls f world (umsig hf supplied) with
      | .ok after _ => goals.normal.holds item runtime after actual
      | .why _ _ => False
      | .logik error => allowed error
      | .hardware _ => True)
    (fun more larger supplied suppliedBounded => do
      let normal ← goals.normal.encode more larger symbols (symbols.bounded_mono bounded larger)
      indirectCondition (policy.weaken larger) budget n supplied suppliedBounded symbols
        (symbols.bounded_mono bounded larger) hr
        (fun actual _ item runtime world => goals.normal.holds item runtime world actual)
        (fun _ beyond _ _ => .ok ((normal.weaken beyond).map
          (fun _ _ _ _ ready actual realized _ _ => ready actual realized)))
        (some (normal.map (fun _ _ _ _ ready actual realized _ => ready actual realized))))
  return (pre.read Λ (p.orte ++ args.orte)).map (fun valuation item runtime world ready actual realized allowed safe => by
    have ready := ready actual ((symbols.realizes_world actual valuation world
      (world.lese Λ (p.orte ++ args.orte))).mp realized) allowed safe
    unfold Runtime.wpS
    dsimp only [execStmtH]
    generalize eval (world.lese Λ (p.orte ++ args.orte)) p (world.lese Λ (p.orte ++ args.orte)) actual = pointer at ⊢
    obtain ⟨f, hf⟩ := pointer
    dsimp only
    have ready := ready f hf
    cases reply : runtime.calls f (world.lese Λ (p.orte ++ args.orte))
      (umsig hf (evalArgs (world.lese Λ (p.orte ++ args.orte)) args (world.lese Λ (p.orte ++ args.orte)) actual)) <;>
      simpa only [reply, Symbolic.Goals.holds] using ready)

/-- The interface's view of a target's answer is the target's answer at the bound type. -/
theorem ergWert_cast {e₁ e₂ : Option Ty} (same : e₁ = e₂) (h₁ : e₁ = some τ) (h₂ : e₂ = some τ)
    (value : ErgVal D e₁) : ergWert h₁ value = ergWert h₂ (cast (congrArg (ErgVal D) same) value) := by
  subst same
  rfl

theorem ergWert_ptrResult {f : D.Fn} {n : Nat} (hf : D.passt f n = true) (he : (D.sigNr n).erg = some τ)
    (value : ErgVal D (D.erg f)) : ergWert (ergSig hf he) value = ergWert he (ptrResult hf value) :=
  ergWert_cast (D.passt_sig hf).erg _ he value

end Gabbro.Grammatik.Vertraege.Pruefer
