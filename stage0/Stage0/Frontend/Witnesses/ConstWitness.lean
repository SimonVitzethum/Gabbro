module
public import Stage0.Frontend.ExportCorrectness
public import Grammatik.Parser.Elab.Konst.Scalar.Export
public import Grammatik.Parser.Elab.Generic.Body

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.Konst
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The same original predicate clauses are used at both call sites. -/
def signature : FnSig where
  art := "const"
  name := "increment"
  params := [("x", .range (.atom "u8") (.lit 0) (.lit 10) false)]
  res := some (.range (.atom "u8") (.lit 0) (.lit 11) false)
  fehler := none
  klauseln := [.needs (.bin ">" (.variable "x") (.lit 0)),
    .gives (.bin "==" .res (.bin "+" (.variable "x") (.lit 1)))]

def function : UKonstFn where
  name := "increment"
  params := [("x", .int 0 10)]
  erg := .int 0 11
  rumpf := .block [] (some (.ret (some (.bin "+" (.variable "x") (.lit 1)))))
  signature := signature

/-- This is the actual source collector, not a manually supplied different function. -/
theorem collected_zeuge :
    uKonstFns [.fnT signature function.rumpf] = [function] := rfl

/-- Two different arguments yield their checked exact results through the production pass. -/
theorem two_values_zeuge :
    ersetzeSExpr [function] (.call "increment" [.lit 3]) = .ok (.lit 4) ∧
    ersetzeSExpr [function] (.call "increment" [.lit 5]) = .ok (.lit 6) := by
  constructor <;> rfl

/-- Both source-derived certificates and KExpr denotations are generated together. -/
theorem two_certificates_zeuge :
    ∃ first : Scalar.CheckedCall function [function] [] [.lit 3],
    ∃ second : Scalar.CheckedCall function [function] [] [.lit 5],
      Scalar.checkCall function [function] [] [.lit 3] = .ok first ∧
      Scalar.checkCall function [function] [] [.lit 5] = .ok second ∧
      first.value = 4 ∧ second.value = 6 ∧
      first.quoted.syntax.evalInt = some 4 ∧ second.quoted.syntax.evalInt = some 6 := by
  let first := (Scalar.checkCall function [function] [] [.lit 3]).toOption.get (by decide)
  let second := (Scalar.checkCall function [function] [] [.lit 5]).toOption.get (by decide)
  exact ⟨first, second, by rfl, by rfl, by rfl, by rfl,
    first.syntaxValue, second.syntaxValue⟩

/-- A requires failure is a named contract refusal, never a literal. -/
theorem requires_refused_zeuge :
    ersetzeSExpr [function] (.call "increment" [.lit 0]) =
      .error "const contract violated at `increment`: requires failed" := rfl

/-- A false ensures clause is checked on the computed return value. -/
def wrongPost : UKonstFn :=
  { function with signature := { signature with klauseln :=
    [.needs (.bin ">" (.variable "x") (.lit 0)),
      .gives (.bin "==" .res (.variable "x"))] } }

theorem ensures_refused_zeuge :
    ersetzeSExpr [wrongPost] (.call "increment" [.lit 3]) =
      .error "const contract violated at `increment`: ensures failed" := rfl

/-- The C17 design keeps a runtime argument refused at the const boundary. -/
theorem open_refused_zeuge :
    ersetzeSExpr [function] (.call "increment" [.variable "runtime"]) =
      .error "const open argument at `increment`: certified substitution needs closed arguments" := rfl

/-- Intermediate overflow cannot be cancelled into an apparently valid result. -/
def overflows : UKonstFn :=
  { function with rumpf := .block [] (some (.ret (some
    (.bin "-" (.bin "+" (.variable "x") (.lit 11)) (.lit 11))))),
    signature := { signature with klauseln := [] } }

theorem overflow_refused_zeuge :
    ersetzeSExpr [overflows] (.call "increment" [.lit 3]) =
      .error "const range failure at `increment`: arithmetic overflow or no value" := rfl

/-- Parser-to-checker witness: two const calls with an actual contract in source text. -/
def characters : List Char :=
  ("const fn increment(x : u8 in 0 .. 10) -> u8 in 0 .. 11 ".toList ++
   "requires x > 0 ensures result == x + 1 { return x + 1; } ".toList ++
   "impl fn main() -> u64 { return increment(3) + increment(5); }".toList)

def text : String := String.ofList characters

theorem compiled_zeuge : (compile text).toOption.isSome = true := by decide +kernel

def result : Compiled text := (compile text).toOption.get compiled_zeuge

/-- The same checked result goes through AkzeptiertX and the ordinary lowering endpoint. -/
theorem source_pipeline_zeuge :
    compile text = .ok result ∧ CanonicalSourceProgram result ∧
      result.unit.fns.length = 1 ∧ OldSource.accepts result.unit result.program = .ok true :=
  ⟨except_ok_get compiled_zeuge, compile_source_program text result, by decide +kernel, result.accepted⟩

/-- The whole-image theorem remains the production one; const folding adds no runner. -/
theorem image_pipeline_zeuge [Runner.IR.Kern] [Senke.CloneOK]
    (K : Nat) (bytes : List Runner.B) (emitted : irBild text K = .ok bytes) :
    ∃ output : Emitted text K,
      emit text K = .ok output ∧ output.image.bytes = bytes ∧ output.Correct := by
  obtain ⟨output, he, hb, hc, _⟩ := irBild_correct text K bytes emitted
  exact ⟨output, he, hb, hc⟩

/-- A contracted const call in an initializer uses the same checked source path. -/
def initializerText : String := String.ofList
  ("const fn increment(x : u8 in 0 .. 10) -> u8 in 0 .. 11 ".toList ++
   "requires x > 0 ensures result == x + 1 { return x + 1; } ".toList ++
   "const ANSWER : u8 = increment(3); impl fn main() -> u8 { return ANSWER; }".toList)

theorem initializer_compiled_zeuge :
    (compile initializerText).toOption.isSome = true := by decide +kernel

/-- An outer constant cannot turn a same-named runtime parameter into a closed argument. -/
theorem parameter_shadow_zeuge :
    let items := [SItemTief.constT "x" (.atom "u8") (.one (.lit 3)),
      .fnT signature function.rumpf,
      .fnT { art := "impl", name := "main", params := [("x", .atom "u8")],
        res := some (.atom "u8"), fehler := none, klauseln := [] }
        (.block [] (some (.ret (some (.call "increment" [.variable "x"])))))]
    konstErsetzePipeline items =
      .error "const open argument at `increment`: certified substitution needs closed arguments" := by rfl

/-- Else-arm reason binders also shadow compile-time constant names. -/
theorem reason_shadow_zeuge :
    let env : Generic.Environment :=
      { declarations := [], constants := [], constantFunctions := [], aliases := [] }
    let bindings : Generic.Bindings := { values := [("reason", .lit 3)] }
    let body := SAnw.bindElse "value" none (.call "foreign" []) "reason"
      (.block [] (some (.ret (some (.call "increment" [.variable "reason"])))) )
    (Generic.rewriteBody env bindings body).run [] = .ok (body, []) := by rfl

/-- Generic specialization cannot bypass the original const contract. -/
theorem generic_contract_refused_zeuge :
    Generic.constantArgument 0 255 [function] [] (.call "increment" [.lit 0]) =
      .error "const contract violated at `increment`: requires failed" := rfl

/-- Boolean truth is not silently accepted as the integer one. -/
theorem argument_type_refused_zeuge :
    ersetzeSExpr [function] (.call "increment" [.tru]) =
      .error "const argument failure at `increment`: const type failure: expected an integer expression" := rfl

end Gabbro.Stage0.Frontend.ConstWitness
