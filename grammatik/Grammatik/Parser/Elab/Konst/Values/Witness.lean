module
public import Grammatik.Parser.Elab.Konst.ErsetzungTor

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Values.Witness
open Uebersetze Scalar
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def positive : UKonstFn where
  name := "positive"
  params := [("x", .int 0 10)]
  erg := .bool
  rumpf := .block [] (some (.ret (some (.bin ">" (.variable "x") (.lit 0)))))
  signature := { art := "const", name := "positive", params := [("x", .range (.atom "u8") (.lit 0) (.lit 10) false)],
    res := some (.atom "bool"), fehler := none, klauseln :=
      [.gives (.bin "==" .res (.bin ">" (.variable "x") (.lit 0)))] }

/-- Both Boolean values are delivered, with the original ensures retained. -/
theorem bool_values_zeuge :
    ersetzeSExpr [positive] (.call "positive" [.lit 3]) = .ok .tru ∧
    ersetzeSExpr [positive] (.call "positive" [.lit 0]) = .ok .fls := ⟨rfl, rfl⟩

def optional : UKonstFn where
  name := "optional"
  params := [("x", .int 0 3)]
  erg := .opt 4
  rumpf := .block [] (some (.ret (some (.call "Some" [.variable "x"])))))
  signature := { art := "const", name := "optional", params := [("x", .range (.atom "u8") (.lit 0) (.lit 3) false)],
    res := some (.index true "Slots"), fehler := none, klauseln := [] }

def absent : UKonstFn :=
  { optional with name := "absent", params := [],
    rumpf := .block [] (some (.ret (some (.call "None" [])))),
    signature := { optional.signature with name := "absent", params := [] } }

/-- Option absence and the actual present index remain distinct typed values. -/
theorem option_values_zeuge :
    ersetzeSExpr [optional] (.call "optional" [.lit 3]) = .ok (.call "Some" [.lit 3]) ∧
    ersetzeSExpr [absent] (.call "absent" []) = .ok (.call "None" []) := ⟨rfl, rfl⟩

def schema : USum :=
  { name := "Choice", cases := [("Empty", none), ("Data", some (.int 0 255)),
    ("Flag", some .bool), ("Text", some (.str 1))] }

def tagged : UKonstFn where
  name := "tagged"
  params := [("x", .int 0 10)]
  erg := .sum schema.spec
  rumpf := .block [] (some (.ret (some (.call "Data" [.bin "+" (.variable "x") (.lit 1)])))))
  signature := { art := "const", name := "tagged", params := [("x", .range (.atom "u8") (.lit 0) (.lit 10) false)],
    res := some (.atom "Choice"), fehler := none, klauseln := [] }
  sums := [schema]

def emptyTag : UKonstFn :=
  { tagged with params := [], rumpf := .block [] (some (.ret (some (.variable "Empty")))),
    signature := { tagged.signature with params := [] } }

def flagTag : UKonstFn :=
  { emptyTag with rumpf := .block [] (some (.ret (some (.call "Flag" [.tru])))) }

def textTag : UKonstFn :=
  { emptyTag with rumpf := .block [] (some (.ret (some (.call "Text" [.ext .text ["Z"] []])))) }

/-- Tag identity and complete numeric/Boolean/string payloads survive quotation. -/
theorem tag_values_zeuge :
    ersetzeSExpr [tagged] (.call "tagged" [.lit 4]) = .ok (.call "Data" [.lit 5]) ∧
    ersetzeSExpr [emptyTag] (.call "tagged" []) = .ok (.variable "Empty") ∧
    ersetzeSExpr [flagTag] (.call "tagged" []) = .ok (.call "Flag" [.tru]) ∧
    ersetzeSExpr [textTag] (.call "tagged" []) = .ok (.call "Text" [.ext .text ["Z"] []]) :=
  ⟨rfl, rfl, rfl, rfl⟩

def shortText (text : String) (maximum : Nat := 1) : UKonstFn where
  name := "shortText"
  params := []
  erg := .str maximum
  rumpf := .block [] (some (.ret (some (.ext .text [text] []))))
  signature := { art := "const", name := "shortText", params := [],
    res := some (.str (.lit maximum)), fehler := none, klauseln := [] }

/-- Empty and one-byte results preserve the actual UTF-8 spelling and length. -/
theorem string_values_zeuge :
    ersetzeSExpr [shortText ""] (.call "shortText" []) = .ok (.ext .text [""] []) ∧
    ersetzeSExpr [shortText "A"] (.call "shortText" []) = .ok (.ext .text ["A"] []) := ⟨rfl, rfl⟩

/-- The production collector binds the Boolean fixture to its actual source signature. -/
theorem bool_collected_zeuge :
    collectFunctions [.fnT positive.signature positive.rumpf] = .ok [positive] := rfl

/-- A zero-byte maximum is checked separately from an empty string under maximum one. -/
theorem zero_string_zeuge :
    ersetzeSExpr [shortText "" 0] (.call "shortText" []) = .ok (.ext .text [""] []) := rfl

def reasonTag : UKonstFn where
  name := "reasonTag"
  params := []
  erg := .why 2
  rumpf := .block [] (some (.ret (some (.why "Reason" "Second"))))
  signature := { art := "const", name := "reasonTag", params := [],
    res := some (.atom "Reason"), fehler := none, klauseln := [] }
  sums := [{ name := "Foreign", cases := [("Other", none), ("Second", none)] },
    { name := "Reason", cases := [("First", none), ("Second", none)] }]

/-- Ordinary reason-tag values keep both their owner and the exact selected case. -/
theorem reason_value_zeuge :
    ersetzeSExpr [reasonTag] (.call "reasonTag" []) = .ok (.why "Reason" "Second") := rfl

theorem foreign_reason_refused_zeuge :
    ersetzeSExpr [{ reasonTag with rumpf := .block [] (some (.ret (some (.why "Foreign" "Second")))) }]
      (.call "reasonTag" []) = .error "const reason owner is unknown: Foreign" := rfl

/-- The witnesses instantiate the generic G/literal theorem jointly with a
    successfully generated certificate and a checked complete result value. -/
theorem portable_call_sound_zeuge :
    ∃ call : Values.CheckedCall optional [optional] [] [.lit 3],
      Values.checkCall optional [optional] [] [.lit 3] = .ok call ∧
      call.value = some (⟨3, by decide, by decide⟩ : Zahl 0 3) ∧
      ∀ σ O passes depth,
        rufAt call.function.model.program O passes (depth + 1) () σ call.args = .ok σ call.value ∧
        eval σ call.quoted.expr σ call.args = call.value := by
  let call := (Values.checkCall optional [optional] [] [.lit 3]).toOption.get (by decide)
  refine ⟨call, by rfl, by rfl, ?_⟩
  intro σ O passes depth
  exact ⟨(call.sound σ O passes depth).1, (call.sound σ O passes depth).2.1⟩

/-- The wrong result type never becomes a neutral integer or a success. -/
theorem bool_type_refused_zeuge :
    ersetzeSExpr [{ positive with rumpf := .block [] (some (.ret (some (.lit 1)))) }]
      (.call "positive" [.lit 3]) = .error "const value has a different declared type" := rfl

theorem option_bound_refused_zeuge :
    ersetzeSExpr [{ optional with params := [],
      rumpf := .block [] (some (.ret (some (.call "Some" [.lit 4])))) }]
      (.call "optional" []) = .error "const value interval is outside its declared type" := rfl

theorem tag_payload_refused_zeuge :
    ersetzeSExpr [{ emptyTag with rumpf := .block [] (some (.ret (some (.call "Data" [.tru])))) }]
      (.call "tagged" []) = .error "const value has a different declared type" := rfl

theorem tag_unknown_refused_zeuge :
    ersetzeSExpr [{ emptyTag with rumpf := .block [] (some (.ret (some (.variable "Foreign")))) }]
      (.call "tagged" []) = .error "const tagged constructor is unknown: Foreign" := rfl

theorem string_utf8_bound_refused_zeuge :
    ersetzeSExpr [shortText "é"] (.call "shortText" []) =
      .error "const string literal exceeds its declared maximum" := rfl

theorem wide_string_refused_zeuge :
    ersetzeSExpr [shortText "A" 2] (.call "shortText" []) =
      .error "const result type without a certified replacement at `shortText`" := rfl

theorem portable_post_refused_zeuge :
    ersetzeSExpr [{ positive with signature := { positive.signature with klauseln := [.gives .fls] } }]
      (.call "positive" [.lit 3]) =
      .error "const contract violated at `positive`: ensures failed" := rfl

def captured : UKonstFn where
  name := "captured"
  params := [("x", .int 0 10)]
  erg := .int 0 20
  rumpf := .block [] (some (.ret (some (.bin "+" (.variable "x") (.variable "math::K")))))
  signature := { art := "const", name := "captured", params := [("x", .range (.atom "u8") (.lit 0) (.lit 10) false)],
    res := some (.range (.atom "u8") (.lit 0) (.lit 20) false), fehler := none, klauseln := [] }
  constants := [("math::K", 5), ("x", 99)]

/-- Original global names in both body and arguments reach their certificates.
    The parameter x shadows the captured global x even in the body derivation. -/
theorem qualified_normalization_zeuge :
    ersetzeSExpr [captured] (.call "captured" [.bin "+" (.variable "math::K") (.lit 1)]) =
      .ok (.lit 11) := rfl

theorem normalization_denotation_zeuge :
    ∃ call : Scalar.CheckedCall captured [captured] captured.constants
        [.bin "+" (.variable "math::K") (.lit 1)],
      Scalar.checkCall captured [captured] captured.constants
        [.bin "+" (.variable "math::K") (.lit 1)] = .ok call ∧ call.value = 11 ∧
      ∀ before after,
        uKonstWert call.lo call.hi [captured] call.bindings 64
          (normalizeNames (locals captured.params) captured.constants call.function.source) =
          some (eval before call.function.model.body.2.2.expr after call.args).n := by
  let call := (Scalar.checkCall captured [captured] captured.constants
    [.bin "+" (.variable "math::K") (.lit 1)]).toOption.get (by decide)
  exact ⟨call, by rfl, by rfl, call.normalized_denotation⟩

/-- Runtime binders cannot be closed using a same-named global. -/
theorem original_parameter_refused_zeuge :
    ersetzeSAnwIn ["x"] [captured]
      (.ret (some (.call "captured" [.variable "x"]))) =
      .error "const open argument at `captured`: certified substitution needs closed arguments" := rfl

/-- Quantifier variables, sequential locals and pattern payloads also remain open. -/
theorem binder_refused_zeuge :
    ersetzeSExpr [captured] (.ext .all ["x", "slots", "Slots"]
      [.call "captured" [.variable "x"]]) =
      .error "const open argument at `captured`: certified substitution needs closed arguments" ∧
    ersetzeSAnw [captured] (.block [.bind false "x" none (.lit 2)]
      (some (.ret (some (.call "captured" [.variable "x"]))))) =
      .error "const open argument at `captured`: certified substitution needs closed arguments" ∧
    ersetzeSAnw [captured] (.arm "Data" (some "x")
      (.ret (some (.call "captured" [.variable "x"])))) =
      .error "const open argument at `captured`: certified substitution needs closed arguments" :=
  ⟨rfl, rfl, rfl⟩

/-- The normalization induction has a non-degenerate original qualified-name fixture. -/
theorem source_meaning_normalized_zeuge :
    let D := declaration [] (.int 0 10)
    let source := SExpr.bin "+" (.variable "module::K") (.lit 1)
    ∃ normalized : Normalized (D := D) [] [("module::K", 5)] source,
      normalize [] [("module::K", 5)] source = .ok normalized ∧
      Scalar.expression [] (normalizeNames ([] : Locals []) [("module::K", 5)] source) =
        .ok normalized.code ∧ normalized.code.1 = .int 6 6 := by
  dsimp only
  let normalized := (normalize (D := declaration [] (.int 0 10)) [] [("module::K", 5)]
    (.bin "+" (.variable "module::K") (.lit 1))).toOption.get (by decide)
  exact ⟨normalized, by rfl, normalized.meaning.normalized, by rfl⟩

theorem integer_argument_normalized_denotation_zeuge :
    ∃ argument : IntegerArgument [] [("module::K", 5)] 0 10
        (.bin "+" (.variable "module::K") (.lit 1)) 6,
      ∀ before after,
        uKonstWert 0 10 [] [] 64
          (normalizeNames ([] : Locals []) [("module::K", 5)]
            (.bin "+" (.variable "module::K") (.lit 1))) =
          some (eval before argument.code.expr after .nil).n := by
  let normalized := (normalize (D := declaration [] (.int 0 10)) [] [("module::K", 5)]
    (.bin "+" (.variable "module::K") (.lit 1))).toOption.get (by decide)
  let argument : IntegerArgument [] [("module::K", 5)] 0 10
      (.bin "+" (.variable "module::K") (.lit 1)) 6 :=
    ⟨normalized, 6, 6, Code.add (Code.literal 5) (Code.literal 1), by rfl, by rfl, by rfl⟩
  exact ⟨argument, argument.normalized_denotation⟩

/-- The common replacement theorem has success, exact value and soundness jointly. -/
theorem replacement_sound_zeuge :
    ∃ replacement : Replacement optional [optional] [] [.lit 3],
      checkReplacement optional [optional] [] [.lit 3] = .ok replacement ∧
      replacement.syntax = .call "Some" [.lit 3] ∧ replacement.evidence.Sound := by
  let replacement := (checkReplacement optional [optional] [] [.lit 3]).toOption.get (by decide)
  exact ⟨replacement, by rfl, by rfl, replacement.sound⟩

/-- The production theorem derives the certificate from actual substitution success. -/
theorem substitution_certified_zeuge :
    ∃ checked : Replacement optional [optional] [] [.lit 3],
      checkReplacement optional [optional] [] [.lit 3] = .ok checked ∧
      SExpr.call "Some" [.lit 3] = checked.syntax ∧ checked.evidence.Sound := by
  exact ersetzeSExpr_call_certified [] [optional] "optional" [.lit 3] [.lit 3]
    optional (.call "Some" [.lit 3]) (by rfl) (by rfl) (by rfl)

/-- Generic quotation is instantiated with a complete noninteger G value. -/
theorem reify_denotes_zeuge :
    let D := declaration [] .bool
    ∃ literal : Reified D [] [] .bool true,
      reify [] [] 64 .bool true = .ok literal ∧ literal.syntax = .tru ∧
      ∀ before after, eval before literal.expr after .nil = true := by
  dsimp only
  let literal := (reify (D := declaration [] .bool) (Γ := []) [] [] 64 .bool true).toOption.get (by decide)
  exact ⟨literal, by rfl, by rfl, fun before after => reify_denotes literal before after .nil⟩

end Gabbro.Grammatik.Parser.Konst.Values.Witness
