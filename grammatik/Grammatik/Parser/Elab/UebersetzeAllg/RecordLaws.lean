module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
public import Grammatik.Kern.Syntax.Syntax.ProduktZucker

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- The real expression lowerer emits the nominal constructor over the complete field list. -/
theorem record_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (identity : Nat) (reordered : Bool) (sides : List (Ty × USide))
    (args : Args (declOf u) Γ Λ (sides.map (·.1)))
    (gate : u.exportGate = .ok ())
    (lowered : lowProductArgs u Γ Λ fn er sides = .ok args)
    (schema : { s : URecord // s.ty = .prod identity (sides.map (·.1)) })
    (hschema : uRecordOf u.records (.prod identity (sides.map (·.1))) = .ok schema) :
    lowWertE u Γ Λ fn er (.product identity reordered sides) =
      .ok ⟨.prod identity (sides.map (·.1)), Expr.prod identity args⟩ := by
  simp only [lowWertE, gate, hschema, lowered, bind, Except.bind]

/-- Empty products use the canonical empty argument list in the same lexical/result scope. -/
theorem lowProductArgs_nil (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) : lowProductArgs u Γ Λ fn er [] = .ok .nil := by
  rw [lowProductArgs]

/-- Product fields use the actual checking-mode lowerer, with no separate callback instance. -/
theorem lowProductArgs_cons (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (ty : Ty) (side : USide) (rest : List (Ty × USide)) :
    lowProductArgs u Γ Λ fn er ((ty, side) :: rest) = (do
      let head ← lowWertAtE u Γ Λ fn er ty side
      let tail ← lowProductArgs u Γ Λ fn er rest
      pure (.cons head tail)) := by
  rw [lowProductArgs]

/-- Every literal field admitted by the predicate argument reader is
    accepted by the ordinary checking-mode expression elaborator. -/
theorem specLiteralField_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (ty : Ty) (side : USide) (valid : specLiteralFieldFits ty side = true) :
    ∃ expression, lowWertAtE u Γ Λ fn er ty side = .ok expression := by
  unfold specLiteralFieldFits at valid
  split at valid
  · rename_i lo hi value
    obtain ⟨loFits, hiFits⟩ := of_decide_eq_true valid
    by_cases same : Ty.int value value = .int lo hi
    · refine ⟨same ▸ Expr.lit value, ?_⟩
      simp only [lowWertAtE, lowWertE, LowSide.wert, fitW, dite_eq_left same]
    · refine ⟨Expr.widen loFits hiFits (Expr.lit value), ?_⟩
      simp only [lowWertAtE, lowWertE, LowSide.wert, fitW, dite_eq_right same,
        dite_eq_left loFits, dite_eq_left hiFits]
  · rename_i value
    cases value
    · exact ⟨Expr.fls, by simp only [lowWertAtE, lowWertE, fitW, dite_true] <;> rfl⟩
    · exact ⟨Expr.tru, by simp only [lowWertAtE, lowWertE, fitW, dite_true] <;> rfl⟩
  · rename_i capacity bytes
    cases decoded : bytesZahl bytes with
    | none => simp only [decoded, Bool.false_eq_true] at valid
    | some words =>
      have fits : words.length ≤ capacity := of_decide_eq_true (by simpa only [decoded] using valid)
      let literal : Expr (declOf u) Γ Λ (.str words.length) := .strLit words (Nat.le_refl _)
      by_cases same : Ty.str words.length = .str capacity
      · refine ⟨same ▸ literal, ?_⟩
        simp only [lowWertAtE, lowWertE, lowText, decoded, fitW, dite_eq_left same, literal]
      · refine ⟨Expr.strWeit capacity literal, ?_⟩
        simp only [lowWertAtE, lowWertE, lowText, decoded, fitW, dite_eq_right same, literal,
          ite_eq_left fits]
  · cases valid

theorem specLiteralFields_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (fields : List (Ty × USide))
    (valid : fields.all (fun field => specLiteralFieldFits field.1 field.2) = true) :
    ∃ args, lowProductArgs u Γ Λ fn er fields = .ok args := by
  induction fields with
  | nil => exact ⟨.nil, lowProductArgs_nil u Γ Λ fn er⟩
  | cons field rest ih =>
    obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp valid
    obtain ⟨value, lowValue⟩ := specLiteralField_lower u Γ Λ fn er field.1 field.2 head
    obtain ⟨args, lowArgs⟩ := ih tail
    cases field
    exact ⟨.cons value args, by
      simp only [lowProductArgs, lowValue, lowArgs, bind, Except.bind, pure, Except.pure]⟩

/-- Bind the successful source argument to the ordinary G nominal
    constructor. Every field passed checking mode at the declared type. -/
theorem specLiteralRecord_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (ctx : UCtx) (name : String) (source : List SExpr)
    (identity : Nat) (reordered : Bool) (fields : List (Ty × USide)) (result : Ty)
    (read : uWertBody ctx (.call name source) = .ok (.product identity reordered fields))
    (accepted : uSpecValueArgument ctx result (.call name source) = .ok ())
    (gate : u.exportGate = .ok ())
    (scope : u.records = ctx.records) :
    ∃ (args : Args (declOf u) Γ Λ (fields.map Prod.fst)),
      result = .prod identity (fields.map Prod.fst) ∧
      lowWertE u Γ Λ fn er (.product identity reordered fields) =
        .ok ⟨.prod identity (fields.map Prod.fst), Expr.prod identity args⟩ := by
  obtain ⟨parsed, sourceRead, typeRead⟩ := uSpecValueArgument_exact accepted
  have exactSide := Except.ok.inj (read.symm.trans sourceRead)
  subst parsed
  change uSpecLiteralRecordType ctx name identity fields = some result at typeRead
  unfold uSpecLiteralRecordType at typeRead
  cases selected : uRecordConstructor ctx name with
  | none =>
    simp only [selected, Option.bind_eq_bind, Option.bind_none] at typeRead
    cases typeRead
  | some schema =>
    simp only [selected, Option.bind_eq_bind, Option.bind_some] at typeRead
    split at typeRead
    · rename_i checked
      have resultType : schema.ty = result := Option.some.inj typeRead
      have member : schema ∈ u.records := scope.symm ▸ uRecordConstructor_mem selected
      have schemaExists (type : Ty) (same : schema.ty = type) :
          ∃ hit, uRecordOf u.records type = .ok hit :=
        same ▸ uRecordOf_complete member
      obtain ⟨hit, exactSchema⟩ := schemaExists _ checked.1
      obtain ⟨args, lowered⟩ := specLiteralFields_lower u Γ Λ fn er fields checked.2
      exact ⟨args, resultType.symm.trans checked.1,
        record_lower u Γ Λ fn er identity reordered fields args gate lowered _ exactSchema⟩
    · cases typeRead

/-- A Boolean constructor field jointly satisfies the reader premises
    for arbitrary nominal identity, field name and Boolean value. -/
theorem specLiteralRecord_source_erfuellbar (base : UCtx) (name label : String)
    (identity : Nat) (value : Bool) :
    let schema : URecord := { name, identity, fields := [(label, .bool)] }
    let ctx := { base with records := schema :: base.records }
    let argument := SExpr.call name [.ext .label [label] [if value then .tru else .fls]]
    let fields := [(.bool, USide.truth value)]
    uWertBody ctx argument = .ok (.product identity false fields) ∧
      uSpecValueArgument ctx schema.ty argument = .ok () := by
  intro schema ctx argument fields
  have chosen : uRecordConstructor ctx name = some schema := by
    simp [uRecordConstructor, ctx, schema, strEq_apply_eq_decide]
  have read : uWertBody ctx argument = .ok (.product identity false fields) := by
    cases value <;>
      simp [argument, fields, uWertBody, uRechne, chosen, uRecordSides, uRecordSide, uRecordValues,
        schema, uSuch, strEq_apply_eq_decide, bind, Except.bind, pure, Except.pure]
  exact ⟨read, specLiteralRecordArgument_erfuellbar ctx name _ schema fields false chosen read rfl rfl⟩

/-- Typed literals travel through the same actual literal lowerer in body and contract scopes. -/
theorem typed_literal_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (ty : Ty) (raw : USide) :
    lowWertE u Γ Λ fn er (.typed ty raw) = (lowLit ty raw).map (⟨ty, ·⟩) := by
  rw [lowWertE]

/-- Nominal literal construction retains every identity, schema and field-type check. -/
theorem lowLit_product (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (identity actual : Nat) (fields : List Ty) (reordered : Bool) (values : List (Ty × USide)) :
    lowLit (u := u) (Γ := Γ) (Λ := Λ) (.prod identity fields) (.product actual reordered values) = (do
      if identity != actual then throw "source export: constant has a foreign record identity"
      let _ ← uRecordOf u.records (.prod identity fields)
      let args ← lowLitFields fields values
      pure (.prod identity args)) := by
  rw [lowLit]

theorem lowLit_bool (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (value : Bool) :
    lowLit (u := u) (Γ := Γ) (Λ := Λ) .bool (.truth value) =
      .ok (if value then Expr.tru else Expr.fls) := by
  cases value <;> simp only [lowLit, Bool.false_eq_true, ↓reduceIte]

/-- The literal field helper also checks the carried field type before its recursive step. -/
theorem lowLitFields_cons (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (ty actual : Ty) (fields : List Ty) (value : USide) (values : List (Ty × USide)) :
    lowLitFields (u := u) (Γ := Γ) (Λ := Λ) (ty :: fields) ((actual, value) :: values) = (do
      if ty != actual then throw "source export: constant record field has a foreign type"
      let head ← lowLit ty value
      let tail ← lowLitFields fields values
      pure (.cons head tail)) := by
  rw [lowLitFields]

theorem lowLitFields_nil (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) :
    lowLitFields (u := u) (Γ := Γ) (Λ := Λ) [] [] = .ok .nil := by
  rw [lowLitFields]

/-- Nested literal arrays recurse through the same product-aware literal producer. -/
theorem lowLit_array_cons (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (ty : Ty) (count : Nat) (head tail : USide) :
    lowLit (u := u) (Γ := Γ) (Λ := Λ) (.arr ty (count + 1)) (.arrCons head tail) =
      (match lowLit ty head, lowLit (.arr ty count) tail with
       | .ok first, .ok rest => .ok (Expr.arrCons first rest)
       | .error error, _ | _, .error error => .error error) := by
  rw [lowLit]
  cases lowLit (u := u) (Γ := Γ) (Λ := Λ) ty head <;>
    cases lowLit (u := u) (Γ := Γ) (Λ := Λ) (.arr ty count) tail <;> rfl

/-- Product projection and replacement use the canonical semantics, with the whole base footprint. -/
theorem record_replace_meaning {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {identity : Nat}
    {fs : List Ty} {field : Ty} (entry state : World D) (env : Env D Γ)
    (value : Expr D Γ Λ (.prod identity fs)) (position : FieldAt fs field)
    (replacement : Expr D Γ Λ field) :
    eval entry (Expr.prodSet value position replacement) state env =
      prodSetW position (eval entry value state env) (eval entry replacement state env) ∧
    (Expr.prodSet value position replacement).orte = value.orte ++ replacement.orte := ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.UebersetzeAllg
