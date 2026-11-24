module

public import Core.Ast.Aggregate.TupleBindings
public import Core.Ast.Semantik.Formbeweise

/-!
# Prover checklist

## TupleBind

- `Surface.TupleBindInversionAussage`
- `Surface.TupleBindSuffixAussage`
- `Surface.TupleBindDerivationAussage`
- `TupleBindParseAussage`
- `TupleBindElaboriertAussage`
- `TupleBindRealisiertAussage`
- `TupleBindAnnahmeAussage`
- `TupleBindIdealAussage`
- `TupleBindEinheitAussage`
- `TupleBindImplAussage`
- `TupleBindErhaltungAussage`
- `TupleBindRegelSicherAussage`
- `TupleBindErfuellbarAmAussage`
- `TupleBindLocalsAussage`
-/

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

private theorem patternName_consumes {input : List Token} {name : Option Identifier} {rest : List Token}
    (read : PatternNameReads input name rest) : rest <:+ input := by
  cases read <;> exact List.suffix_cons _ _

private theorem patternTail_consumes : (input : List Token) → (names : List (Option Identifier)) →
    (rest : List Token) → PatternTailReads input names rest → rest <:+ input
  | _, _, _, .close => List.suffix_cons _ _
  | _, _, _, @PatternTailReads.next input name more names rest nameRead tailRead =>
      (patternTail_consumes more names rest tailRead).trans
        ((patternName_consumes nameRead).trans (List.suffix_cons comma input))

private theorem tuplePattern_consumes : (input : List Token) → (pattern : TuplePattern) →
    (rest : List Token) → TuplePatternReads (openParen :: input) pattern rest → rest <:+ input
  | _, _, _, @TuplePatternReads.tuple input first next second more tail rest firstRead secondRead tailRead =>
      (patternTail_consumes more tail rest tailRead).trans
        ((patternName_consumes secondRead).trans
          ((List.suffix_cons comma next).trans (patternName_consumes firstRead)))

private theorem tupleAnnotation_consumes : (input : List Token) → (annotation : Option WrittenType) →
    (rest : List Token) → TupleAnnotationReads input annotation rest → rest <:+ input
  | _, _, _, .absent => List.suffix_cons _ _
  | _, _, _, @TupleAnnotationReads.written input written rest typeRead =>
      ((List.suffix_cons assignment rest).trans (TypeReads.consumes typeRead)).trans
        (List.suffix_cons colon input)

private theorem openParen_ne_word (name : List Char) : openParen ≠ Token.word name := by
  intro h
  unfold openParen at h
  nomatch h

private theorem letKeyword_ne_word (name : List Char) : letKeyword ≠ Token.word name := by
  intro h
  unfold letKeyword at h
  cases h

theorem tupleBind_suffix : TupleBindSuffixAussage := by
  intro scope result input tree rest read
  generalize htok : letKeyword :: openParen :: input = tokens at read
  cases read
  case tupleBind =>
      have patternRead : TuplePatternReads _ _ _ := ‹_›
      have annotationRead : TupleAnnotationReads _ _ _ := ‹_›
      have valueRead : ExprReads scope 0 _ _ (semicolon :: rest) := ‹_›
      rw [← (List.cons.inj htok).2] at patternRead
      exact ((List.suffix_cons semicolon rest).trans (ExprReads.consumes valueRead)).trans
        ((tupleAnnotation_consumes _ _ _ annotationRead).trans
          (tuplePattern_consumes input _ _ patternRead))
  case variantMatch =>
      have h : openParen = keyword "match" := (List.cons.inj (List.cons.inj htok).2).1
      unfold keyword at h
      exact (openParen_ne_word _ h).elim
  all_goals
    first
    | simp_all
    | exact (openParen_ne_word _ (List.cons.inj (List.cons.inj htok).2).1).elim

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

theorem tupleBind_am_ort (ctx : Scope × Option (Ty .value)) : (tupleBindForm ctx).RegelAmOrt := by
  intro args
  change (((expr 0 args.value).anhaengen (.einzel
    (.bindeTupel 0 args.types (args.pattern.names.map Option.isSome)))).code[
      (expr 0 args.value).code.length]? =
    some (.bindeTupel 0 args.types (args.pattern.names.map Option.isSome)))
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

theorem tupleBind_elaboriert : TupleBindElaboriertAussage := by
  intro ctx platform args
  rfl

theorem tupleBind_realisiert : TupleBindRealisiertAussage := by
  intro ctx platform args s running active live atPc
  exact (tupleBindForm ctx).realisiert (tupleBind_am_ort ctx) platform args s
    running active live atPc

theorem tupleBind_annahme : TupleBindAnnahmeAussage := by
  intro ctx
  exact (tupleBindForm ctx).annahme

theorem tupleBind_ideal : TupleBindIdealAussage := by
  intro ctx
  refine ⟨tupleBind_am_ort ctx, ?_⟩
  intro args
  exact ⟨((tupleBindForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem tupleBind_einheit : TupleBindEinheitAussage := by
  intro ctx platform args
  exact ⟨rfl, ((tupleBindForm ctx).befehl args).kommutation⟩

theorem tupleBind_impl : TupleBindImplAussage := by
  intro ctx args c s w plans u
  rfl

private theorem tupleBind_keineInvarianten (ctx : Scope × Option (Ty .value))
    (args : Surface.TupleBindArgs ctx.1) :
    ((tupleBindForm ctx).fragment args).klauseln.invariant = [] := by
  change (stmt (Stmt.tupleBind args.pattern args.annotation args.checked args.value)).klauseln.invariant = []
  exact stmt_keine_invarianten _

theorem tupleBind_erhaltung : TupleBindErhaltungAussage := by
  intro ctx
  exact (tupleBindForm ctx).erhaltung (tupleBind_keineInvarianten ctx)

theorem tupleBind_regelSicher : TupleBindRegelSicherAussage := by
  intro ctx platform args
  exact ((tupleBindForm ctx).befehl args).sicher ((tupleBindForm ctx).fragment args)
    platform (tupleBind_keineInvarianten ctx args)

private theorem tupleLocals_length : (types : List (Ty .value)) → (value : Wert (tupleType types)) →
    (names : List (Option Identifier)) → names.length = types.length →
    (tupleLocals types value (names.map Option.isSome)).length =
      ((names.zip types).filterMap fun (name, _) => name).length
  | [], _, [], _ => rfl
  | _ :: _, _, [], h => by cases h
  | [], _, _ :: _, h => by cases h
  | t :: ts, (head, tail), name :: names, h => by
      cases name with
      | none =>
          simpa [tupleLocals] using (tupleLocals_length ts tail names (by simpa using h))
      | some id =>
          simpa [tupleLocals] using (tupleLocals_length ts tail names (by simpa using h))

theorem tupleBind_locals : TupleBindLocalsAussage := by
  intro ctx args frame value temp
  have got : wertAls (tupleType args.types) ⟨tupleType args.types, value⟩ = some value := by
    change (if same : tupleType args.types = tupleType args.types then some (same ▸ value) else none) = some value
    rw [dif_pos rfl]
  simp only [tupleBindForm, Quellform.befehl, Befehl.auswerten]
  rw [temp]
  simp only [Option.bind_some]
  rw [got]
  simp only [Option.map_some, Option.getD_some]
  have hlen : (args.pattern.bindings args.types).length =
      ((args.pattern.names.zip args.types).filterMap fun (name, _) => name).length := by
    simp only [TuplePattern.bindings, List.length_reverse]
    let z := args.pattern.names.zip args.types
    change (z.filterMap (fun x => Option.map (fun id => (⟨id, x.2, false, false⟩ : Binding)) x.1)).length =
      (z.filterMap fun x => x.1).length
    induction z with
    | nil => rfl
    | cons x xs ih =>
        cases hx : x.1 with
        | none => simpa [hx] using ih
        | some id => simpa [hx] using congrArg Nat.succ ih
  refine ⟨trivial, ?_, trivial, trivial⟩
  · simp only [List.length_append, List.length_reverse]
    rw [hlen]
    rw [tupleLocals_length args.types value args.pattern.names args.checked.1]

theorem tupleBind_erfuellbar : TupleBindErfuellbarAmAussage := by
  intro platform start
  let pattern : TuplePattern := ⟨none, none, []⟩
  have checked : pattern.valid none [.bool, .bool] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [pattern, TuplePattern.names]
    · exact List.nodup_nil
    · intro name mem
      simp [pattern, TuplePattern.names] at mem
    · intro written mem
      simpa using mem
  let args : Surface.TupleBindArgs [] :=
    ⟨.bool, .bool, [], pattern, none, checked, .tupleValue .trueLit .falseLit .empty⟩
  let form := tupleBindForm ([], none)
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.wahrheitswert 0 true).nach eintritt s₀
  let s₂ := (Befehl.wahrheitswert 1 false).nach eintritt s₁
  let s₃ := (Befehl.baueTupel 0 [.bool, .bool]).nach eintritt s₂
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.wahrheitswert 0 true, rfl, rfl, rfl⟩
  have second : E.system.ISchritt eintritt s₁ () [plan] s₂ :=
    ⟨.wahrheitswert 1 false, rfl, rfl, rfl⟩
  have third : E.system.ISchritt eintritt s₂ () [plan] s₃ :=
    ⟨.baueTupel 0 [.bool, .bool], rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₃ :=
    .schritt eintritt () [plan]
      (.schritt eintritt () [plan] (.schritt eintritt () [plan] .start first) second) third
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s₃ reached
    (form.realisiert (tupleBind_am_ort ([], none)) platform args s₃ rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

end Gabbro.Core.Ast.Semantik
