module

public import Core.Ast.Aggregate.TupleBindings
import Core.Ast.Aggregate.PatternPrint
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
    (rest : List Token) → TupleAnnotationReads scope input annotation rest → rest <:+ input
  | _, _, _, .absent => List.suffix_cons _ _
  | _, _, _, @TupleAnnotationReads.written _ input written rest typeRead =>
      ((List.suffix_cons assignment rest).trans (TypeReads.consumes typeRead)).trans
        (List.suffix_cons colon input)

private theorem directCall_not_tupleBind {scope : Scope} {input : List Token}
    {tokens : List Token} {call : DirectCall scope} {rest : List Token}
    (read : CallReads scope tokens call (semicolon :: rest))
    (eq : letKeyword :: openParen :: input = tokens) : False := by
  subst tokens
  obtain ⟨args, same, _⟩ := CallReads.inversion read
  have headEq : letKeyword = .word call.name.val := (List.cons.inj same).1
  have nameEq : call.name.val = "let".toList := by
    simpa [letKeyword] using headEq.symm
  have inList : call.name.val ∈ ["let", "if", "return", "while", "for", "leave", "next", "match"].map String.toList := by
    rw [nameEq]
    exact List.mem_map.2 ⟨"let", List.mem_cons_self, rfl⟩
  exact (call.ordinary.2 inList).elim

private theorem optionLet_not_tupleBind (mutable : Bool) (name : Identifier) {input tail : List Token}
    (same : letKeyword :: openParen :: input = optionLetHead mutable name ++ tail) : False := by
  cases mutable <;> cases (List.cons.inj (List.cons.inj same).2).1

private theorem tupleBind_inversion : Surface.TupleBindInversionAussage := by
  intro scope result input tree rest read
  generalize htok : letKeyword :: openParen :: input = tokens at read
  cases read
  case tupleBind =>
      have patternRead : TuplePatternReads _ _ _ := ‹_›
      have annotationRead : TupleAnnotationReads scope _ _ _ := ‹_›
      have valueRead : ExprReads scope 0 _ _ (semicolon :: rest) := ‹_›
      rw [← (List.cons.inj htok).2] at patternRead
      refine ⟨⟨_,_,_,_,_,‹_›,_⟩, _, _, patternRead, annotationRead, valueRead, rfl⟩
  case directCall callRead =>
      exact (directCall_not_tupleBind callRead htok).elim
  case letOption =>
      exact (optionLet_not_tupleBind _ _ htok).elim
  all_goals
    exfalso
    simpa [letKeyword, returnKeyword, ifKeyword, openParen, closeParen, semicolon,
      assignment, colon, comma, dot, keyword] using htok

theorem tupleBind_suffix : Surface.TupleBindSuffixAussage := by
  intro scope result input tree rest read
  generalize htok : letKeyword :: openParen :: input = tokens at read
  cases read
  case tupleBind =>
      have patternRead : TuplePatternReads _ _ _ := ‹_›
      have annotationRead : TupleAnnotationReads scope _ _ _ := ‹_›
      have valueRead : ExprReads scope 0 _ _ (semicolon :: rest) := ‹_›
      rw [← (List.cons.inj htok).2] at patternRead
      exact ((List.suffix_cons semicolon rest).trans (ExprReads.consumes valueRead)).trans
        ((tupleAnnotation_consumes _ _ _ annotationRead).trans
          (tuplePattern_consumes input _ _ patternRead))
  case directCall callRead =>
      exact (directCall_not_tupleBind callRead htok).elim
  case letOption =>
      exact (optionLet_not_tupleBind _ _ htok).elim
  all_goals
    exfalso
    simpa [letKeyword, returnKeyword, ifKeyword, openParen, closeParen, semicolon,
      assignment, colon, comma, dot, keyword] using htok

theorem tupleBind_prints (ctx : Scope × Option (Ty .value)) (args : TupleBindArgs ctx.1) :
    (tupleBind ctx).production args
      (((Category.statement ctx.1 ctx.2).printPieces ((tupleBind ctx).tree args)).map PrintedToken.value) := by
  dsimp [tupleBind, Category.printPieces]
  simp only [Stmt.printTokens, Stmt.printPieces, List.map_append, List.map_cons, List.map_nil]
  have letTok : letName.print.value = letKeyword := by rfl
  have assignTok : printAssignment.value = assignment := by rfl
  have semiTok : printSemicolon.value = semicolon := by rfl
  simp only [letTok, assignTok, semiTok, List.append_assoc]
  let ann := (tupleAnnotationPieces args.annotation).map PrintedToken.value
  let valToks := args.value.printTokens
  let more := ann ++ (assignment :: (valToks ++ [semicolon]))
  let rhs := valToks ++ [semicolon]
  let input := (args.pattern.printPieces.map PrintedToken.value) ++ more
  refine ⟨input, more, rhs, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact TuplePattern.printReads args.pattern more (fun id h => (args.checked.2.2.1 id h).1)
  · exact TupleAnnotationReads.printReads args.annotation (valToks ++ [semicolon]) (fun w h => (args.checked.2.2.2 w h).1)
  · exact Expr.printReads (tree := args.value) (minimum := 0) (rest := [semicolon]) noOperatorAtSemicolon

theorem tupleBind_derivation : Surface.TupleBindDerivationAussage := by
  intro ctx
  refine ⟨fun args tokens prod => ?_, tupleBind_prints ctx, ?_⟩
  · rcases prod with ⟨input, more, rhs, rfl, pRead, aRead, eRead⟩
    exact StmtReads.tupleBind args.checked pRead aRead eRead
  · let pattern : TuplePattern := ⟨none, none, []⟩
    have checked : pattern.valid ctx.1 none [.bool, .bool] := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [pattern, TuplePattern.names]
      · exact List.nodup_nil
      · intro name mem
        cases mem
      · intro written mem
        cases mem
    let args : TupleBindArgs ctx.1 :=
      ⟨.bool, .bool, [], pattern, none, checked, .tupleValue .trueLit .falseLit .empty⟩
    exact Rule.satisfiableOfPrint args (tupleBind_prints ctx args)

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
  have checked : pattern.valid [] none [.bool, .bool] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [pattern, TuplePattern.names]
    · exact List.nodup_nil
    · intro name mem
      cases mem
    · intro written mem
      cases mem
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

theorem tupleBind_parse : TupleBindParseAussage := by
  intro ctx args text pieces lexed prod
  exact (Surface.tupleBind_derivation ctx).parse lexed prod

end Gabbro.Core.Ast.Semantik
