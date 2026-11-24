module

public import Core.Ast.Aggregate.Records.Fields
public import Core.Ast.Semantik.Formbeweise
import Core.Ast.Aggregate.Records.ConstructionProofs
import Core.Ast.Semantik.Runtime.ValueCoercion

/-!
# AssignField

- `Surface.AssignFieldInversionAussage`
- `Surface.AssignFieldSuffixAussage`
- `Surface.AssignFieldDerivationAussage`
- `AssignFieldParseAussage`
- `AssignFieldElaboriertAussage`
- `AssignFieldRealisiertAussage`
- `AssignFieldAnnahmeAussage`
- `AssignFieldIdealAussage`
- `AssignFieldEinheitAussage`
- `AssignFieldImplAussage`
- `AssignFieldErhaltungAussage`
- `AssignFieldRegelSicherAussage`
- `AssignFieldErfuellbarAmAussage`
- `AssignFieldFrameAussage`
- `AssignFieldProgramAussage`
-/

namespace Gabbro.Core.Ast.Surface

theorem AssignFieldInversion : AssignFieldInversionAussage := by
  intro scope result name field input tree rest read
  have noDotExpr : ∀ {t : Ty .value} (tree : Expr scope t) (r : List Gabbro.Core.Text.Token),
      ¬ ExprReads scope 0 (dot :: .word field :: assignment :: input) tree r := by
    intro t tree r rd
    cases rd with
    | atom a tail => cases a
  have noDotCall : ∀ (call : DirectCall scope) (rs : List Gabbro.Core.Text.Token),
      ¬ CallReads scope (dot :: .word field :: assignment :: input) call rs := by
    intro call rs rd
    cases rd
  have noDotPattern : ∀ (pat : TuplePattern) (rs : List Gabbro.Core.Text.Token),
      ¬ TuplePatternReads (dot :: .word field :: assignment :: input) pat rs := by
    intro pat rs rd
    cases rd
  generalize htok : (.word name :: dot :: .word field :: assignment :: input) = toks at read
  cases read with
  | assignField ref visible writable fld index checked fits valueRead =>
      rename_i refName nm labs src input' value
      injection htok with hName hTail
      injection hTail with hDot hTail2
      injection hTail2 with hWord hTail3
      injection hTail3 with hAssign hInput
      have hn : name = ref.binding.name.val := by injection hName with h
      have hf : field = fld.val := by injection hWord with h
      have inputEq : input = input' := hInput
      have valueRead' : ExprReads scope 0 input value (semicolon :: rest) := by
        simpa only [inputEq] using valueRead
      exact ⟨⟨refName, nm, labs, ref, visible, writable, fld, index, checked, src, value, fits⟩,
        hn.symm, hf.symm, valueRead', rfl⟩
  | assignVar => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | letBinding => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | ret => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | ite => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | retVoid => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | letMutable => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | directCall =>
      rename_i call cr
      cases cr
      have hdot : dot = openParen := (List.cons.inj (List.cons.inj htok).2).1
      cases hdot
  | bindDirect => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | whileBounded => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | forRange => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | tupleBind => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | letMutableValue => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | variantMatch => simp_all [letKeyword, keyword, returnKeyword, ifKeyword, assignment, dot, semicolon, noDotExpr, noDotCall, noDotPattern]
  | letOption mutable _ _ _ _ _ _ =>
      cases mutable <;> cases (List.cons.inj (List.cons.inj htok).2).1
  | retOption _ initializer =>
      cases initializer <;> cases (List.cons.inj (List.cons.inj htok).2).1

theorem AssignFieldSuffix : AssignFieldSuffixAussage := by
  intro scope result name field input tree rest read
  obtain ⟨a, hname, hfield, valueRead, htree⟩ := AssignFieldInversion read
  exact (List.suffix_cons semicolon rest).trans (ExprReads.consumes valueRead)

open Gabbro.Core.Text

private theorem assignFieldPrints (ctx : Scope × Option (Ty .value)) (args : AssignFieldArgs ctx.1) :
    (assignField ctx).production args
      (((Category.statement ctx.1 ctx.2).printPieces ((assignField ctx).tree args)).map PrintedToken.value) := by
  refine ⟨args.value.printTokens ++ [semicolon], ?_, ?_⟩
  · change (Category.printPieces (.statement ctx.1 ctx.2) ((assignField ctx).tree args)).map
      PrintedToken.value = _
    simp only [Category.printPieces, assignField, Stmt.printPieces, Expr.printTokens,
      List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rfl
  · exact args.value.printReads noOperatorAtSemicolon

theorem AssignFieldDerivation : AssignFieldDerivationAussage := by
  rintro ctx ⟨witness⟩
  refine ⟨?_, assignFieldPrints ctx, Rule.satisfiableOfPrint witness (assignFieldPrints ctx witness)⟩
  rintro args tokens ⟨input, rfl, valueRead⟩
  exact .assignField args.ref args.visible args.writable args.field args.index args.written args.fits valueRead

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

theorem AssignFieldElaboriert : AssignFieldElaboriertAussage := by
  intro ctx platform args
  rfl

theorem AssignFieldRealisiert : AssignFieldRealisiertAussage := by
  intro ctx platform args s running active live atPc
  exact (assignFieldForm ctx).realisiert (fun args => by
    change (((expr 0 args.value).code ++ [Befehl.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index])[(expr 0 args.value).code.length]? =
      some (.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index))
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  ) platform args s running active live atPc

theorem AssignFieldAnnahme : AssignFieldAnnahmeAussage := by
  intro ctx
  exact Quellform.annahme (assignFieldForm ctx)

theorem AssignFieldIdeal : AssignFieldIdealAussage := by
  intro ctx
  refine ⟨?_, ?_⟩
  · intro args
    change (((expr 0 args.value).code ++ [Befehl.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index])[(expr 0 args.value).code.length]? =
      some (.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index))
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  · intro args
    exact ⟨((assignFieldForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem AssignFieldEinheit : AssignFieldEinheitAussage := by
  intro ctx platform args
  exact ⟨rfl, ((assignFieldForm ctx).befehl args).kommutation⟩

theorem AssignFieldImpl : AssignFieldImplAussage := by
  intro ctx args c s w plans u
  rfl

theorem AssignFieldErhaltung : AssignFieldErhaltungAussage := by
  intro ctx
  exact Quellform.erhaltung (assignFieldForm ctx)
    (fun args => stmt_keine_invarianten ((Surface.assignField ctx).tree args).2)

theorem AssignFieldRegelSicher : AssignFieldRegelSicherAussage := by
  intro ctx platform args
  exact (Quellform.erhaltung (assignFieldForm ctx)
    (fun args => stmt_keine_invarianten ((Surface.assignField ctx).tree args).2)
    platform args).2.2.2

open Gabbro.Core.Text

theorem AssignFieldParse : AssignFieldParseAussage := by
  intro ctx args text pieces lex prod
  apply (Category.statement ctx.1 ctx.2).syntax.parse_iff.mpr
  refine ⟨pieces, lex, ?_⟩
  rcases prod with ⟨input, htok, valueRead⟩
  rw [htok]
  exact .assignField args.ref args.visible args.writable args.field args.index args.written args.fits valueRead

theorem AssignFieldFrame : AssignFieldFrameAussage := by
  intro ctx args frame record value hlocal htemp
  have hwiden : wertAls (args.types.get args.index) ⟨args.source, value⟩ =
      some (Wert.widen args.source (args.types.get args.index) args.fits value) :=
    wertAls_widen _ _ _ value
  have hold : wertAls (recordValueType args.name args.labels args.types)
      ⟨recordValueType args.name args.labels args.types, record⟩ = some record := by
    simp only [wertAls, recordValueType, dif_pos]
  have hlt : args.ref.index < frame.lokale.length := by
    by_contra h
    have hn : frame.lokale[args.ref.index]? = none := List.getElem?_eq_none (Nat.ge_of_not_lt h)
    rw [hn] at hlocal
    cases hlocal
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [assignFieldForm, Befehl.auswerten]
    rw [hlocal, htemp]
    simp only [Option.bind, Option.join, id_eq]
    rw [hold, hwiden]
    try simp only [Option.bind]
    rw [List.getElem?_set_self hlt]
    rfl
  · intro i hi
    simp only [assignFieldForm, Befehl.auswerten]
    exact List.getElem?_set_ne (Ne.symm hi)
  · simp only [assignFieldForm, Befehl.auswerten]
  · simp only [assignFieldForm, Befehl.auswerten]

theorem AssignFieldErfuellbarAm : AssignFieldErfuellbarAmAussage := by
  intro platform start
  let field : Identifier := ⟨['x'], 'x', [], rfl,
    by unfold Text.isNameStart Text.isLetter; exact Or.inl (Or.inl ⟨by decide, by decide⟩),
    by intro a ha; cases ha⟩
  let name : List Char := ['R']
  let labels : List Identifier := [field]
  let types : List (Ty .value) := [.int 1 2]
  let recTy : Ty .value := recordValueType name labels types
  let binding : Binding := ⟨field, recTy, true, false⟩
  let scope : Scope := [binding]
  let ref : Local scope recTy := .here
  let index : Fin types.length := ⟨0, by decide⟩
  let written : RecordFieldAt labels field index.val := by
    change (labels.map Subtype.val).Nodup ∧ labels[0]? = some field
    constructor
    · change List.Pairwise (fun a b : Text.RawText => a ≠ b) [field.val]
      constructor
      · intro b hb
        cases hb
      · constructor
    · change [field][0]? = some field
      rfl
  let source : Ty .value := .int 1 1
  let value : Expr scope source := .lit 1
  let fits : Fits source (types.get index) := by
    change (1 : Int) ≤ 1 ∧ (1 : Int) ≤ 2
    exact ⟨by decide, by decide⟩
  let visible : ref.visible := by
    change recTy.valueBinding ∧ ref.nameVisible
    constructor
    · change True
      trivial
    · dsimp [ref, Local.nameVisible]
      trivial
  let writable : ref.binding.mutable = true := rfl
  let args : Surface.AssignFieldArgs scope :=
    ⟨name, labels, types, ref, visible, writable, field, index, written, source, value, fits⟩
  let ctx : Scope × Option (Ty .value) := (scope, none)
  let form := assignFieldForm ctx
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  have h₁ : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.literal 0 1, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start h₁
  refine ⟨ctx, args, form.erfuellbar_aus_erreichbar platform start args s₁ reached ?_ ?_⟩
  · exact form.realisiert (fun args => by
      change (((expr 0 args.value).code ++ [Befehl.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index])[(expr 0 args.value).code.length]? =
        some (.setzeRecordFeld 0 args.ref.index args.name args.labels args.types args.index))
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
    ) platform args s₁ rfl rfl rfl rfl
  · intro g guard
    change none = some g at guard
    cases guard

theorem AssignFieldProgram : AssignFieldProgramAussage := by
  intro platform start
  let value := RecordExample.value
  let name := RecordExample.name
  let field := RecordExample.field
  let member : RecordMember := ⟨field, .bool⟩
  let recTy := recordValueType name.val value.labels value.types
  let localScope : Scope := ⟨field, recTy, true, false⟩ :: RecordExample.scope
  let ref : Local localScope recTy := .here
  let index : Fin value.types.length := ⟨0, Nat.zero_lt_succ _⟩
  let bind : Stmt none RecordExample.scope localScope :=
    .letMutableValue field (directName_of_singleton (name := field) rfl).1 value.expression
  let update : Stmt none localScope localScope :=
    .assignField ref ⟨trivial, trivial⟩ rfl field index
      ⟨List.nodup_singleton _, rfl⟩ .falseLit trivial
  let body : BracedBlock none RecordExample.scope := .braces (.step bind (.step update .done))
  let schema : Decl [] RecordExample.scope :=
    .record false name [member] (by
      intro m belongs
      cases List.mem_singleton.mp belongs
      trivial) (List.nodup_singleton _)
  let main : Decl RecordExample.scope RecordExample.scope :=
    .function mainName mainName_direct [] none (fun _ h => (List.not_mem_nil h).elim)
      none body List.nodup_nil (fun h => by cases h) none
  let tree : Ast.Unit := ⟨RecordExample.scope, .step schema (.step main .done)⟩
  let E := elaborieren platform (category := .unit) tree
  have advance {s : Zustand} {b : Befehl} (reached : E.system.IErreichbar (I.start E start).2 s)
      (head : E.system.kopf s eintritt = some b) :
      E.system.IErreichbar (I.start E start).2 (b.nach eintritt s) :=
    .schritt eintritt () [plan] reached ⟨b, head, rfl, rfl⟩
  let defineSchema := Befehl.definiereRecord name.val value.labels value.types
  let defineMain := functionInstruction RecordExample.scope mainName [] none false
    (functionCode none none body) none
  let startMain := Befehl.starte mainName
  let evalTrue := Befehl.wahrheitswert 0 true
  let build := Befehl.baueRecord 0 name.val value.labels value.types [0]
  let bindLocal := Befehl.bindeWert 0 recTy false
  let evalFalse := Befehl.wahrheitswert 0 false
  let s₀ := (I.start E start).2
  let s₁ := defineSchema.nach eintritt s₀
  let s₂ := defineMain.nach eintritt s₁
  let s₃ := startMain.nach eintritt s₂
  let s₄ := evalTrue.nach eintritt s₃
  let s₅ := build.nach eintritt s₄
  let s₆ := bindLocal.nach eintritt s₅
  let s₇ := evalFalse.nach eintritt s₆
  have r₁ : E.system.IErreichbar s₀ s₁ := advance (b := defineSchema) .start rfl
  have r₂ : E.system.IErreichbar s₀ s₂ := advance (b := defineMain) r₁ rfl
  have r₃ : E.system.IErreichbar s₀ s₃ := advance (b := startMain) r₂ rfl
  have r₄ : E.system.IErreichbar s₀ s₄ := advance (b := evalTrue) r₃ rfl
  have r₅ : E.system.IErreichbar s₀ s₅ := advance (b := build) r₄ rfl
  have r₆ : E.system.IErreichbar s₀ s₆ := advance (b := bindLocal) r₅ rfl
  have r₇ : E.system.IErreichbar s₀ s₇ := advance (b := evalFalse) r₆ rfl
  refine ⟨tree, Ast.print (category := .unit) tree, s₇, 0, 0, name.val, value.labels, value.types,
    index, Ast.parse_print _, r₇, rfl, (true, PUnit.unit), (false, PUnit.unit), rfl, rfl, ?_⟩
  intro same
  cases same

end Gabbro.Core.Ast.Semantik
