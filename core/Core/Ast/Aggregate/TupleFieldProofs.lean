module

public import Core.Ast.Aggregate.Tuples
public import Core.Ast.Aggregate.Records.RecordFieldProofs
public import Core.Ast.Semantik.Formbeweise

/-!
# TupleField

Prove the pinned statements in this file.

- `Surface.TupleFieldInversionAussage`
- `Surface.TupleFieldSuffixAussage`
- `Surface.TupleFieldDerivationAussage`
- `TupleFieldParseAussage`
- `TupleFieldElaboriertAussage`
- `TupleFieldRealisiertAussage`
- `TupleFieldAnnahmeAussage`
- `TupleFieldIdealAussage`
- `TupleFieldEinheitAussage`
- `TupleFieldImplAussage`
- `TupleFieldErhaltungAussage`
- `TupleFieldRegelSicherAussage`
- `TupleFieldErfuellbarAmAussage`
-/

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Ast.Semantik

theorem tupleTypeInjAux : ∀ {a b : List (Ty .value)}, tupleType a = tupleType b → a = b := by
  intro a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons y ys =>
          simp only [tupleType] at h
          cases h
  | cons x xs ih =>
      intro b h
      cases b with
      | nil =>
          simp only [tupleType] at h
          cases h
      | cons y ys =>
          simp only [tupleType] at h
          injection h with h1 h2
          subst y
          exact congrArg (fun l => x :: l) (ih h2)

theorem tupleFieldInvGen {scope first second types minimum input type}
    {tree : Expr scope type} {rest} (allowed : minimum ≤ Infix.projection.precedence) :
    ∀ (inputType : Ty .value) (base0 : Expr scope inputType),
      (eqT : inputType = tupleType (first :: second :: types)) →
      (n : Nat) →
      ExprTail scope minimum base0 (dot :: .natural n :: input) tree rest →
      ∃ i : Fin (first :: second :: types).length, i.val = n ∧
        ExprTail scope minimum (.tupleField (eqT ▸ base0) i) input tree rest := by
    intro inputType base0 eqT n r
    generalize htok : (dot :: .natural n :: input) = toks at r
    cases r with
    | stop blocked =>
        exfalso
        exact blocked ⟨.projection, .natural n :: input,
          by simpa only [Infix.token] using htok.symm, allowed⟩
    | binary op hle _ _ =>
        have head : dot = op.token := (List.cons.inj htok).1
        have eq : (.projection : Infix) = .arith op :=
          Infix.token_injective (by simpa only [Infix.token] using head)
        cases eq
    | div hle _ _ _ =>
        have head : dot = Infix.div.token := (List.cons.inj htok).1
        have eq : (.projection : Infix) = .div :=
          Infix.token_injective (by simpa only [Infix.token] using head)
        cases eq
    | compare op hle _ _ _ =>
        have head : dot = (Infix.compare op).token := (List.cons.inj htok).1
        have eq : (.projection : Infix) = .compare op :=
          Infix.token_injective (by simpa only [Infix.token] using head)
        cases eq
    | logic op hle _ _ =>
        have head : dot = (Infix.logic op).token := (List.cons.inj htok).1
        have eq : (.projection : Infix) = .logic op :=
          Infix.token_injective (by simpa only [Infix.token] using head)
        cases eq
    | arrayIndex _ _ _ hle _ _ =>
        have head : dot = openBracket := (List.cons.inj htok).1
        have eq : (.projection : Infix) = .index :=
          Infix.token_injective (by simpa only [Infix.token] using head)
        cases eq
    | tupleField base' index' hle tail =>
        rename_i a b ts input'
        have hlists : a :: b :: ts = first :: second :: types :=
          tupleTypeInjAux eqT
        injection hlists with ha htail
        injection htail with hb hts
        subst a
        subst b
        subst ts
        have numEq : .natural n :: input = .natural index'.val :: input' := (List.cons.inj htok).2
        have hidx : index'.val = n := by
          injection (List.cons.inj numEq).1 with h
          exact h.symm
        have inputEq : input = input' := (List.cons.inj numEq).2
        subst input'
        exact ⟨index', hidx, tail⟩
    | recordField _ field' _ _ hle _ =>
        have restEq : .natural n :: input = .word field'.val :: _ := (List.cons.inj htok).2
        cases (List.cons.inj restEq).1
    | textConcat _ _ _ _ _ => cases (List.cons.inj htok).1
    | textIndex _ _ _ _ _ | substring _ _ _ _ _ _ _ => cases (List.cons.inj htok).1
    | optionIsSome _ _ _ _ _ => cases (List.cons.inj (List.cons.inj htok).2).1

theorem TupleFieldInversion : TupleFieldInversionAussage := by
  intro scope first second types minimum n input type base tree rest allowed read
  exact tupleFieldInvGen allowed _ base rfl n read

theorem TupleFieldSuffix : TupleFieldSuffixAussage := by
  intro scope first second types minimum n input type base tree rest allowed read
  obtain ⟨i, hival, tail⟩ := tupleFieldInvGen allowed _ base rfl n read
  exact ExprTail.consumes tail

open Gabbro.Core.Text

theorem tupleFieldReadsLower {scope : Scope} {first second : Ty .value} {types : List (Ty .value)}
    {n : Nat} {input input' : List Token} {inputType : Ty .value}
    {base : Expr scope inputType}
    (eqT : inputType = tupleType (first :: second :: types))
    (hn : n < (first :: second :: types).length)
    (blocked : ¬ Continues 0 input')
    (read : ExprReads scope 8 input base (dot :: .natural n :: input')) :
    ∃ i : Fin (first :: second :: types).length, i.val = n ∧
      ExprReads scope 0 input (.tupleField (eqT ▸ base) i) input' := by
  subst inputType
  cases read with
  | atom a tail =>
      cases tail with
      | stop _ =>
          refine ⟨⟨n, hn⟩, rfl, ?_⟩
          exact .atom a (.tupleField base ⟨n, hn⟩ (Nat.zero_le _) (.stop blocked))
      | binary op hle _ _ =>
          cases op <;> simp only [Arith.precedence, Infix.precedence] at hle <;> omega
      | div hle _ _ _ =>
          simp only [Infix.precedence] at hle <;> omega
      | compare op hle _ _ _ =>
          simp only [Infix.precedence] at hle <;> omega
      | logic op hle _ _ =>
          cases op <;> simp only [Infix.precedence] at hle <;> omega
      | arrayIndex _ _ _ hle _ _ =>
          simp only [Infix.precedence] at hle <;> omega
      | tupleField _ _ hle _ =>
          simp only [Infix.precedence] at hle <;> omega
      | recordField _ _ _ _ hle _ =>
          simp only [Infix.precedence] at hle <;> omega
      | textConcat _ _ hle _ _ =>
          simp only [Arith.precedence] at hle <;> omega
      | textIndex _ _ hle _ _ | substring _ _ _ hle _ _ _ | optionIsSome _ _ _ hle _ =>
          simp only [Infix.precedence] at hle <;> omega

theorem tupleFieldPrintTokens {scope : Scope} {first second : Ty .value} {tailTypes : List (Ty .value)}
    (base : Expr scope (tupleType (first :: second :: tailTypes)))
    (index : Fin (first :: second :: tailTypes).length) :
    (Expr.tupleField base index).printTokens =
      openParen :: (base.printTokens ++ [dot, .natural index.val, closeParen]) := by
  simp only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil,
    List.singleton_append, List.cons_append, List.nil_append, List.append_assoc, printOpen, printClose, printDot, printInteger,
    printPunctuation, PrintedToken.unquoted, openParen, closeParen, dot, String.reduceToList]

theorem tupleFieldPrints (scope : Scope) (args : TupleFieldArgs scope) :
    (tupleField scope).production args
      (((Category.expression scope).printPieces ((tupleField scope).tree args)).map PrintedToken.value) := by
  change postfixProduction (fun input rest =>
      ExprReads scope 8 input args.base (dot :: .natural args.index.val :: rest))
    ((Expr.tupleField args.base args.index).printTokens)
  rw [tupleFieldPrintTokens args.base args.index]
  right
  refine ⟨args.base.printTokens ++ [dot, .natural args.index.val, closeParen], rfl, ?_⟩
  apply Expr.printReads
  rintro ⟨op, rest, hEq, hle⟩
  have htok : op.token = dot := (List.cons.inj hEq).1.symm
  have opEq : op = .projection := Infix.token_injective (by simpa only [Infix.token] using htok)
  subst op
  have bad : ¬ (8 : Nat) ≤ 7 := by decide
  exact bad (by simpa only [Infix.precedence] using hle)

theorem tupleFieldReads (scope : Scope) (args : TupleFieldArgs scope) (tokens : List Token)
    (read : (tupleField scope).production args tokens) :
    (Category.expression scope).reads tokens ((tupleField scope).tree args) := by
  change ExprReads scope 0 tokens (Expr.tupleField args.base args.index) []
  change postfixProduction (fun input rest =>
      ExprReads scope 8 input args.base (dot :: .natural args.index.val :: rest)) tokens at read
  rcases read with plain | grouped
  · obtain ⟨i, hi, r0⟩ := tupleFieldReadsLower (scope := scope) (first := args.first)
      (second := args.second) (types := args.tail) (n := args.index.val)
      (input := tokens) (input' := []) (inputType := _) (base := args.base)
      rfl args.index.isLt noOperatorAtEnd plain
    have ieq : i = args.index := Fin.ext hi
    subst i
    exact r0
  · rcases grouped with ⟨inside, rfl, groupedRead⟩
    obtain ⟨i, hi, r0⟩ := tupleFieldReadsLower (scope := scope) (first := args.first)
      (second := args.second) (types := args.tail) (n := args.index.val)
      (input := inside) (input' := [closeParen]) (inputType := _) (base := args.base)
      rfl args.index.isLt noOperatorAtClose groupedRead
    have ieq : i = args.index := Fin.ext hi
    subst i
    exact .atom (.grouped r0) (.stop noOperatorAtEnd)

theorem tupleFieldErfuellbar (scope : Scope) : (tupleField scope).Satisfiable := by
  let a : Ty .value := .int 1 1
  let b : Ty .value := .int 2 2
  let base : Expr scope (tupleType [a, b]) := .tupleValue (.lit 1) (.lit 2) .empty
  let args : TupleFieldArgs scope := ⟨a, b, [], base, ⟨0, Nat.zero_lt_succ _⟩⟩
  exact Rule.satisfiableOfPrint args (tupleFieldPrints scope args)

theorem TupleFieldDerivation : TupleFieldDerivationAussage := by
  intro scope
  exact ⟨fun args => tupleFieldReads scope args, tupleFieldPrints scope, tupleFieldErfuellbar scope⟩

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

theorem TupleFieldElaboriert : TupleFieldElaboriertAussage := by
  intro scope platform args
  rfl

theorem TupleFieldRealisiert : TupleFieldRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (tupleFieldForm scope).realisiert (fun args => by
    change (((expr 0 args.base).code ++ [Befehl.liesTupelfeld 0 args.types args.index])[(expr 0 args.base).code.length]? =
      some (.liesTupelfeld 0 args.types args.index))
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  ) platform args s running active live atPc

theorem TupleFieldAnnahme : TupleFieldAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (tupleFieldForm scope)

theorem TupleFieldIdeal : TupleFieldIdealAussage := by
  intro scope
  refine ⟨?_, ?_⟩
  · intro args
    change (((expr 0 args.base).code ++ [Befehl.liesTupelfeld 0 args.types args.index])[(expr 0 args.base).code.length]? =
      some (.liesTupelfeld 0 args.types args.index))
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  · intro args
    exact ⟨((tupleFieldForm scope).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem TupleFieldEinheit : TupleFieldEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((tupleFieldForm scope).befehl args).kommutation⟩

theorem TupleFieldImpl : TupleFieldImplAussage := by
  intro scope args c s w plans u
  rfl

theorem TupleFieldErhaltung : TupleFieldErhaltungAussage := by
  intro scope
  exact Quellform.erhaltung (tupleFieldForm scope)
    (fun args => expr_keine_invarianten 0 ((Surface.tupleField scope).tree args).2)

theorem TupleFieldRegelSicher : TupleFieldRegelSicherAussage := by
  intro scope platform args
  exact (Quellform.erhaltung (tupleFieldForm scope)
    (fun args => expr_keine_invarianten 0 ((Surface.tupleField scope).tree args).2)
    platform args).2.2.2.1

theorem TupleFieldErfuellbarAm : TupleFieldErfuellbarAmAussage := by
  intro platform start
  let form := tupleFieldForm []
  let a : Ty .value := .int 1 1
  let b : Ty .value := .int 2 2
  let base : Expr [] (tupleType [a, b]) := .tupleValue (.lit 1) (.lit 2) .empty
  let args : Surface.TupleFieldArgs [] := ⟨a, b, [], base, ⟨0, Nat.zero_lt_succ _⟩⟩
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  let s₂ := (Befehl.literal 1 2).nach eintritt s₁
  let s₃ := (Befehl.baueTupel 0 [a, b]).nach eintritt s₂
  let s₄ := (Befehl.liesTupelfeld 0 [a, b] ⟨0, Nat.zero_lt_succ _⟩).nach eintritt s₃
  have h₁ : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.literal 0 1, rfl, rfl, rfl⟩
  have h₂ : E.system.ISchritt eintritt s₁ () [plan] s₂ := ⟨.literal 1 2, rfl, rfl, rfl⟩
  have h₃ : E.system.ISchritt eintritt s₂ () [plan] s₃ := ⟨.baueTupel 0 [a, b], rfl, rfl, rfl⟩
  have h₄ : E.system.ISchritt eintritt s₃ () [plan] s₄ :=
    ⟨.liesTupelfeld 0 [a, b] ⟨0, Nat.zero_lt_succ _⟩, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₃ :=
    .schritt eintritt () [plan]
      (.schritt eintritt () [plan]
        (.schritt eintritt () [plan] .start h₁) h₂) h₃
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s₃ reached
    (form.realisiert (fun args => by
      change (((expr 0 args.base).code ++ [Befehl.liesTupelfeld 0 args.types args.index])[(expr 0 args.base).code.length]? =
        some (.liesTupelfeld 0 args.types args.index))
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
    ) platform args s₃ rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

theorem TupleFieldParse : TupleFieldParseAussage := by
  intro scope args text pieces lex prod
  exact (Surface.TupleFieldDerivation scope).parse lex prod

end Gabbro.Core.Ast.Semantik
