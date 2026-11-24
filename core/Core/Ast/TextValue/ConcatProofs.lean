module

public import Core.Ast.TextValue.Concat
public import Core.Ast.Semantik.Formbeweise
public import Core.Ast.Semantik.Sicherheit
import Init.Omega

/-!
# TextConcat

Prove the pinned statements in this file.

- `TextConcatInversionAussage`
- `TextConcatDerivationAussage`
- `TextConcatBytesAussage`
- `TextConcatParseAussage`
- `TextConcatElaboriertAussage`
- `TextConcatRealisiertAussage`
- `TextConcatAnnahmeAussage`
- `TextConcatIdealAussage`
- `TextConcatEinheitAussage`
- `TextConcatImplAussage`
- `TextConcatErhaltungAussage`
- `TextConcatKernOrtAussage`
- `TextConcatRegelSicherAussage`
- `TextConcatRegelAntwortSicherAussage`
- `TextConcatKostenUndSpurAussage`
- `TextConcatErfuellbarAmAussage`
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter
open Gabbro.Core.Text
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Surface

private theorem noAddAtPrec6 (more : List Token) :
    ¬ Continues (Arith.add.precedence + 1) (Arith.add.token :: more) := by
  rintro ⟨op, rest, same, allowed⟩
  have opAdd : op = .arith .add :=
    Infix.token_injective (by simpa only [Infix.token] using (List.cons.inj same).1.symm)
  subst op
  change 6 ≤ 5 at allowed
  omega

theorem textConcatInversion : TextConcatInversionAussage := by
  intro scope a minimum input type left tree rest allowed read
  cases read with
  | stop blocked =>
      exact (blocked ⟨.arith .add, input, rfl, allowed⟩).elim
  | textConcat _ right _ reads tail =>
      exact ⟨_, right, _, reads, tail⟩

private theorem textConcatPrint (scope : Scope) (args : TextConcatArgs scope) :
    (textConcat scope).production args
      (((Category.expression scope).printPieces ((textConcat scope).tree args)).map
        PrintedToken.value) := by
  change postfixProduction (fun input rest =>
    ∃ rhs, ExprReads scope (Arith.add.precedence + 1) input args.left (Arith.add.token :: rhs) ∧
      ExprReads scope (Arith.add.precedence + 1) rhs args.right rest)
    ((Expr.textConcat args.left args.right).printTokens)
  have tokens : (Expr.textConcat args.left args.right).printTokens =
      openParen :: (args.left.printTokens ++ [Arith.add.token] ++ args.right.printTokens ++
        [closeParen]) := by
    simp only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons,
      List.map_nil, List.singleton_append, List.append_assoc, Arith.print_value,
      printOpen, printClose, printPunctuation, PrintedToken.unquoted,
      (show (Token.punctuation "(".toList : Token) = openParen by decide),
      (show (Token.punctuation ")".toList : Token) = closeParen by decide)]
    rfl
  rw [tokens]
  refine Or.inr ⟨_, rfl, ?_⟩
  refine ⟨args.right.printTokens ++ [closeParen], ?_, ?_⟩
  · simpa only [List.nil_append, List.singleton_append, List.cons_append, List.append_assoc] using
      (Expr.printReads args.left (noAddAtPrec6 (args.right.printTokens ++ [closeParen])))
  · exact Expr.printReads args.right noOperatorAtClose

private theorem suffix_length_le {a b : List Token} (h : a <:+ b) : a.length ≤ b.length := by
  rcases h with ⟨t, ht⟩
  rw [← ht]
  simp

private theorem textTailCompose {scope it it2 it3}
    {first : Expr scope it} {input : List Token} {tree : Expr scope it2} {rest : List Token}
    {tree2 : Expr scope it3} {final : List Token}
    (tail : ExprTail scope (Arith.add.precedence + 1) first input tree rest)
    (next : ExprTail scope 0 tree rest tree2 final) :
    ExprTail scope 0 first input tree2 final := by
  cases tail with
  | stop _ => exact next
  | binary op _ reads tail' =>
      have hlen : _ := suffix_length_le (ExprReads.consumes reads)
      exact .binary op (Nat.zero_le _) reads (textTailCompose tail' next)
  | div _ reads nonzero tail' =>
      have hlen : _ := suffix_length_le (ExprReads.consumes reads)
      exact .div (Nat.zero_le _) reads nonzero (textTailCompose tail' next)
  | compare op _ reads follows tail' =>
      have hlen : _ := suffix_length_le (ExprReads.consumes reads)
      exact .compare op (Nat.zero_le _) reads follows (textTailCompose tail' next)
  | logic op _ reads tail' =>
      have hlen : _ := suffix_length_le (ExprReads.consumes reads)
      exact .logic op (Nat.zero_le _) reads (textTailCompose tail' next)
  | arrayIndex base lower upper _ reads tail' =>
      have hlen : _ := suffix_length_le (ExprReads.consumes reads)
      exact .arrayIndex base lower upper (Nat.zero_le _) reads (textTailCompose tail' next)
  | tupleField base index _ tail' =>
      exact .tupleField base index (Nat.zero_le _) (textTailCompose tail' next)
  | recordField base field index written _ tail' =>
      exact .recordField base field index written (Nat.zero_le _) (textTailCompose tail' next)
  | textConcat left right' _ reads tail' =>
      have hlen : _ := suffix_length_le (ExprReads.consumes reads)
      exact .textConcat left right' (Nat.zero_le _) reads (textTailCompose tail' next)
  | textIndex base offset _ reads tail' =>
      have hlen : _ := suffix_length_le (ExprReads.consumes reads)
      exact .textIndex base offset (Nat.zero_le _) reads (textTailCompose tail' next)
  | substring base first' last _ reads₁ reads₂ tail' =>
      have hlen₁ : _ := suffix_length_le (ExprReads.consumes reads₁)
      have hlen₂ : _ := suffix_length_le (ExprReads.consumes reads₂)
      exact .substring base first' last (Nat.zero_le _) reads₁ reads₂
        (textTailCompose tail' next)
termination_by input.length
decreasing_by
  simp_all
  omega

private theorem textTailLowerConcat {scope a b it} {first : Expr scope it} {input : List Token}
    {tree : Expr scope (.text a)} {rhs final : List Token}
    (tail : ExprTail scope (Arith.add.precedence + 1) first input tree (Arith.add.token :: rhs))
    (right : Expr scope (.text b))
    (rightRead : ExprReads scope (Arith.add.precedence + 1) rhs right final)
    (blocked : ¬ Continues 0 final) :
    ExprTail scope 0 first input (Expr.textConcat tree right) final :=
  textTailCompose tail (.textConcat tree right (Nat.zero_le _) rightRead (.stop blocked))

theorem textConcatDerivation : TextConcatDerivationAussage := by
  intro scope
  refine ⟨?reads, textConcatPrint scope, ?erfuellbar⟩
  · intro args tokens production
    change ExprReads scope 0 tokens (Expr.textConcat args.left args.right) []
    rcases production with plain | grouped
    · rcases plain with ⟨rhs, leftRead, rightRead⟩
      cases leftRead with
      | atom atomRead tail =>
          exact .atom atomRead (textTailLowerConcat tail args.right rightRead noOperatorAtEnd)
    · rcases grouped with ⟨inside, rfl, body⟩
      rcases body with ⟨rhs, leftRead, rightRead⟩
      cases leftRead with
      | atom atomRead tail =>
          exact .atom (.grouped (.atom atomRead
            (textTailLowerConcat tail args.right rightRead noOperatorAtClose)))
            (.stop noOperatorAtEnd)
  · let decoded : List Char := []
    let a := (sourceUtf8 decoded).size
    let left : Expr scope (.text a) := .textLiteral decoded
    let args : TextConcatArgs scope := ⟨a, a, left, left⟩
    exact Rule.satisfiableOfPrint args (textConcatPrint scope args)

theorem textConcatBytes : TextConcatBytesAussage := by
  intro a b left right frame hleft hright
  have hl : left.bytes.size ≤ a := left.bound
  have hr : right.bytes.size ≤ b := right.bound
  dsimp
  simp [Befehl.auswerten, Rahmen.schreibe, wertAls, TextValue.concat, ByteArray.size_append,
    hleft, hright, left.bound, right.bound]
  all_goals
    first
    | rfl
    | exact Nat.add_le_add hl hr
    | omega

private theorem textConcatRootLookup (p : Fragment) (b : Befehl) :
    (p.anhaengen (.einzel b)).code[p.code.length]? = some b := by
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

private theorem textConcat_amOrt (scope : Scope) : (textConcatForm scope).RegelAmOrt := by
  intro args
  let p := (expr 0 args.left).anhaengen (expr 1 args.right)
  let b : Befehl := .textConcat 0 args.a args.b
  have hpos : (textConcatForm scope).position args = p.code.length := by
    dsimp [textConcatForm, p, Fragment.anhaengen]
    rw [List.length_append]
  rw [hpos]
  change (p.anhaengen (.einzel b)).code[p.code.length]? = some b
  exact textConcatRootLookup p b

private theorem textConcat_keine_invarianten (scope : Scope)
    (args : TextConcatArgs scope) :
    ((textConcatForm scope).fragment args).klauseln.invariant = [] := by
  change ((((expr 0 args.left).anhaengen (expr 1 args.right)).anhaengen
    (.einzel (Befehl.textConcat 0 args.a args.b))).klauseln.invariant) = []
  simp only [Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
    Quellklauseln.leer, List.append_nil]
  rw [expr_keine_invarianten 0 args.left, expr_keine_invarianten 1 args.right]
  rfl

theorem textConcatParse : TextConcatParseAussage := by
  intro scope args text pieces lexed production
  exact (textConcatDerivation scope).parse lexed production

theorem textConcatElaboriert : TextConcatElaboriertAussage := by
  intro scope platform args
  rfl

theorem textConcatRealisiert : TextConcatRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (textConcatForm scope).realisiert (textConcat_amOrt scope) platform args s
    running active live atPc

theorem textConcatAnnahme : TextConcatAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (textConcatForm scope)

theorem textConcatIdeal : TextConcatIdealAussage := by
  intro scope
  refine ⟨textConcat_amOrt scope, ?_⟩
  intro args
  refine ⟨Befehl.bestimmt _, ?_⟩
  intro c s w plans u
  rfl

theorem textConcatEinheit : TextConcatEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((textConcatForm scope).befehl args).kommutation⟩

theorem textConcatImpl : TextConcatImplAussage := by
  intro scope args c s w plans u
  rfl

theorem textConcatErhaltung : TextConcatErhaltungAussage := by
  intro scope
  apply Quellform.erhaltung
  intro args
  exact textConcat_keine_invarianten scope args

theorem textConcatKernOrt : TextConcatKernOrtAussage := by
  intro scope
  exact textConcat_amOrt scope

theorem textConcatRegelSicher : TextConcatRegelSicherAussage := by
  intro scope platform args
  exact Befehl.sicher ((textConcatForm scope).fragment args) platform
    (textConcat_keine_invarianten scope args) ((textConcatForm scope).befehl args)

theorem textConcatRegelAntwortSicher : TextConcatRegelAntwortSicherAussage := by
  intro scope platform args
  dsimp [RegelAntwortSicher]
  intro t c s choice stepPlan u spur next head rule execute
  let form := textConcatForm scope
  let b := form.befehl args
  have hplan : stepPlan = plan := (List.cons.inj rule.1).1
  subst stepPlan
  obtain ⟨rfl, _⟩ := b.vollzug_genau (w := choice) rule execute
  constructor
  · intro answer same
    cases same
  · intro answer
    exact List.not_mem_nil

theorem textConcatKostenUndSpur : TextConcatKostenUndSpurAussage := by
  intro scope platform args
  dsimp [TextInstructionCost]
  intro t c s choice stepPlan u spur next head rule execute
  let form := textConcatForm scope
  let b := form.befehl args
  obtain ⟨rfl, _⟩ := b.vollzug_genau (w := choice) rule execute
  refine ⟨rfl, rfl, ?_⟩
  change 0 + [stepPlan].length = 1
  rfl

theorem textConcatErfuellbarAm : TextConcatErfuellbarAmAussage := by
  intro platform start
  let decoded : List Char := []
  let a := (sourceUtf8 decoded).size
  let left : Expr [] (.text a) := .textLiteral decoded
  let args : TextConcatArgs [] := ⟨a, a, left, left⟩
  let form := textConcatForm []
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.textLiteral 0 decoded).nach eintritt s₀
  let s₂ := (Befehl.textLiteral 1 decoded).nach eintritt s₁
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.textLiteral 0 decoded, rfl, rfl, rfl⟩
  have second : E.system.ISchritt eintritt s₁ () [plan] s₂ :=
    ⟨.textLiteral 1 decoded, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₂ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start first) second
  refine ⟨args, ?_⟩
  dsimp [Quellform.TextErfuellbar]
  refine ⟨Ast.print (category := .expression []) (form.produktion.tree args), s₂,
    Ast.parse_print _, rfl, reached, ?_, ?_, ?_⟩
  · exact form.realisiert (textConcat_amOrt []) platform args s₂ rfl rfl rfl rfl
  · intro g guard
    simp [Befehl.guard] at guard
    cases guard
  · constructor
    · rfl
    · have h0 : (s₂.lokal eintritt).temp 0 = some ⟨.text a, TextValue.literal decoded⟩ := by
        dsimp [s₂, s₁, Befehl.nach, Befehl.auswerten, Rahmen.schreibe]
        simp [a]
      have h1 : (s₂.lokal eintritt).temp 1 = some ⟨.text a, TextValue.literal decoded⟩ := by
        dsimp [s₂, Befehl.nach, Befehl.auswerten, Rahmen.schreibe]
        simp [a]
      have htmp := (textConcatBytes a a (TextValue.literal decoded) (TextValue.literal decoded)
          (s₂.lokal eintritt) h0 h1).1
      change (((((textConcatForm []).befehl args).nach eintritt s₂).lokal eintritt).temp 0).isSome = true
      dsimp [textConcatForm, args]
      rw [Befehl.nach]
      simp only [Function.update_self]
      rw [htmp]
      rfl

end Gabbro.Core.Ast.Semantik
