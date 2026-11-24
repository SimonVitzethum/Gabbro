module

public import Core.Ast.TextValue.Substring
public import Core.Ast.Semantik.Formbeweise
public import Core.Ast.Semantik.Quellform
public import Core.Ast.Surface
public import Core.Ast.Print
public import Core.Ast.Expression

import Init.Omega

/-!
# Substring

Prove the pinned statements in this file.

- `SubstringDerivationAussage`
- `SubstringSuffixAussage`
- `SubstringBytesAussage`
- `SubstringParseAussage`
- `SubstringElaboriertAussage`
- `SubstringRealisiertAussage`
- `SubstringAnnahmeAussage`
- `SubstringIdealAussage`
- `SubstringEinheitAussage`
- `SubstringImplAussage`
- `SubstringErhaltungAussage`
- `SubstringKernOrtAussage`
- `SubstringRegelSicherAussage`
- `SubstringRegelAntwortSicherAussage`
- `SubstringKostenUndSpurAussage`
- `SubstringErfuellbarAmAussage`
-/

@[expose] public section

open Gabbro.Core.Text
open Gabbro.Core.Ast
open Gabbro.Core.Annahme

namespace Gabbro.Core.Ast.Surface

private theorem substringInfixPrecLe7 (op : Infix) : op.precedence ≤ 7 := by
  cases op with
  | arith a => cases a <;> simp only [Infix.precedence, Arith.precedence] <;> omega
  | div => simp only [Infix.precedence] <;> omega
  | compare c => simp only [Infix.precedence] <;> omega
  | logic l => cases l <;> simp only [Infix.precedence] <;> omega
  | index => simp only [Infix.precedence] <;> omega
  | projection => simp only [Infix.precedence] <;> omega

private theorem substringNoOpAtSlice : ¬ Continues minimum (sliceRange :: more) := by
  rintro ⟨op, _, same, _⟩
  have htok : op.token = sliceRange := (List.cons.inj same).1.symm
  cases op with
  | arith a => cases a <;> simp [Infix.token, Arith.token, sliceRange] at htok
  | div => simp [Infix.token, sliceRange] at htok
  | compare c => cases c <;> simp [Infix.token, Compare.spelling, sliceRange] at htok
  | logic l => cases l <;> simp [Infix.token, Logic.spelling, sliceRange] at htok
  | index => simp [Infix.token, openBracket, sliceRange] at htok
  | projection => simp [Infix.token, dot, sliceRange] at htok

private theorem substringPrintTokens
    (base : Expr scope (.text capacity))
    (first : Expr scope (.int lo₁ hi₁)) (last : Expr scope (.int lo₂ hi₂)) :
    (Expr.substring base first last).printTokens =
      openParen :: (base.printTokens ++ [openBracket] ++ first.printTokens ++
        [sliceRange] ++ last.printTokens ++ [closeBracket, closeParen]) := by
  simp only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons, List.map_nil,
    List.singleton_append, List.append_assoc, printOpen, printClose, printOpenBracket,
    printCloseBracket, printSliceRange, printPunctuation, PrintedToken.unquoted, openParen,
    closeParen,
    (show (Token.punctuation "(".toList : Token) = openParen by decide),
    (show (Token.punctuation "[".toList : Token) = openBracket by decide),
    (show (Token.punctuation "..".toList : Token) = sliceRange by decide),
    (show (Token.punctuation "]".toList : Token) = closeBracket by decide),
    (show (Token.punctuation ")".toList : Token) = closeParen by decide)]
  rfl

private theorem substringPrint (scope : Scope) (args : SubstringArgs scope) :
    (substring scope).production args
      (((Category.expression scope).printPieces ((substring scope).tree args)).map PrintedToken.value) := by
  change postfixProduction (fun input rest =>
    ∃ first last, ExprReads scope 8 input args.base (openBracket :: first) ∧
      ExprReads scope 0 first args.first (sliceRange :: last) ∧
      ExprReads scope 0 last args.last (closeBracket :: rest))
    ((Expr.substring args.base args.first args.last).printTokens)
  rw [substringPrintTokens]
  right
  refine ⟨args.base.printTokens ++ [openBracket] ++ args.first.printTokens ++
    [sliceRange] ++ args.last.printTokens ++ [closeBracket, closeParen], rfl, ?_⟩
  refine ⟨args.first.printTokens ++ [sliceRange] ++ args.last.printTokens ++
    [closeBracket, closeParen], args.last.printTokens ++ [closeBracket, closeParen], ?_, ?_, ?_⟩
  · simpa only [List.singleton_append, List.cons_append, List.append_assoc, List.nil_append] using
      (Expr.printReads (minimum := 8)
        (rest := openBracket :: (args.first.printTokens ++ [sliceRange] ++
          args.last.printTokens ++ [closeBracket, closeParen]))
        args.base (by
          intro cont
          obtain ⟨op, more, same, allowed⟩ := cont
          have prec := substringInfixPrecLe7 op
          omega))
  · simpa only [List.singleton_append, List.cons_append, List.append_assoc, List.nil_append] using
      (Expr.printReads (minimum := 0)
        (rest := sliceRange :: (args.last.printTokens ++ [closeBracket, closeParen]))
        args.first substringNoOpAtSlice)
  · exact Expr.printReads (rest := [closeBracket, closeParen]) args.last noOperatorAtCloseBracket

private theorem substringErfuellbar (scope : Scope) : (substring scope).Satisfiable := by
  let base : Expr scope (.text (sourceUtf8 []).size) := .textLiteral []
  let args : SubstringArgs scope := ⟨(sourceUtf8 []).size, 0, 0, 0, 0, base, .lit 0, .lit 0⟩
  exact Rule.satisfiableOfPrint args (substringPrint scope args)

private theorem substringDerivationLocal : Gabbro.Core.Ast.Semantik.SubstringDerivationAussage := by
  intro scope
  refine ⟨?_, substringPrint scope, substringErfuellbar scope⟩
  · intro args tokens production
    change ExprReads scope 0 tokens (Expr.substring args.base args.first args.last) []
    rcases production with plain | grouped
    · rcases plain with ⟨first, last, baseRead, firstRead, lastRead⟩
      cases baseRead with
      | atom atomRead highTail =>
          cases highTail with
          | stop =>
              exact .atom atomRead (.substring args.base args.first args.last (by omega)
                firstRead lastRead (.stop noOperatorAtEnd))
          | binary op hle _ _ =>
              have prec : op.precedence ≤ 7 := by
                simpa [Infix.precedence] using substringInfixPrecLe7 (.arith op)
              omega
          | div hle _ _ _ =>
              have prec := substringInfixPrecLe7 .div
              omega
          | compare op hle _ _ =>
              have prec := substringInfixPrecLe7 (.compare op)
              omega
          | logic op hle _ _ =>
              have prec := substringInfixPrecLe7 (.logic op)
              omega
          | arrayIndex _ _ _ hle _ _ =>
              have prec := substringInfixPrecLe7 .index
              omega
          | tupleField _ _ hle _ =>
              have prec := substringInfixPrecLe7 .projection
              omega
          | recordField _ _ _ _ hle _ =>
              have prec := substringInfixPrecLe7 .projection
              omega
          | textConcat _ _ hle _ _ =>
              simp only [Arith.precedence] at hle
              omega
          | textIndex _ _ hle _ _ =>
              have prec := substringInfixPrecLe7 .index
              omega
          | substring _ _ _ hle _ _ _ =>
              have prec := substringInfixPrecLe7 .index
              omega
    · rcases grouped with ⟨inside, rfl, first, last, baseRead, firstRead, lastRead⟩
      cases baseRead with
      | atom atomRead highTail =>
          cases highTail with
          | stop =>
              have inner : ExprReads scope 0 inside
                  (Expr.substring args.base args.first args.last) [closeParen] :=
                .atom atomRead (.substring args.base args.first args.last (by omega)
                  firstRead lastRead (.stop noOperatorAtClose))
              exact .atom (.grouped inner) (.stop noOperatorAtEnd)
          | binary op hle _ _ =>
              have prec : op.precedence ≤ 7 := by
                simpa [Infix.precedence] using substringInfixPrecLe7 (.arith op)
              omega
          | div hle _ _ _ =>
              have prec := substringInfixPrecLe7 .div
              omega
          | compare op hle _ _ =>
              have prec := substringInfixPrecLe7 (.compare op)
              omega
          | logic op hle _ _ =>
              have prec := substringInfixPrecLe7 (.logic op)
              omega
          | arrayIndex _ _ _ hle _ _ =>
              have prec := substringInfixPrecLe7 .index
              omega
          | tupleField _ _ hle _ =>
              have prec := substringInfixPrecLe7 .projection
              omega
          | recordField _ _ _ _ hle _ =>
              have prec := substringInfixPrecLe7 .projection
              omega
          | textConcat _ _ hle _ _ =>
              simp only [Arith.precedence] at hle
              omega
          | textIndex _ _ hle _ _ =>
              have prec := substringInfixPrecLe7 .index
              omega
          | substring _ _ _ hle _ _ _ =>
              have prec := substringInfixPrecLe7 .index
              omega

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem substringRootLookup (p : Fragment) (b : Befehl) :
    (p.anhaengen (.einzel b)).code[p.code.length]? = some b := by
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

private theorem substringAmOrt (scope : Scope) : (substringForm scope).RegelAmOrt := by
  intro args
  dsimp [substringForm, Quellform.fragment, fragment, expr]
  let p := ((expr 0 args.base).anhaengen (expr 1 args.first)).anhaengen (expr 2 args.last)
  let b : Befehl := .substring 0 args.capacity
  change (p.anhaengen (.einzel b)).code[
    (expr 0 args.base).code.length + (expr 1 args.first).code.length +
      (expr 2 args.last).code.length]? = some b
  have hlen : p.code.length = (expr 0 args.base).code.length +
      (expr 1 args.first).code.length + (expr 2 args.last).code.length := by
    simp [p, Fragment.anhaengen, List.length_append]
    omega
  rw [← hlen]
  exact substringRootLookup p b

theorem substringDerivation : SubstringDerivationAussage :=
  Surface.substringDerivationLocal

theorem substringSuffix : SubstringSuffixAussage := by
  intro scope capacity type minimum first rest base tree allowed read
  generalize htok : openBracket :: first = toks at read
  cases read with
  | stop blocked =>
      exact (blocked ⟨.index, first, htok.symm, allowed⟩).elim
  | textConcat left right hle rightRead tail =>
      have hname : openBracket = Arith.add.token := (List.cons.inj htok).1
      simp [Arith.token, openBracket] at hname
  | textIndex tbase offset hle offsetRead tail =>
      have hfirst : first = _ := (List.cons.inj htok).2
      subst first
      have hclose : closeBracket :: _ <:+ _ := ExprReads.consumes offsetRead
      have hmore : _ <:+ _ := (List.suffix_cons closeBracket _).trans hclose
      have hrest : rest <:+ _ := ExprTail.consumes tail
      exact hrest.trans hmore
  | substring sbase sf sl hle firstRead lastRead tail =>
      have hfirst : first = _ := (List.cons.inj htok).2
      subst first
      have hslice : sliceRange :: _ <:+ _ := ExprReads.consumes firstRead
      have hlast : _ <:+ _ := (List.suffix_cons sliceRange _).trans hslice
      have hclose : closeBracket :: _ <:+ _ := ExprReads.consumes lastRead
      have hmore : _ <:+ _ := ((List.suffix_cons closeBracket _).trans hclose).trans hlast
      exact (ExprTail.consumes tail).trans hmore

theorem substringBytes : SubstringBytesAussage := by
  intro capacity text first last frame htext hfirst hlast
  dsimp
  let i : Int := first.zahl.wert
  let j : Int := last.zahl.wert
  let b : Befehl := .substring 0 capacity
  let next : Rahmen := b.auswerten frame
  have hguard : b.guard frame = some ⟨.teilfolge, (i, j, text.bytes.size)⟩ := by
    simp [b, i, j, Befehl.guard, htext, hfirst, hlast, wertAls, text.bound]
    rfl
  change b.guard frame = some ⟨.teilfolge, (i, j, text.bytes.size)⟩ ∧
    (waechterBedarf .teilfolge (i, j, text.bytes.size) →
      let out := text.slice i.toNat j.toNat
      next.temp 0 = some ⟨.text capacity, out⟩ ∧ next.pc = frame.pc + 1 ∧
        out.bytes.size = j.toNat - i.toNat ∧
        ∀ k < out.bytes.size, out.bytes[k]? = text.bytes[i.toNat + k]?) ∧
    (¬ waechterBedarf .teilfolge (i, j, text.bytes.size) → next.stopp = some .ungueltigerWert)
  refine ⟨hguard, ?_, ?_⟩
  · intro hw
    have hcond : 0 ≤ i ∧ i ≤ j ∧ j ≤ (text.bytes.size : Int) := by
      simpa [waechterBedarf] using hw
    have haus : next = frame.schreibe 0 (some ⟨.text capacity, text.slice i.toNat j.toNat⟩) := by
      simp [next, b, i, j, Befehl.auswerten, htext, hfirst, hlast, wertAls, text.bound, hcond]
    have hjle : j.toNat ≤ text.bytes.size := by omega
    have hilj : i.toNat ≤ j.toNat := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [haus]
      simp [Rahmen.schreibe]
    · rw [haus]
      rfl
    · change (text.slice i.toNat j.toNat).bytes.size = j.toNat - i.toNat
      simp only [TextValue.slice, ByteArray.size_extract]
      rw [min_eq_left hjle]
    · intro k hk
      have hk' : k < (text.bytes.extract i.toNat j.toNat).size := by
        simpa [TextValue.slice] using hk
      have hk'' : k < j.toNat - i.toNat := by
        simpa [ByteArray.size_extract, min_eq_left hjle] using hk'
      have hik : i.toNat + k < text.bytes.size := by omega
      change (text.bytes.extract i.toNat j.toNat)[k]? = text.bytes[i.toNat + k]?
      rw [show (text.bytes.extract i.toNat j.toNat)[k]? = some ((text.bytes.extract i.toNat j.toNat)[k]'hk') by simp [hk']]
      rw [show text.bytes[i.toNat + k]? = some (text.bytes[i.toNat + k]'hik) by simp [hik]]
      congr 1
      exact ByteArray.getElem_extract (start := i.toNat) (stop := j.toNat) hk'
  · intro hnw
    have hnot : ¬ (0 ≤ i ∧ i ≤ j ∧ j ≤ (text.bytes.size : Int)) := by
      intro hc
      exact hnw (by simpa [waechterBedarf] using hc)
    have haus : next = frame.halt .ungueltigerWert := by
      simp [next, b, i, j, Befehl.auswerten, htext, hfirst, hlast, wertAls, text.bound, hnot]
    rw [haus]
    rfl

theorem substringParse : SubstringParseAussage := by
  intro scope args text pieces lexed production
  exact (substringDerivation scope).parse lexed production

theorem substringElaboriert : SubstringElaboriertAussage := by
  intro scope platform args
  rfl

theorem substringRealisiert : SubstringRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (substringForm scope).realisiert (substringAmOrt scope) platform args s
    running active live atPc

theorem substringAnnahme : SubstringAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (substringForm scope)

theorem substringIdeal : SubstringIdealAussage := by
  intro scope
  refine ⟨substringAmOrt scope, ?_⟩
  intro args
  exact ⟨((substringForm scope).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem substringEinheit : SubstringEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((substringForm scope).befehl args).kommutation⟩

theorem substringImpl : SubstringImplAussage := by
  intro scope args c s w plans u
  rfl

theorem substringErhaltung : SubstringErhaltungAussage := by
  intro scope
  exact Quellform.erhaltung (substringForm scope)
    (fun args => expr_keine_invarianten 0 ((Surface.substring scope).tree args).2)

theorem substringKernOrt : SubstringKernOrtAussage := by
  intro scope
  exact substringAmOrt scope

theorem substringRegelSicher : SubstringRegelSicherAussage := by
  intro scope platform args
  exact (substringErhaltung scope platform args).2.2.2

theorem substringRegelAntwortSicher : SubstringRegelAntwortSicherAussage := by
  intro scope platform args
  dsimp only
  intro tstamp ctx st choice stepPlan u spur trail _ hImpl hExec
  let p := (substringForm scope).fragment args
  let b := (substringForm scope).befehl args
  obtain ⟨htrail, _⟩ := b.vollzug_genau (e := (p.einheit platform).einrichtung) (w := choice) hImpl hExec
  have hplan : stepPlan = plan := (List.cons.inj hImpl.1).1
  subst stepPlan
  subst spur
  constructor
  · intro answer
    simp [plan]
  · intro answer
    exact List.not_mem_nil

theorem substringKostenUndSpur : SubstringKostenUndSpurAussage := by
  intro scope platform args
  dsimp only
  intro tstamp ctx st choice stepPlan u spur trail _ hImpl hExec
  let p := (substringForm scope).fragment args
  let b := (substringForm scope).befehl args
  obtain ⟨htrail, _⟩ := b.vollzug_genau (e := (p.einheit platform).einrichtung) (w := choice) hImpl hExec
  subst spur
  refine ⟨rfl, rfl, ?_⟩
  have hplan : stepPlan = plan := (List.cons.inj hImpl.1).1
  subst stepPlan
  simp [Fragment.einheit]

theorem substringErfuellbarAm : SubstringErfuellbarAmAussage := by
  intro platform start
  let cap : Nat := (sourceUtf8 []).size
  let base : Expr [] (.text cap) := .textLiteral []
  let args : Surface.SubstringArgs [] := ⟨cap, 0, 0, 0, 0, base, .lit 0, .lit 0⟩
  refine ⟨args, ?_⟩
  let form := substringForm []
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (.textLiteral 0 [] : Befehl).nach eintritt s₀
  let s₂ := (.literal 1 0 : Befehl).nach eintritt s₁
  let s₃ := (.literal 2 0 : Befehl).nach eintritt s₂
  have h₁ : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.textLiteral 0 [], rfl, rfl, rfl⟩
  have h₂ : E.system.ISchritt eintritt s₁ () [plan] s₂ := ⟨.literal 1 0, rfl, rfl, rfl⟩
  have h₃ : E.system.ISchritt eintritt s₂ () [plan] s₃ := ⟨.literal 2 0, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₃ :=
    .schritt eintritt () [plan]
      (.schritt eintritt () [plan] (.schritt eintritt () [plan] .start h₁) h₂) h₃
  let b : Befehl := form.befehl args
  let zero : Ganzzahl := ⟨0, 0, Zahl.literal 0⟩
  have ht0 : (s₃.lokal eintritt).temp 0 = some ⟨.text cap, TextValue.literal []⟩ := by
    simp [s₃, s₂, s₁, s₀, Befehl.nach, Befehl.auswerten, Rahmen.schreibe, cap]
  have ht1 : (s₃.lokal eintritt).zahl 1 = some zero := by
    simp [s₃, s₂, s₁, s₀, Befehl.nach, Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl,
      alsGanzzahl, zero]
  have ht2 : (s₃.lokal eintritt).zahl 2 = some zero := by
    simp [s₃, s₂, s₁, s₀, Befehl.nach, Befehl.auswerten, Rahmen.schreibe, Rahmen.zahl,
      alsGanzzahl, zero]
  have hb := substringBytes cap (TextValue.literal []) zero zero (s₃.lokal eintritt) ht0 ht1 ht2
  dsimp [Quellform.TextErfuellbar]
  refine ⟨Ast.print (category := .expression []) (form.produktion.tree args), s₃,
    Ast.parse_print _, rfl, reached, ?_, ?_, ?_⟩
  · exact form.realisiert (substringAmOrt []) platform args s₃ rfl rfl rfl rfl
  · intro g guard
    have hgval : (form.befehl args).guard (s₃.lokal eintritt) =
        some ⟨.teilfolge, (0, 0, (TextValue.literal [] : TextValue cap).bytes.size)⟩ := by
      simpa [form, substringForm, args, b, zero, Zahl.literal] using hb.1
    rw [hgval] at guard
    cases guard
    simp [waechterBedarf]
  · have hw : waechterBedarf .teilfolge
        (0, 0, (TextValue.literal [] : TextValue cap).bytes.size) := by
      simp [waechterBedarf]
    have hgood := hb.2.1 hw
    refine ⟨?_, ?_⟩
    · simp [form, substringForm, args, b, s₃, s₂, s₁, s₀, Befehl.nach,
        Befehl.auswerten, Rahmen.schreibe, waechterBedarf, cap]
    · have ht := hgood.1
      have hsame : (b.nach eintritt s₃).lokal eintritt =
          (Befehl.substring 0 cap).auswerten (s₃.lokal eintritt) := by
        simp [b, form, substringForm, args, Befehl.nach]
      rw [hsame, ht]
      simp

end Gabbro.Core.Ast.Semantik
