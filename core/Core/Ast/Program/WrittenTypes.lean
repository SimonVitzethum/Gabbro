module

public import Core.Ast.LowLevel.TypeTokens

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def intSpelling (signed : Bool) (width : Nat) : List Char :=
  (if signed then 'i' else 'u') :: (toString width).toList

-- Mirror printInteger.lexeme using the decimal digit tail of the width.
def intTypeName (signed : Bool) (width : Nat) : Identifier :=
  ⟨intSpelling signed width, (if signed then 'i' else 'u'), (toString width).toList, rfl, by
    cases signed <;> exact .inl (.inl ⟨by decide, by decide⟩), by
    intro c member
    right; change IsDecimalDigit c
    have member' : c ∈ Nat.toDigits 10 width := by simpa only [Nat.toString_eq_ofList_toDigits, String.toList_ofList] using member
    have digit : c.isDigit := Nat.isDigit_of_mem_toDigits (n := width) (b := 10) (Nat.zero_lt_succ _) (Nat.le_refl _) (c := c) member'
    simpa only [IsDecimalDigit, Char.le_def, Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] using digit⟩

def signedPieces (number : Int) : List PrintedToken :=
  if number < 0 then [Arith.sub.print, printInteger number.natAbs] else [printInteger number.natAbs]

def printStringType : PrintedToken := printProgramWord 's' ['t', 'r', 'i', 'n', 'g']
  (by decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c (rfl | rfl | rfl | rfl | rfl) <;> decide)

def printMax : PrintedToken := printProgramWord 'm' ['a', 'x'] (by decide)
  (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c (rfl | rfl) <;> decide)

def printIndex : PrintedToken := printProgramWord 'i' ['n', 'd', 'e', 'x'] (by decide) (by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl | rfl) <;> decide)

def printInto : PrintedToken := printProgramWord 'i' ['n', 't', 'o'] (by decide) (by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl) <;> decide)

def printOption : PrintedToken := printProgramWord 'o' ['p', 't', 'i', 'o', 'n'] (by decide) (by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro c (rfl | rfl | rfl | rfl | rfl) <;> decide)

mutual


def WrittenType.printPieces : WrittenType → List PrintedToken
  | .bool => [printBoolType]
  | .integer signed width none => [(intTypeName signed width).print]
  | .integer signed width (some (lo, hi)) =>
    [(intTypeName signed width).print, printIn] ++ signedPieces lo ++ [printClosedRange] ++ signedPieces hi
  | .array element count => [printOpenBracket] ++ element.printPieces ++
      [printSemicolon, printInteger count, printCloseBracket]
  | .tuple first second rest => [printOpen] ++ first.printPieces ++ [printComma] ++
      second.printPieces ++ rest.printTail ++ [printClose]
  | .text capacity => [printStringType, printMax, printInteger capacity]
  | .index carrier _ => [printIndex, printInto, carrier.print]
  | .indexOption carrier _ => [printOption, printIndex, printInto, carrier.print]
  | .address space => space.printPieces
  | .ownedRegion => LowLevel.printOwnedRegion

def WrittenTypes.printTail : WrittenTypes → List PrintedToken
  | .empty => []
  | .next head tail => printComma :: head.printPieces ++ tail.printTail

end

inductive SignedReads : List Token → Int → List Token → Prop where
  | positive : SignedReads (.natural n :: rest) n rest
  | negative : SignedReads (minus :: .natural n :: rest) (-(n : Int)) rest

mutual

inductive TypeReads (scope : Scope) : List Token → WrittenType → List Token → Prop where
  | bool : TypeReads scope (keyword "bool" :: rest) .bool rest
  | integer (valid : (WrittenType.integer signed width none).valid scope)
      (closed : ∀ more, rest ≠ keyword "in" :: more) :
      TypeReads scope (.word (intSpelling signed width) :: rest) (.integer signed width none) rest
  | interval (valid : (WrittenType.integer signed width (some (lo, hi))).valid scope) :
      SignedReads input lo (closedRange :: more) → SignedReads more hi rest →
      TypeReads scope (.word (intSpelling signed width) :: keyword "in" :: input)
        (.integer signed width (some (lo, hi))) rest
  | array (count : Nat) (bound : Expr [] (.int count count)) :
      TypeReads scope input element (semicolon :: boundInput) →
      ExprReads [] 0 boundInput bound (closeBracket :: rest) →
      TypeReads scope (openBracket :: input) (.array element count) rest
  | tuple : TypeReads scope input first (comma :: secondInput) → TypeReads scope secondInput second more →
      TypeItemsTail scope more tail rest → TypeReads scope (openParen :: input) (.tuple first second tail) rest
  | text : TypeReads scope (keyword "string" :: keyword "max" :: .natural capacity :: rest) (.text capacity) rest
  | index (carrier : Identifier) (resolved : scope.carrierCount carrier = some count) :
      TypeReads scope (keyword "index" :: keyword "into" :: .word carrier.val :: rest) (.index carrier count) rest
  | indexOption (carrier : Identifier) (resolved : scope.carrierCount carrier = some count) :
      TypeReads scope (keyword "option" :: keyword "index" :: keyword "into" :: .word carrier.val :: rest)
        (.indexOption carrier count) rest
  | address (space : LowLevel.AddressSpace) :
      TypeReads scope (keyword "address" :: .punctuation ['<'] ::
        keyword space.name :: .punctuation ['>'] :: rest) (.address space) rest
  | ownedRegion : TypeReads scope
      (keyword "region" :: .punctuation ['<'] :: keyword "normal" :: comma ::
        keyword "rw" :: .punctuation ['>'] :: rest) .ownedRegion rest

inductive TypeItemsTail (scope : Scope) : List Token → WrittenTypes → List Token → Prop where
  | close : TypeItemsTail scope (closeParen :: rest) .empty rest
  | comma : TypeReads scope input head more → TypeItemsTail scope more tail rest →
      TypeItemsTail scope (comma :: input) (.next head tail) rest

end

-- Mirror AtomReads.lit_inversion and exclude the signed arm by token kind.
theorem SignedReads.deterministic (left : SignedReads input a rest) (right : SignedReads input b more) :
    a = b ∧ rest = more := by
  cases left with
  | positive => cases right with | positive => exact ⟨rfl, rfl⟩
  | negative => cases right with | negative => exact ⟨rfl, rfl⟩

private theorem intSpelling_not_text : ∀ (s : Bool) (w : Nat), keyword "string" ≠ .word (intSpelling s w) := by
  intro s w same
  cases s <;> cases same
private theorem intSpelling_not_option : ∀ (s : Bool) (w : Nat), keyword "option" ≠ .word (intSpelling s w) := by
  intro s w same
  cases s <;> cases same
private theorem intSpelling_not_index : ∀ (s : Bool) (w : Nat), intSpelling s w ≠ "index".toList := by
  intro s w h
  cases s with
  | false => cases h
  | true =>
    have tail : (toString w).toList = ['n', 'd', 'e', 'x'] := (List.cons.inj h).2
    have digits : (toString w).toList = Nat.toDigits 10 w := by
      rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
    have member : 'n' ∈ Nat.toDigits 10 w := by
      rw [← digits, tail]
      exact List.mem_cons_self
    have digit := Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) member
    contradiction

local macro "different_type_head" equal:ident : tactic =>
  `(tactic|
    (have head := (List.cons.inj $equal).1
     simp only [keyword, String.reduceToList, Token.word.injEq, List.cons.injEq,
       Char.reduceEq, false_and, reduceCtorEq] at head))

local macro "different_integer_head" equal:ident : tactic =>
  `(tactic|
    (have head := Token.word.inj (List.cons.inj $equal).1
     unfold intSpelling at head
     split at head <;> cases head))

private theorem textType_det
    (other : TypeReads scope input out rest')
    (equality : keyword "string" :: keyword "max" :: .natural capacity :: rest = input) :
    WrittenType.text capacity = out ∧ rest = rest' := by
  cases other with
  | text =>
    simp only [List.cons.injEq, Token.natural.injEq, true_and] at equality
    obtain ⟨rfl, rfl⟩ := equality
    exact ⟨rfl, rfl⟩
  | integer => exact (intSpelling_not_text _ _ (List.cons.inj equality).1).elim
  | interval => exact (intSpelling_not_text _ _ (List.cons.inj equality).1).elim
  | _ => different_type_head equality

private theorem carrierIndex_det
    (carrier : Identifier) (resolved : scope.carrierCount carrier = some count)
    (other : TypeReads scope input out rest')
    (equality : keyword "index" :: keyword "into" :: .word carrier.val :: rest = input) :
    WrittenType.index carrier count = out ∧ rest = rest' := by
  cases other with
  | index otherCarrier otherResolved =>
    simp only [List.cons.injEq, Token.word.injEq, true_and] at equality
    obtain ⟨spelling, rfl⟩ := equality
    cases Subtype.ext spelling
    cases Option.some.inj (resolved.symm.trans otherResolved)
    exact ⟨rfl, rfl⟩
  | integer =>
    exact (intSpelling_not_index _ _ (Token.word.inj (List.cons.inj equality).1).symm).elim
  | interval =>
    exact (intSpelling_not_index _ _ (Token.word.inj (List.cons.inj equality).1).symm).elim
  | _ => different_type_head equality

private theorem carrierOption_det
    (carrier : Identifier) (resolved : scope.carrierCount carrier = some count)
    (other : TypeReads scope input out rest')
    (equality : keyword "option" :: keyword "index" :: keyword "into" :: .word carrier.val :: rest = input) :
    WrittenType.indexOption carrier count = out ∧ rest = rest' := by
  cases other with
  | indexOption otherCarrier otherResolved =>
    simp only [List.cons.injEq, Token.word.injEq, true_and] at equality
    obtain ⟨spelling, rfl⟩ := equality
    cases Subtype.ext spelling
    cases Option.some.inj (resolved.symm.trans otherResolved)
    exact ⟨rfl, rfl⟩
  | integer => exact (intSpelling_not_option _ _ (List.cons.inj equality).1).elim
  | interval => exact (intSpelling_not_option _ _ (List.cons.inj equality).1).elim
  | _ => different_type_head equality

-- Mirror ExprReads.deterministic, dispatch on the width spelling and then on in.
theorem TypeReads.deterministic (left : TypeReads scope input a rest) (right : TypeReads scope input b more) :
    a = b ∧ rest = more := by
  have not_bool : ∀ (s : Bool) (w : Nat), intSpelling s w ≠ "bool".toList := by
    intro s w h
    cases s <;> cases h
  have spelling_inj : ∀ {s w s' w'}, intSpelling s w = intSpelling s' w' → s = s' ∧ w = w' := by
    intro s w s' w' h
    have hh := congrArg List.head? h; have ht := congrArg List.tail h
    have hc : (if s then 'i' else 'u') = (if s' then 'i' else 'u') := Option.some.inj hh
    have hs : s = s' := by cases s <;> cases s' <;> first | rfl | cases hc
    cases hs
    have ht' : (toString w).toList = (toString w').toList := by simpa only [intSpelling, List.tail_cons] using ht
    have hdigits : Nat.toDigits 10 w = Nat.toDigits 10 w' := by
      simpa only [Nat.toString_eq_ofList_toDigits, String.toList_ofList] using ht'
    have hv : w = w' := by
      have hv' := congrArg (fun l => Nat.ofDigitChars 10 l 0) hdigits
      simpa only [Nat.ofDigitChars_ten_toDigits] using hv'
    exact ⟨rfl, hv⟩
  refine (TypeReads.rec
    (motive_1 := fun input tree rest _deriv => ∀ (input' : List Token) (b' : WrittenType) (more' : List Token),
      TypeReads scope input' b' more' → input = input' → tree = b' ∧ rest = more')
    (motive_2 := fun input tree rest _ =>
      ∀ input' tree' rest', TypeItemsTail scope input' tree' rest' →
        input = input' → tree = tree' ∧ rest = rest')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ left) input b more right rfl
  · intro rest input' b' more' rightDeriv hEq
    cases rightDeriv
    case bool => injection hEq with hword htail; exact ⟨rfl, htail⟩
    case integer valid' closed' =>
        injection hEq with hword htail; injection hword with hspell
        exact (not_bool _ _ hspell.symm).elim
    case interval valid' loRead' hiRead' =>
        injection hEq with hword htail; injection hword with hspell
        exact (not_bool _ _ hspell.symm).elim
    all_goals first | different_type_head hEq | different_integer_head hEq
  · intro signed width rest valid closed input' b' more' rightDeriv hEq
    cases rightDeriv
    case bool =>
        injection hEq with hword htail; injection hword with hspell
        exact (not_bool _ _ hspell).elim
    case integer valid' closed' =>
        injection hEq with hword htail; injection hword with hspell
        obtain ⟨hs, hw⟩ := spelling_inj hspell
        cases hs; cases hw; exact ⟨rfl, htail⟩
    case interval valid' loRead' hiRead' =>
        injection hEq with hword htail; injection hword with hspell
        exact (closed _ htail).elim
    case index =>
      exact (intSpelling_not_index _ _ (Token.word.inj (List.cons.inj hEq).1)).elim
    case text =>
      exact (intSpelling_not_text _ _ (List.cons.inj hEq).1.symm).elim
    case indexOption =>
      exact (intSpelling_not_option _ _ (List.cons.inj hEq).1.symm).elim
    all_goals first | different_type_head hEq | different_integer_head hEq
  · intro signed width lo hi input more rest valid loRead hiRead input' b' more' rightDeriv hEq
    cases rightDeriv
    case bool =>
        injection hEq with hword htail; injection hword with hspell
        exact (not_bool _ _ hspell).elim
    case integer valid' closed' =>
        injection hEq with hword htail; injection hword with hspell
        exact (closed' _ htail.symm).elim
    case interval valid' loRead' hiRead' =>
        injection hEq with hword htail; injection hword with hspell
        obtain ⟨hs, hw⟩ := spelling_inj hspell
        cases hs; cases hw; cases htail
        obtain ⟨hlo, hmore⟩ := SignedReads.deterministic loRead loRead'
        cases hmore
        obtain ⟨hhi, hrest⟩ := SignedReads.deterministic hiRead hiRead'
        cases hlo; cases hhi; exact ⟨rfl, hrest⟩
    case index =>
      exact (intSpelling_not_index _ _ (Token.word.inj (List.cons.inj hEq).1)).elim
    case text =>
      exact (intSpelling_not_text _ _ (List.cons.inj hEq).1.symm).elim
    case indexOption =>
      exact (intSpelling_not_option _ _ (List.cons.inj hEq).1.symm).elim
    all_goals first | different_type_head hEq | different_integer_head hEq
  · intro _ _ _ _ count bound elementRead boundRead ih input' out rest' other equality
    cases other with
    | array otherCount otherBound otherElement otherBoundRead =>
      obtain ⟨rfl, suffix⟩ := ih _ _ _ otherElement (List.cons.inj equality).2
      cases (List.cons.inj suffix).2
      obtain ⟨same, more⟩ := ExprReads.deterministic boundRead otherBoundRead
      have types := congrArg Sigma.fst same
      have counts : count = otherCount := by
        have endpoints : (count : Int) = otherCount := by injection types
        omega
      cases counts
      exact ⟨rfl, (List.cons.inj more).2⟩
    | _ => different_type_head equality
  · intro _ _ _ _ _ _ _ firstRead secondRead tailRead firstDet secondDet tailDet input' out rest' other equality
    cases other with
    | tuple otherFirst otherSecond otherTail =>
      obtain ⟨rfl, firstSuffix⟩ := firstDet _ _ _ otherFirst (List.cons.inj equality).2
      cases (List.cons.inj firstSuffix).2
      obtain ⟨rfl, rfl⟩ := secondDet _ _ _ otherSecond rfl
      obtain ⟨rfl, rfl⟩ := tailDet _ _ _ otherTail rfl
      exact ⟨rfl, rfl⟩
    | _ => different_type_head equality
  · intros
    exact textType_det (by assumption) (by assumption)
  · intros
    exact carrierIndex_det _ (by assumption) (by assumption) (by assumption)
  · intros
    exact carrierOption_det _ (by assumption) (by assumption) (by assumption)
  · intro rest space input' out rest' other equality
    cases other with
    | address otherSpace =>
      have operands := (List.cons.inj (List.cons.inj equality).2).2
      have nameEq := Token.word.inj (List.cons.inj operands).1
      cases LowLevel.AddressSpace.name_injective (String.toList_injective nameEq)
      exact ⟨rfl, (List.cons.inj (List.cons.inj operands).2).2⟩
    | integer => different_integer_head equality
    | interval => different_integer_head equality
    | _ => different_type_head equality
  · intro rest input' out rest' other equality
    cases other with
    | ownedRegion =>
      exact ⟨rfl, List.append_cancel_left (as := LowLevel.ownedRegionTokens) equality⟩
    | integer => different_integer_head equality
    | interval => different_integer_head equality
    | _ => different_type_head equality
  · intro rest input' out rest' other equality
    cases other with
    | close => exact ⟨rfl, (List.cons.inj equality).2⟩
    | comma _ _ => cases equality
  · intro _ _ _ _ _ headRead tailRead headDet tailDet input' out rest' other equality
    cases other with
    | close => cases equality
    | comma otherHead otherTail =>
      obtain ⟨rfl, rfl⟩ := headDet _ _ _ otherHead (List.cons.inj equality).2
      obtain ⟨rfl, rfl⟩ := tailDet _ _ _ otherTail rfl
      exact ⟨rfl, rfl⟩


-- Mirror ExprReads.consumes for the signed interval endpoints.
theorem TypeReads.consumes (read : TypeReads scope input a rest) : rest <:+ input := by
  have signed_suffix : ∀ {inp n out}, SignedReads inp n out → out <:+ inp := by
    intro inp n out r
    cases r with
    | positive => exact List.suffix_cons _ _
    | negative => exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
  refine TypeReads.rec
    (motive_1 := fun input _ rest _ => rest <:+ input)
    (motive_2 := fun input _ rest _ => rest <:+ input)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ read
  · intros; exact List.suffix_cons _ _
  · intros; exact List.suffix_cons _ _
  · intros
    rename_i loRead hiRead
    exact ((signed_suffix hiRead).trans
      ((List.suffix_cons _ _).trans (signed_suffix loRead))).trans
      ((List.suffix_cons _ _).trans (List.suffix_cons _ _))
  · intros
    rename_i _ boundRead elementSuffix
    exact ((List.suffix_cons _ _).trans (ExprReads.consumes boundRead)).trans
      (((List.suffix_cons _ _).trans elementSuffix).trans (List.suffix_cons _ _))
  · intros
    rename_i firstSuffix secondSuffix tailSuffix
    exact (tailSuffix.trans (secondSuffix.trans
      ((List.suffix_cons _ _).trans firstSuffix))).trans (List.suffix_cons _ _)
  · intros
    exact ((List.suffix_cons _ _).trans (List.suffix_cons _ _)).trans (List.suffix_cons _ _)
  · intros
    exact ((List.suffix_cons _ _).trans (List.suffix_cons _ _)).trans (List.suffix_cons _ _)
  · intros
    exact (((List.suffix_cons _ _).trans (List.suffix_cons _ _)).trans
      (List.suffix_cons _ _)).trans (List.suffix_cons _ _)
  · intro rest space; exact List.suffix_append space.tokens rest
  · intro rest; exact List.suffix_append LowLevel.ownedRegionTokens rest
  · intros; exact List.suffix_cons _ _
  · intros
    rename_i headSuffix tailSuffix
    exact (tailSuffix.trans headSuffix).trans (List.suffix_cons _ _)

-- Mirror Expr.printReads with the range suffix discriminator.
theorem WrittenType.printReads (tree : WrittenType) (valid : tree.valid scope)
    (closed : ∀ more, rest ≠ keyword "in" :: more) :
    TypeReads scope (tree.printPieces.map PrintedToken.value ++ rest) tree rest := by
  have signed_printReads : ∀ (number : Int) (tail : List Token),
      SignedReads ((signedPieces number).map PrintedToken.value ++ tail) number tail := by
    intro number tail
    unfold signedPieces
    by_cases hneg : number < 0
    · simp only [if_pos hneg, List.map_cons, List.map_nil]
      rw [Arith.print_value]
      let n := number.natAbs
      change SignedReads (minus :: .natural n :: tail) number tail
      have hnum : number = -(n : Int) := by
        have hnat : (n : Int) = -number := by dsimp [n]; exact Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
        omega
      rw [hnum]; exact SignedReads.negative (n := n) (rest := tail)
    · simp only [if_neg hneg, List.map_cons, List.map_nil]
      let n := number.natAbs
      change SignedReads (.natural n :: tail) number tail
      have hnum : number = (n : Int) := by dsimp [n]; exact Int.eq_natAbs_of_nonneg (by omega)
      rw [hnum]; exact SignedReads.positive (n := n) (rest := tail)
  have hpInt : ∀ (s : Bool) (w : Nat), (intTypeName s w).print.value = Token.word (intSpelling s w) := by
    intro s w; rfl
  have hpIn : printIn.value = keyword "in" := by rfl
  have hpRange : printClosedRange.value = closedRange := by rfl
  have hpOpen : printOpen.value = openParen := rfl
  have hpClose : printClose.value = closeParen := rfl
  have hpOpenBracket : printOpenBracket.value = openBracket := rfl
  have hpCloseBracket : printCloseBracket.value = closeBracket := rfl
  have hpSemicolon : printSemicolon.value = semicolon := rfl
  have hpComma : printComma.value = comma := rfl
  have hpNat (value : Nat) : (printInteger value).value = .natural value := rfl
  refine WrittenType.rec
    (motive_1 := fun tree => tree.valid scope →
      ∀ rest, (∀ more, rest ≠ keyword "in" :: more) →
        TypeReads scope (tree.printPieces.map PrintedToken.value ++ rest) tree rest)
    (motive_2 := fun trees => trees.valid scope → ∀ rest,
      TypeItemsTail scope (trees.printTail.map PrintedToken.value ++ closeParen :: rest) trees rest)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ tree valid rest closed
  · intro _ rest _
    have hp : printBoolType.value = keyword "bool" := by rfl
    simpa only [WrittenType.printPieces, hp, List.map_cons, List.map_nil, List.singleton_append] using
      (TypeReads.bool (rest := rest))
  · intro signed width interval valid rest closed
    cases interval with
    | none =>
        simpa only [WrittenType.printPieces, hpInt, List.map_cons, List.map_nil, List.singleton_append] using
          (TypeReads.integer (signed := signed) (width := width) valid closed)
    | some bounds =>
        have loRead := signed_printReads bounds.1 (closedRange :: (signedPieces bounds.2).map PrintedToken.value ++ rest)
        have hiRead := signed_printReads bounds.2 rest
        simpa only [WrittenType.printPieces, hpInt, hpIn, hpRange, List.map_append, List.map_cons, List.map_nil,
          List.singleton_append, List.append_assoc, List.cons_append, List.nil_append] using
          (TypeReads.interval (signed := signed) (width := width) valid loRead hiRead)

  · intro element count elementPrint valid rest _
    have boundRead : ExprReads [] 0 (.natural count :: closeBracket :: rest)
        (Expr.lit count) (closeBracket :: rest) :=
      .atom .lit (.stop noOperatorAtCloseBracket)
    have elementRead := elementPrint valid (semicolon :: .natural count :: closeBracket :: rest)
      (by intro more impossible; cases impossible)
    simpa only [WrittenType.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append, hpOpenBracket, hpCloseBracket, hpSemicolon, hpNat] using
      (TypeReads.array count (Expr.lit count) elementRead boundRead)
  · intro first second tail firstPrint secondPrint tailPrint valid rest _
    have tailRead := tailPrint valid.2.2 rest
    let afterSecond := tail.printTail.map PrintedToken.value ++ (closeParen :: rest)
    let secondInput := second.printPieces.map PrintedToken.value ++ afterSecond
    have secondRead := secondPrint valid.2.1 afterSecond
      (by
        intro more h
        cases tail <;> simp only [afterSecond, WrittenTypes.printTail, List.map_nil,
          List.nil_append, List.map_cons, List.cons_append, hpComma] at h <;> cases h)
    have firstRead := firstPrint valid.1 (comma :: secondInput)
      (by intro more impossible; cases impossible)
    simpa only [WrittenType.printPieces, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append, hpOpen, hpClose, hpComma, afterSecond, secondInput] using
      (TypeReads.tuple firstRead secondRead tailRead)
  · intro capacity _ rest _
    exact .text
  · intro carrier count valid rest _
    exact .index carrier valid
  · intro carrier count valid rest _
    exact .indexOption carrier valid
  · intro space _ rest _
    simpa only [WrittenType.printPieces, LowLevel.AddressSpace.printTokens, LowLevel.AddressSpace.tokens,
      List.cons_append, List.nil_append] using
      (TypeReads.address (rest := rest) space)
  · intro _ rest _
    exact .ownedRegion
  · intro _ rest
    exact .close
  · intro head tail headPrint tailPrint valid rest
    have tailRead := tailPrint valid.2 rest
    have headRead := headPrint valid.1
      (tail.printTail.map PrintedToken.value ++ closeParen :: rest)
      (by cases tail <;> intro more h <;> cases h)
    simpa only [WrittenTypes.printTail, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, hpComma] using (TypeItemsTail.comma headRead tailRead)

end Gabbro.Core.Ast
