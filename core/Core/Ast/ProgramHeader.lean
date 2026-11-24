module

public import Core.Ast.Print

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def colon : Token := .punctuation ":".toList
def comma : Token := .punctuation ",".toList
def arrow : Token := .punctuation "->".toList
def closedRange : Token := .punctuation "..".toList
def openRange : Token := .punctuation "..<".toList

def keyword (word : String) : Token := .word word.toList

def printColon : PrintedToken := printPunctuation ":" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by
  intro c same
  obtain rfl : ':' = c := Option.some.inj (by simpa using same)
  exact ⟨by simp [isSpace], by decide, by decide, by decide⟩)
def printComma : PrintedToken := printPunctuation "," (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by
  intro c same
  obtain rfl : ',' = c := Option.some.inj (by simpa using same)
  exact ⟨by simp [isSpace], by decide, by decide, by decide⟩)
def printArrow : PrintedToken := printPunctuation "->" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by
  intro c same
  obtain rfl : '-' = c := Option.some.inj (by simpa using same)
  exact ⟨by simp [isSpace], by decide, by decide, by decide⟩)
def printClosedRange : PrintedToken := printPunctuation ".." (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by
  intro c same
  obtain rfl : '.' = c := Option.some.inj (by simpa using same)
  exact ⟨by simp [isSpace], by decide, by decide, by decide⟩)
def printOpenRange : PrintedToken := printPunctuation "..<" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by
  intro c same
  obtain rfl : '.' = c := Option.some.inj (by simpa using same)
  exact ⟨by simp [isSpace], by decide, by decide, by decide⟩)

/-- The finite keywords used by these productions are unquoted words. -/
def printProgramWord (head : Char) (tail : List Char) (first : 'a' ≤ head ∧ head ≤ 'z')
    (rest : ∀ c ∈ tail, 'a' ≤ c ∧ c ≤ 'z') : PrintedToken :=
  (keywordName head tail first rest).print

-- Mirror returnName and the punctuationHead lemma for each new terminal.
def printConst : PrintedToken := printProgramWord 'c' ['o', 'n', 's', 't'] (by decide) (by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide)
def printFn : PrintedToken := printProgramWord 'f' ['n'] (by decide) (by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl <;> decide)
def printBoolType : PrintedToken := printProgramWord 'b' ['o', 'o', 'l'] (by decide) (by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide)
def printIn : PrintedToken := printProgramWord 'i' ['n'] (by decide) (by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl <;> decide)
def printMut : PrintedToken := printProgramWord 'm' ['u', 't'] (by decide) (by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide)
def printWhile : PrintedToken := printProgramWord 'w' ['h', 'i', 'l', 'e'] (by decide) (by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide)
def printBounded : PrintedToken := printProgramWord 'b' ['o', 'u', 'n', 'd', 'e', 'd'] (by decide) (by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
def printOps : PrintedToken := printProgramWord 'o' ['p', 's'] (by decide) (by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide)
def printFor : PrintedToken := printProgramWord 'f' ['o', 'r'] (by decide) (by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide)
def printDecreases : PrintedToken :=
  printProgramWord 'd' ['e', 'c', 'r', 'e', 'a', 's', 'e', 's'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

-- Mirror Identifier.print with an underscore allowed in the tail.
def printOnExceeded : PrintedToken :=
  Identifier.print ⟨"on_exceeded".toList, 'o', "n_exceeded".toList, rfl, by
    exact .inl (.inl ⟨by decide, by decide⟩), by
    intro c member
    simp at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide⟩

def intSpelling (signed : Bool) (width : Nat) : List Char :=
  (if signed then 'i' else 'u') :: (toString width).toList

-- Mirror printInteger.lexeme using the decimal digit tail of the width.
def intTypeName (signed : Bool) (width : Nat) : Identifier :=
  ⟨intSpelling signed width, (if signed then 'i' else 'u'), (toString width).toList, rfl, by
    cases signed <;> exact .inl (.inl ⟨by decide, by decide⟩), by
    intro c member
    right
    change IsDecimalDigit c
    have member' : c ∈ Nat.toDigits 10 width := by
      simpa [Nat.toString_eq_ofList_toDigits] using member
    have digit : c.isDigit :=
      Nat.isDigit_of_mem_toDigits (n := width) (b := 10) (Nat.zero_lt_succ _) (Nat.le_refl _) (c := c) member'
    simpa only [IsDecimalDigit, Char.le_def, Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] using digit⟩

def signedPieces (number : Int) : List PrintedToken :=
  if number < 0 then [Arith.sub.print, printInteger number.natAbs] else [printInteger number.natAbs]

def WrittenType.printPieces : WrittenType → List PrintedToken
  | .bool => [printBoolType]
  | .integer signed width none => [(intTypeName signed width).print]
  | .integer signed width (some (lo, hi)) =>
    [(intTypeName signed width).print, printIn] ++ signedPieces lo ++ [printClosedRange] ++ signedPieces hi

inductive SignedReads : List Token → Int → List Token → Prop where
  | positive : SignedReads (.natural n :: rest) n rest
  | negative : SignedReads (minus :: .natural n :: rest) (-(n : Int)) rest

inductive TypeReads : List Token → WrittenType → List Token → Prop where
  | bool : TypeReads (keyword "bool" :: rest) .bool rest
  | integer (valid : (WrittenType.integer signed width none).valid)
      (closed : ∀ more, rest ≠ keyword "in" :: more) :
      TypeReads (.word (intSpelling signed width) :: rest) (.integer signed width none) rest
  | interval (valid : (WrittenType.integer signed width (some (lo, hi))).valid) :
      SignedReads input lo (closedRange :: more) → SignedReads more hi rest →
      TypeReads (.word (intSpelling signed width) :: keyword "in" :: input)
        (.integer signed width (some (lo, hi))) rest

def Parameter.printPieces (p : Parameter) : List PrintedToken :=
  [p.name.print, printColon] ++ p.written.printPieces

mutual
inductive ParamsRead : List Token → List Parameter → List Token → Prop where
  | empty : ParamsRead (closeParen :: rest) [] rest
  | first (p : Parameter) : TypeReads input p.written more → ParamsTail more ps rest →
      ParamsRead (.word p.name.val :: colon :: input) (p :: ps) rest

inductive ParamsTail : List Token → List Parameter → List Token → Prop where
  | close : ParamsTail (closeParen :: rest) [] rest
  | comma : ParamsRead input ps rest → ParamsTail (comma :: input) ps rest
end

mutual
inductive ArgsRead (scope : Scope) : List Token → List (TypedExpr scope) → List Token → Prop where
  | empty : ArgsRead scope (closeParen :: rest) [] rest
  | first : ExprReads scope 0 input e more → ArgsTail scope more es rest →
      ArgsRead scope input (e.typed :: es) rest

inductive ArgsTail (scope : Scope) : List Token → List (TypedExpr scope) → List Token → Prop where
  | close : ArgsTail scope (closeParen :: rest) [] rest
  | comma : ArgsRead scope input es rest → ArgsTail scope (comma :: input) es rest
end

def commaSeparated (pieces : List (List PrintedToken)) : List PrintedToken :=
  (pieces.intersperse [printComma]).flatten

def DirectCall.printPieces (call : DirectCall scope) : List PrintedToken :=
  [call.name.print, printOpen] ++ commaSeparated (call.args.map (fun exp => exp.2.printPieces)) ++ [printClose]

inductive CallReads (scope : Scope) : List Token → DirectCall scope → List Token → Prop where
  | applied (call : DirectCall scope) : ArgsRead scope input call.args rest →
      CallReads scope (.word call.name.val :: openParen :: input) call rest

-- Mirror AtomReads.lit_inversion and exclude the signed arm by token kind.
theorem SignedReads.deterministic (left : SignedReads input a rest) (right : SignedReads input b more) :
    a = b ∧ rest = more := by
  cases left with
  | positive =>
      cases right with
      | positive => exact ⟨rfl, rfl⟩
  | negative =>
      cases right with
      | negative => exact ⟨rfl, rfl⟩

-- Mirror ExprReads.deterministic, dispatch on the width spelling and then on in.
theorem TypeReads.deterministic (left : TypeReads input a rest) (right : TypeReads input b more) :
    a = b ∧ rest = more := by
  have not_bool : ∀ (s : Bool) (w : Nat), intSpelling s w ≠ "bool".toList := by
    intro s w h
    cases s <;> simp [intSpelling] at h
  have spelling_inj : ∀ {s w s' w'}, intSpelling s w = intSpelling s' w' → s = s' ∧ w = w' := by
    intro s w s' w' h
    cases s <;> cases s' <;> simp [intSpelling] at h
    all_goals
      have hdigits : Nat.toDigits 10 w = Nat.toDigits 10 w' := by
        simpa [Nat.toString_eq_ofList_toDigits] using h
      have hv : w = w' := by
        have hv' := congrArg (fun l => Nat.ofDigitChars 10 l 0) hdigits
        simpa [Nat.ofDigitChars_ten_toDigits] using hv'
      exact ⟨rfl, hv⟩
  refine (TypeReads.rec
    (motive := fun input tree rest _deriv => ∀ (input' : List Token) (b : WrittenType) (more : List Token),
      TypeReads input' b more → input = input' → tree = b ∧ rest = more)
    ?_ ?_ ?_ left) input b more right rfl
  · intro input' b more right hEq
    cases right with
    | bool => exact ⟨rfl, rfl⟩
    | integer valid' closed' =>
        injection hEq with hword htail
        injection hword with hspell
        exact (not_bool _ _ hspell.symm).elim
    | interval valid' loRead' hiRead' =>
        injection hEq with hword htail
        injection hword with hspell
        exact (not_bool _ _ hspell.symm).elim
  · intro valid closed input' b more right hEq
    cases right with
    | bool =>
        injection hEq with hword htail
        injection hword with hspell
        exact (not_bool _ _ hspell).elim
    | integer valid' closed' =>
        injection hEq with hword htail
        injection hword with hspell
        obtain ⟨hs, hw⟩ := spelling_inj hspell
        subst s'
        subst w'
        exact ⟨rfl, htail⟩
    | interval valid' loRead' hiRead' =>
        injection hEq with hword htail
        injection hword with hspell
        have bad := closed' _ htail.symm
        exact bad.elim
  · intro valid loRead hiRead input' b more right hEq
    cases right with
    | bool =>
        injection hEq with hword htail
        injection hword with hspell
        exact (not_bool _ _ hspell).elim
    | integer valid' closed' =>
        injection hEq with hword htail
        injection hword with hspell
        exact (closed' _ htail.symm).elim
    | interval valid' loRead' hiRead' =>
        injection hEq with hword htail
        injection hword with hspell
        injection htail with htailIn
        obtain ⟨hs, hw⟩ := spelling_inj hspell
        subst s'
        subst w'
        cases htailIn
        obtain ⟨hlo, hmore⟩ := SignedReads.deterministic loRead loRead'
        injection hmore with hmoreIn
        cases hmoreIn
        obtain ⟨hhi, hrest⟩ := SignedReads.deterministic hiRead hiRead'
        subst lo'
        subst hi'
        exact ⟨rfl, hrest⟩

-- Mirror ExprReads.consumes for the signed interval endpoints.
theorem TypeReads.consumes (read : TypeReads input a rest) : rest <:+ input := by
  have signed_suffix : ∀ {inp n out}, SignedReads inp n out → out <:+ inp := by
    intro inp n out r
    cases r with
    | positive => exact List.suffix_cons _ _
    | negative => exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
  cases read with
  | bool => exact List.suffix_cons _ _
  | integer valid closed => exact List.suffix_cons _ _
  | interval valid loRead hiRead =>
      have hiS : rest <:+ _ := signed_suffix hiRead
      have loS : _ <:+ _ := signed_suffix loRead
      have moreS : _ <:+ _ := (List.suffix_cons closedRange _).trans loS
      exact ((hiS.trans moreS).trans (List.suffix_cons (keyword "in") _)).trans
        (List.suffix_cons (Token.word (intSpelling signed width)) _)

-- Mirror Expr.printReads with the range suffix discriminator.
theorem WrittenType.printReads (tree : WrittenType) (valid : tree.valid)
    (closed : ∀ more, rest ≠ keyword "in" :: more) :
    TypeReads (tree.printPieces.map PrintedToken.value ++ rest) tree rest := by
  have signed_printReads : ∀ (number : Int) (tail : List Token),
      SignedReads ((signedPieces number).map PrintedToken.value ++ tail) number tail := by
    intro number tail
    unfold signedPieces
    by_cases hneg : number < 0
    · simp only [if_pos hneg, List.map_cons, List.map_nil]
      rw [Arith.print_value]
      change SignedReads (minus :: .natural number.natAbs :: tail) number tail
      have hnum : number = -(number.natAbs : Int) := by
        have hnat : (number.natAbs : Int) = -number := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
        omega
      rw [hnum]
      exact SignedReads.negative
    · simp only [if_neg hneg, List.map_cons, List.map_nil]
      change SignedReads (.natural number.natAbs :: tail) number tail
      have hnum : number = (number.natAbs : Int) := Int.eq_natAbs_of_nonneg (by omega)
      rw [hnum]
      exact SignedReads.positive
  cases tree with
  | bool =>
      simpa [WrittenType.printPieces, printBoolType, printProgramWord, keywordName, Identifier.print] using
        (TypeReads.bool (rest := rest))
  | integer signed width none =>
      simpa [WrittenType.printPieces, intTypeName, intSpelling, Identifier.print] using
        (TypeReads.integer valid closed)
  | integer signed width (some (lo, hi)) =>
      have loRead := signed_printReads lo (closedRange :: (signedPieces hi).map PrintedToken.value ++ rest)
      have hiRead := signed_printReads hi rest
      simpa [WrittenType.printPieces, intTypeName, intSpelling, Identifier.print, printIn, printClosedRange,
        keywordName, printProgramWord, List.map_append, List.append_assoc] using
        (TypeReads.interval valid loRead hiRead)

-- Mirror BlockItems.deterministic, applying TypeReads.deterministic to each parameter.
theorem ParamsRead.deterministic (left : ParamsRead input a rest) (right : ParamsRead input b more) :
    a = b ∧ rest = more := by
  have param_eq : ∀ (p q : Parameter), p.name.val = q.name.val → p.written = q.written → p = q := by
    intro p q hname hwritten
    cases p with | mk n w v o =>
    cases q with | mk n' w' v' o' =>
    dsimp at hname hwritten
    have hn : n = n' := Subtype.ext hname
    subst n'
    subst w'
    rfl
  refine (ParamsRead.rec
    (motive_1 := fun input params rest _deriv => ∀ (input' : List Token) (b : List Parameter) (more : List Token),
      ParamsRead input' b more → input = input' → params = b ∧ rest = more)
    (motive_2 := fun input params rest _deriv => ∀ (input' : List Token) (b : List Parameter) (more : List Token),
      ParamsTail input' b more → input = input' → params = b ∧ rest = more)
    ?_ ?_ ?_ ?_ left) input b more right rfl
  · intro rest right hEq
    cases right with
    | empty => exact ⟨rfl, rfl⟩
    | first p t tail => cases hEq
  · intro p inputL moreL rest ps tRead tailRead tailIH right hEq
    cases right with
    | first p' tRead' tailRead' =>
        injection hEq with hword hin
        injection hword with hnv
        injection hin with hcolon hinL
        cases hinL
        obtain ⟨sameWritten, sameMore⟩ := TypeReads.deterministic tRead tRead'
        cases sameMore
        have hp : p = p' := param_eq p p' hnv.symm sameWritten
        subst p'
        obtain ⟨eqps, eqrest⟩ := tailIH inputL ps' more tailRead' rfl
        subst ps'
        exact ⟨rfl, eqrest⟩
  · intro rest right hEq
    cases right with
    | close => exact ⟨rfl, rfl⟩
    | comma pr => cases hEq
  · intro inputL ps rest pr prIH right hEq
    cases right with
    | comma pr' =>
        injection hEq with hin
        cases hin
        exact prIH inputL ps' rest' pr' rfl

-- Mirror BlockItems.consumes, including the final close parenthesis.
theorem ParamsRead.consumes (read : ParamsRead input ps rest) : rest <:+ input := by
  refine ParamsRead.rec
    (motive_1 := fun input params rest _deriv => rest <:+ input)
    (motive_2 := fun input params rest _deriv => rest <:+ input)
    ?_ ?_ ?_ ?_ read
  · intro rest
    exact List.suffix_cons _ _
  · intro p inputL moreL rest ps tRead tailRead tailIH
    exact tailIH.trans (TypeReads.consumes tRead)
  · intro rest
    exact List.suffix_cons _ _
  · intro inputL ps rest pr prIH
    exact prIH.trans (List.suffix_cons comma inputL)

-- Mirror Block.printItems_reads with commas between the ordered parameters.
theorem ParamsRead.printReads (ps : List Parameter) :
    ParamsRead ((commaSeparated (ps.map Parameter.printPieces) ++ [printClose]).map PrintedToken.value ++ rest)
      ps rest := by
  have comma_cons : ∀ (p : Parameter) (ps : List Parameter),
      commaSeparated ((p :: ps).map Parameter.printPieces) =
        Parameter.printPieces p ++
          (match ps with | [] => [] | _ => [printComma] ++ commaSeparated (ps.map Parameter.printPieces)) := by
    intro p ps
    cases ps with
    | nil => simp [commaSeparated]
    | cons q qs => simp [commaSeparated, List.append_assoc]
  induction ps with
  | nil =>
      simp [commaSeparated]
      exact ParamsRead.empty
  | cons p ps ih =>
      cases ps with
      | nil =>
          simp [commaSeparated]
          apply ParamsRead.first
          · exact p.written.printReads p.valid (by intro more h; cases h)
          · exact ParamsTail.close
      | cons q qs =>
          rw [comma_cons]
          apply ParamsRead.first
          · exact p.written.printReads p.valid (by intro more h; cases h)
          · exact ParamsTail.comma ih

-- Mirror BlockItems.deterministic and apply ExprReads.deterministic at each argument.
theorem ArgsRead.deterministic (left : ArgsRead scope input a rest) (right : ArgsRead scope input b more) :
    a = b ∧ rest = more := by
  refine (ArgsRead.rec
    (motive_1 := fun input args rest _deriv => ∀ (b : List (TypedExpr scope)) (more : List Token),
      ArgsRead scope input b more → args = b ∧ rest = more)
    (motive_2 := fun input args rest _deriv => ∀ (b : List (TypedExpr scope)) (more : List Token),
      ArgsTail scope input b more → args = b ∧ rest = more)
    ?_ ?_ ?_ ?_ left) b more right
  · intro rest b more right
    cases right with
    | empty => exact ⟨rfl, rfl⟩
    | first e tail => cases e with | atom a _ => cases a
  · intro e moreL es rest tailRead tailIH b more right
    cases right with
    | first e' tailRead' =>
        obtain ⟨same, rfl⟩ := ExprReads.deterministic e e'
        cases same
        obtain ⟨eq, rfl⟩ := tailIH es' more tailRead'
        cases eq
        exact ⟨rfl, rfl⟩
  · intro rest b more right
    cases right with
    | close => exact ⟨rfl, rfl⟩
    | comma pr => cases pr
  · intro inputL es rest pr prIH b more right
    cases right with
    | comma pr' => exact prIH es' more' pr'

-- Mirror BlockItems.consumes and compose expression suffixes.
theorem ArgsRead.consumes (read : ArgsRead scope input args rest) : rest <:+ input := by
  refine ArgsRead.rec
    (motive_1 := fun input args rest _deriv => rest <:+ input)
    (motive_2 := fun input args rest _deriv => rest <:+ input)
    ?_ ?_ ?_ ?_ read
  · intro rest
    exact List.suffix_cons _ _
  · intro e moreL es rest tailRead tailIH
    exact tailIH.trans (ExprReads.consumes e)
  · intro rest
    exact List.suffix_cons _ _
  · intro inputL es rest pr prIH
    exact prIH.trans (List.suffix_cons comma inputL)

-- Mirror StmtReads.assign_inversion for the written name and parenthesized argument suffix.
theorem CallReads.inversion (read : CallReads scope input call rest) :
    ∃ args, input = .word call.name.val :: openParen :: args ∧ ArgsRead scope args call.args rest := by
  cases read with
  | applied call argsRead =>
      exact ⟨_, rfl, argsRead⟩

-- Mirror StmtReads.deterministic and use ArgsRead.deterministic.
theorem CallReads.deterministic (left : CallReads scope input a rest) (right : CallReads scope input b more) :
    a = b ∧ rest = more := by
  have call_eq : ∀ (a b : DirectCall scope), a.name.val = b.name.val → a.args = b.args → a = b := by
    intro a b hname hargs
    cases a with | mk n o as =>
    cases b with | mk n' o' as' =>
    dsimp at hname hargs
    have hn : n = n' := Subtype.ext hname
    subst n'
    subst as'
    rfl
  obtain ⟨ia, hia, aArgs⟩ := CallReads.inversion left
  obtain ⟨ib, hib, bArgs⟩ := CallReads.inversion right
  rw [hia] at hib
  injection hib with hword hin
  injection hword with hname
  cases hin
  obtain ⟨typedEq, suffixEq⟩ := ArgsRead.deterministic aArgs bArgs
  exact ⟨call_eq a b hname typedEq, suffixEq⟩

-- Mirror StmtReads.consumes using ArgsRead.consumes.
theorem CallReads.consumes (read : CallReads scope input call rest) : rest <:+ input := by
  obtain ⟨args, rfl, aRead⟩ := CallReads.inversion read
  exact ((ArgsRead.consumes aRead).trans (List.suffix_cons openParen args)).trans
    (List.suffix_cons (.word call.name.val) (openParen :: args))

-- Mirror BracedBlock.printReads using Expr.printReads before close parentheses or commas.
theorem DirectCall.printReads (call : DirectCall scope) :
    CallReads scope (call.printPieces.map PrintedToken.value ++ rest) call rest := by
  have comma_cons : ∀ (e : TypedExpr scope) (es : List (TypedExpr scope)),
      commaSeparated ((e :: es).map (fun exp => exp.2.printPieces)) =
        e.2.printPieces ++
          (match es with | [] => [] | _ => [printComma] ++ commaSeparated (es.map (fun exp => exp.2.printPieces))) := by
    intro e es
    cases es with
    | nil => simp [commaSeparated]
    | cons f fs => simp [commaSeparated, List.append_assoc]
  have noComma : ∀ (more : List Token), ¬ Continues 0 (comma :: more) := by
    intro more h
    rcases h with ⟨op, tail, h, _⟩
    cases op with
    | arith a => cases a <;> cases h
    | div => cases h
    | compare c => cases c <;> cases h
    | logic l => cases l <;> cases h
  have argsRead : ArgsRead scope
      ((commaSeparated (call.args.map (fun exp => exp.2.printPieces)) ++ [printClose]).map PrintedToken.value ++ rest)
      call.args rest := by
    induction call.args with
    | nil =>
        simp [commaSeparated]
        exact ArgsRead.empty
    | cons exp exps ih =>
        cases exps with
        | nil =>
            simp [commaSeparated]
            apply ArgsRead.first
            · exact exp.2.printReads noOperatorAtClose
            · exact ArgsTail.close
        | cons e es =>
            rw [comma_cons]
            apply ArgsRead.first
            · exact exp.2.printReads (by intro h; exact noComma _ h)
            · exact ArgsTail.comma ih
  simpa [DirectCall.printPieces, List.map_append, List.append_assoc] using (CallReads.applied call argsRead)

end Gabbro.Core.Ast
