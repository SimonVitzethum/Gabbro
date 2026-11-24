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
  intro c same; obtain rfl : ':' = c := Option.some.inj (by simpa using same)
  exact ⟨by simp only [isSpace, List.mem_cons, List.not_mem_nil, Char.reduceEq, or_self, not_false_eq_true], by decide, by decide, by decide⟩)
def printComma : PrintedToken := printPunctuation "," (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by
  intro c same; obtain rfl : ',' = c := Option.some.inj (by simpa using same)
  exact ⟨by simp only [isSpace, List.mem_cons, List.not_mem_nil, Char.reduceEq, or_self, not_false_eq_true], by decide, by decide, by decide⟩)
def printArrow : PrintedToken := printPunctuation "->" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by
  intro c same; obtain rfl : '-' = c := Option.some.inj (by simpa using same)
  exact ⟨by simp only [isSpace, List.mem_cons, List.not_mem_nil, Char.reduceEq, or_self, not_false_eq_true], by decide, by decide, by decide⟩)
def printClosedRange : PrintedToken := printPunctuation ".." (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by
  intro c same; obtain rfl : '.' = c := Option.some.inj (by simpa using same)
  exact ⟨by simp only [isSpace, List.mem_cons, List.not_mem_nil, Char.reduceEq, or_self, not_false_eq_true], by decide, by decide, by decide⟩)
def printOpenRange : PrintedToken := printPunctuation "..<" (by
  simp only [punctuation, List.mem_cons, String.reduceEq, true_or, false_or]) (by
  intro c same; obtain rfl : '.' = c := Option.some.inj (by simpa using same)
  exact ⟨by simp only [isSpace, List.mem_cons, List.not_mem_nil, Char.reduceEq, or_self, not_false_eq_true], by decide, by decide, by decide⟩)

/-- The finite keywords used by these productions are unquoted words. -/
def printProgramWord (head : Char) (tail : List Char) (first : 'a' ≤ head ∧ head ≤ 'z')
    (rest : ∀ c ∈ tail, 'a' ≤ c ∧ c ≤ 'z') : PrintedToken :=
  (keywordName head tail first rest).print

-- Mirror returnName and the punctuationHead lemma for each new terminal.
def printConst : PrintedToken := printProgramWord 'c' ['o', 'n', 's', 't'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide)
def printFn : PrintedToken := printProgramWord 'f' ['n'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl <;> decide)
def printBoolType : PrintedToken := printProgramWord 'b' ['o', 'o', 'l'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide)
def printIn : PrintedToken := printProgramWord 'i' ['n'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl <;> decide)
def printMut : PrintedToken := printProgramWord 'm' ['u', 't'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide)
def printWhile : PrintedToken := printProgramWord 'w' ['h', 'i', 'l', 'e'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide)
def printBounded : PrintedToken := printProgramWord 'b' ['o', 'u', 'n', 'd', 'e', 'd'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
def printOps : PrintedToken := printProgramWord 'o' ['p', 's'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide)
def printFor : PrintedToken := printProgramWord 'f' ['o', 'r'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide)
def printDecreases : PrintedToken :=
  printProgramWord 'd' ['e', 'c', 'r', 'e', 'a', 's', 'e', 's'] (by decide) (by
    intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

-- Mirror Identifier.print with an underscore allowed in the tail.
def printOnExceeded : PrintedToken :=
  Identifier.print ⟨"on_exceeded".toList, 'o', "n_exceeded".toList, rfl, by
    exact .inl (.inl ⟨by decide, by decide⟩), by
    intro c member; simp at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact .inl (.inr rfl) | exact .inl (.inl (.inl ⟨by decide, by decide⟩))⟩

def intSpelling (signed : Bool) (width : Nat) : List Char :=
  (if signed then 'i' else 'u') :: (toString width).toList

-- Mirror printInteger.lexeme using the decimal digit tail of the width.
def intTypeName (signed : Bool) (width : Nat) : Identifier :=
  ⟨intSpelling signed width, (if signed then 'i' else 'u'), (toString width).toList, rfl, by
    cases signed <;> exact .inl (.inl ⟨by decide, by decide⟩), by
    intro c member
    right; change IsDecimalDigit c
    have member' : c ∈ Nat.toDigits 10 width := by simpa only [Nat.toString_eq_ofList_toDigits] using member
    have digit : c.isDigit := Nat.isDigit_of_mem_toDigits (n := width) (b := 10) (Nat.zero_lt_succ _) (Nat.le_refl _) (c := c) member'
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
  | positive => cases right with | positive => exact ⟨rfl, rfl⟩
  | negative => cases right with | negative => exact ⟨rfl, rfl⟩

-- Mirror ExprReads.deterministic, dispatch on the width spelling and then on in.
theorem TypeReads.deterministic (left : TypeReads input a rest) (right : TypeReads input b more) :
    a = b ∧ rest = more := by
  have not_bool : ∀ (s : Bool) (w : Nat), intSpelling s w ≠ "bool".toList := by
    intro s w h
    have hh := congrArg List.head? h
    have hc : (if s then 'i' else 'u') = 'b' := by simpa only [intSpelling, List.head?_cons] using hh
    cases s <;> cases hc
  have spelling_inj : ∀ {s w s' w'}, intSpelling s w = intSpelling s' w' → s = s' ∧ w = w' := by
    intro s w s' w' h
    have hh := congrArg List.head? h
    have ht := congrArg List.tail h
    have hc : (if s then 'i' else 'u') = (if s' then 'i' else 'u') := by
      simpa only [intSpelling, List.head?_cons] using hh
    have hs : s = s' := by
      cases s <;> cases s'
      · rfl
      · cases hc
      · cases hc
      · rfl
    cases hs
    have ht' : (toString w).toList = (toString w').toList := by simpa only [intSpelling, List.tail_cons] using ht
    have hdigits : Nat.toDigits 10 w = Nat.toDigits 10 w' := by simpa only [Nat.toString_eq_ofList_toDigits] using ht'
    have hv : w = w' := by
      have hv' := congrArg (fun l => Nat.ofDigitChars 10 l 0) hdigits
      simpa only [Nat.ofDigitChars_ten_toDigits] using hv'
    exact ⟨rfl, hv⟩
  refine (TypeReads.rec
    (motive := fun input tree rest _deriv => ∀ (input' : List Token) (b' : WrittenType) (more' : List Token),
      TypeReads input' b' more' → input = input' → tree = b' ∧ rest = more')
    ?_ ?_ ?_ left) input b more right rfl
  · intro rest input' b' more' rightDeriv hEq
    cases rightDeriv with
    | bool => injection hEq with hword htail; exact ⟨rfl, htail⟩
    | integer valid' closed' =>
        injection hEq with hword htail; injection hword with hspell
        exact (not_bool _ _ hspell.symm).elim
    | interval valid' loRead' hiRead' =>
        injection hEq with hword htail; injection hword with hspell
        exact (not_bool _ _ hspell.symm).elim
  · intro signed width rest valid closed input' b' more' rightDeriv hEq
    cases rightDeriv with
    | bool =>
        injection hEq with hword htail; injection hword with hspell
        exact (not_bool _ _ hspell).elim
    | integer valid' closed' =>
        injection hEq with hword htail; injection hword with hspell
        obtain ⟨hs, hw⟩ := spelling_inj hspell
        cases hs; cases hw; exact ⟨rfl, htail⟩
    | interval valid' loRead' hiRead' =>
        injection hEq with hword htail; injection hword with hspell
        exact (closed _ htail).elim
  · intro signed width lo hi input more rest valid loRead hiRead input' b' more' rightDeriv hEq
    cases rightDeriv with
    | bool =>
        injection hEq with hword htail; injection hword with hspell
        exact (not_bool _ _ hspell).elim
    | integer valid' closed' =>
        injection hEq with hword htail; injection hword with hspell
        exact (closed' _ htail.symm).elim
    | interval valid' loRead' hiRead' =>
        injection hEq with hword htail; injection hword with hspell
        obtain ⟨hs, hw⟩ := spelling_inj hspell
        cases hs; cases hw; cases htail
        obtain ⟨hlo, hmore⟩ := SignedReads.deterministic loRead loRead'
        cases hmore
        obtain ⟨hhi, hrest⟩ := SignedReads.deterministic hiRead hiRead'
        cases hlo; cases hhi; exact ⟨rfl, hrest⟩

-- Mirror ExprReads.consumes for the signed interval endpoints.
theorem TypeReads.consumes (read : TypeReads input a rest) : rest <:+ input := by
  have signed_suffix : ∀ {inp n out}, SignedReads inp n out → out <:+ inp := by
    intro inp n out r
    cases r with
    | positive => exact List.suffix_cons _ _
    | negative => exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
  refine TypeReads.rec (motive := fun input tree rest _deriv => rest <:+ input) ?_ ?_ ?_ read
  · intro rest; exact List.suffix_cons _ _
  · intro signed width rest valid closed; exact List.suffix_cons _ _
  · intro signed width lo hi input more rest valid loRead hiRead
    have hiS : rest <:+ more := signed_suffix hiRead
    have loS : closedRange :: more <:+ input := signed_suffix loRead
    have moreS : more <:+ input := (List.suffix_cons closedRange more).trans loS
    exact ((hiS.trans moreS).trans (List.suffix_cons (keyword "in") input)).trans
      (List.suffix_cons (Token.word (intSpelling signed width)) (keyword "in" :: input))

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
  have hpIn : printIn.value = keyword "in" := by rfl; have hpRange : printClosedRange.value = closedRange := by rfl
  cases tree with
  | bool =>
      have hp : printBoolType.value = keyword "bool" := by rfl
      simpa only [WrittenType.printPieces, hp, List.map_cons, List.map_nil, List.singleton_append] using
        (TypeReads.bool (rest := rest))
  | integer signed width interval =>
      cases interval with
      | none =>
          simpa only [WrittenType.printPieces, hpInt, List.map_cons, List.map_nil, List.singleton_append] using
            (TypeReads.integer (signed := signed) (width := width) valid closed)
      | some bounds =>
          have loRead := signed_printReads bounds.1 (closedRange :: (signedPieces bounds.2).map PrintedToken.value ++ rest)
          have hiRead := signed_printReads bounds.2 rest
          simpa only [WrittenType.printPieces, hpInt, hpIn, hpRange, List.map_append, List.map_cons, List.map_nil,
            List.singleton_append, List.append_assoc] using
            (TypeReads.interval (signed := signed) (width := width) valid loRead hiRead)

-- Mirror BlockItems.deterministic, applying TypeReads.deterministic to each parameter.
theorem ParamsRead.deterministic (left : ParamsRead input a rest) (right : ParamsRead input b more) :
    a = b ∧ rest = more := by
  have param_eq : ∀ (p q : Parameter), p.name.val = q.name.val → p.written = q.written → p = q := by
    intro p q hname hwritten
    cases p with | mk n w v o =>
    cases q with | mk n' w' v' o' =>
    dsimp at hname hwritten
    have hn : n = n' := Subtype.ext hname
    subst n'; subst w'; rfl
  refine (ParamsRead.rec
    (motive_1 := fun input params rest _deriv => ∀ (input' : List Token) (b : List Parameter) (more : List Token),
      ParamsRead input' b more → input = input' → params = b ∧ rest = more)
    (motive_2 := fun input params rest _deriv => ∀ (input' : List Token) (b : List Parameter) (more : List Token),
      ParamsTail input' b more → input = input' → params = b ∧ rest = more)
    ?_ ?_ ?_ ?_ left) input b more right rfl
  · intro rest input' b' more' rightDeriv hEq
    cases rightDeriv with
    | empty => injection hEq with hhead htail; exact ⟨rfl, htail⟩
    | first p t tail => cases hEq
  · intro inputL moreL psL restL p tRead tailRead tailIH input' b' more' rightDeriv hEq
    cases rightDeriv with
    | empty => cases hEq
    | first p' tRead' tailRead' =>
        injection hEq with hword hin; injection hword with hnv
        injection hin with hcolon hinL; cases hinL
        obtain ⟨sameWritten, sameMore⟩ := TypeReads.deterministic tRead tRead'
        cases sameMore
        have hp : p = p' := param_eq p p' hnv sameWritten
        cases hp
        obtain ⟨eqps, eqrest⟩ := tailIH _ _ _ tailRead' rfl
        cases eqps; exact ⟨rfl, eqrest⟩
  · intro rest input' b' more' rightDeriv hEq
    cases rightDeriv with
    | close => injection hEq with hhead htail; exact ⟨rfl, htail⟩
    | comma pr => cases hEq
  · intro inputL psL restL pr prIH input' b' more' rightDeriv hEq
    cases rightDeriv with
    | close => cases hEq
    | comma pr' => injection hEq with hcomma hin; exact prIH _ _ _ pr' hin

-- Mirror BlockItems.consumes, including the final close parenthesis.
theorem ParamsRead.consumes (read : ParamsRead input ps rest) : rest <:+ input := by
  refine ParamsRead.rec
    (motive_1 := fun input params rest _deriv => rest <:+ input)
    (motive_2 := fun input params rest _deriv => rest <:+ input)
    ?_ ?_ ?_ ?_ read
  · intro rest; exact List.suffix_cons _ _
  · intro inputL moreL psL restL p tRead tailRead tailIH
    exact ((tailIH.trans (TypeReads.consumes tRead)).trans (List.suffix_cons colon inputL)).trans
      (List.suffix_cons (Token.word p.name.val) (colon :: inputL))
  · intro rest; exact List.suffix_cons _ _
  · intro inputL psL restL pr prIH
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
    | nil => simp only [commaSeparated, List.intersperse_nil, List.intersperse_singleton, List.flatten_nil, List.flatten_cons]
    | cons q qs => simp only [commaSeparated, List.intersperse_cons_cons, List.flatten_cons, List.append_assoc, List.map_cons]
  have hClose : printClose.value = closeParen := by rfl; have hComma : printComma.value = comma := by rfl
  induction ps with
  | nil =>
      simp only [commaSeparated, List.intersperse_nil, List.flatten_nil, List.map_nil, List.nil_append, hClose]
      exact ParamsRead.empty
  | cons p ps ih =>
      cases ps with
      | nil =>
          simp only [commaSeparated, List.intersperse_nil, List.flatten_nil, List.map_nil, List.nil_append, hClose]
          apply ParamsRead.first
          · exact p.written.printReads p.valid (rest := ([printClose].map PrintedToken.value ++ rest))
              (by simp only [hClose, closeParen, keyword, Token.noConfusion])
          · exact ParamsTail.close
      | cons q qs =>
          rw [comma_cons]
          simp only [List.nil_append, List.map_append, List.append_assoc]
          apply ParamsRead.first
          · simpa only [hClose, hComma, List.map_append, List.map_cons, List.map_nil, List.singleton_append,
              List.append_assoc] using
              (p.written.printReads p.valid
                (rest := comma :: ((commaSeparated ((q :: qs).map Parameter.printPieces) ++ [printClose]).map PrintedToken.value ++ rest))
                (by simp only [hComma, comma, keyword, Token.noConfusion]))
          · simpa only [List.map_append, List.map_cons, List.map_nil, List.singleton_append, List.append_assoc,
              hClose] using (ParamsTail.comma ih)

-- Mirror BlockItems.deterministic and apply ExprReads.deterministic at each argument.
theorem ArgsRead.deterministic (left : ArgsRead scope input a rest) (right : ArgsRead scope input b more) :
    a = b ∧ rest = more := by
  refine (ArgsRead.rec
    (motive_1 := fun input args rest _deriv => ∀ (b : List (TypedExpr scope)) (more : List Token),
      ArgsRead scope input b more → args = b ∧ rest = more)
    (motive_2 := fun input args rest _deriv => ∀ (b : List (TypedExpr scope)) (more : List Token),
      ArgsTail scope input b more → args = b ∧ rest = more)
    ?_ ?_ ?_ ?_ left) b more right
  · intro rest b' more' rightDeriv
    cases rightDeriv with
    | empty => exact ⟨rfl, rfl⟩
    | first e tail => cases e with | atom a t => cases a
  · intro inputL typeL exprL restL esL restL2 eProof tailProof tailIH b' more' rightDeriv
    cases rightDeriv with
    | empty => cases eProof with | atom atom tail => cases atom
    | first eProof' tailProof' =>
        obtain ⟨same, rfl⟩ := ExprReads.deterministic eProof eProof'
        cases same
        obtain ⟨eq, rfl⟩ := tailIH _ _ tailProof'
        cases eq; exact ⟨rfl, rfl⟩
  · intro rest b' more' rightDeriv
    cases rightDeriv with | close => exact ⟨rfl, rfl⟩
  · intro inputL esL restL pr prIH b' more' rightDeriv
    cases rightDeriv with | comma pr' => exact prIH _ _ pr'

-- Mirror BlockItems.consumes and compose expression suffixes.
theorem ArgsRead.consumes (read : ArgsRead scope input args rest) : rest <:+ input := by
  refine ArgsRead.rec
    (motive_1 := fun input args rest _deriv => rest <:+ input)
    (motive_2 := fun input args rest _deriv => rest <:+ input)
    ?_ ?_ ?_ ?_ read
  · intro rest; exact List.suffix_cons _ _
  · intro inputL typeL exprL restL esL restL2 eProof tailProof tailIH
    exact tailIH.trans (ExprReads.consumes eProof)
  · intro rest; exact List.suffix_cons _ _
  · intro inputL esL restL pr prIH
    exact prIH.trans (List.suffix_cons comma inputL)

-- Mirror StmtReads.assign_inversion for the written name and parenthesized argument suffix.
theorem CallReads.inversion (read : CallReads scope input call rest) :
    ∃ args, input = .word call.name.val :: openParen :: args ∧ ArgsRead scope args call.args rest := by
  cases read with | applied call argsRead => exact ⟨_, rfl, argsRead⟩

-- Mirror StmtReads.deterministic and use ArgsRead.deterministic.
theorem CallReads.deterministic (left : CallReads scope input a rest) (right : CallReads scope input b more) :
    a = b ∧ rest = more := by
  have call_eq : ∀ (a b : DirectCall scope), a.name.val = b.name.val → a.args = b.args → a = b := by
    intro a b hname hargs
    cases a with | mk n o as =>
    cases b with | mk n' o' as' =>
    dsimp at hname hargs
    have hn : n = n' := Subtype.ext hname
    subst n'; subst as'; rfl
  obtain ⟨ia, hia, aArgs⟩ := CallReads.inversion left
  obtain ⟨ib, hib, bArgs⟩ := CallReads.inversion right
  rw [hia] at hib
  injection hib with hword hin; injection hword with hname; cases hin
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
    | nil => simp only [commaSeparated, List.intersperse_nil, List.intersperse_singleton, List.flatten_nil, List.flatten_cons]
    | cons f fs => simp only [commaSeparated, List.intersperse_cons_cons, List.flatten_cons, List.append_assoc, List.map_cons]
  have noComma : ∀ (more : List Token), ¬ Continues 0 (comma :: more) := by
    intro more h
    rcases h with ⟨op, tail, h, _⟩
    cases op with
    | arith a => cases a <;> cases h
    | div => cases h
    | compare c => cases c <;> cases h
    | logic l => cases l <;> cases h
  have hComma : printComma.value = comma := by rfl; have hpClose : printClose.value = closeParen := by rfl
  have argsRead : ArgsRead scope
      ((commaSeparated (call.args.map (fun exp => exp.2.printPieces)) ++ [printClose]).map PrintedToken.value ++ rest)
      call.args rest := by
    induction call.args with
    | nil =>
        simp only [commaSeparated, List.intersperse_nil, List.flatten_nil, List.map_nil, List.nil_append, hpClose]
        exact ArgsRead.empty
    | cons exp exps ih =>
        cases exps with
        | nil =>
            simp only [commaSeparated, List.intersperse_nil, List.flatten_nil, List.map_nil, List.nil_append, hpClose]
            apply ArgsRead.first
            · exact exp.2.printReads noOperatorAtClose
            · exact ArgsTail.close
        | cons e es =>
            rw [comma_cons]
            apply ArgsRead.first
            · simpa only [Expr.printTokens, hComma, hpClose, List.map_append, List.map_cons, List.map_nil,
                List.singleton_append, List.append_assoc] using
                (exp.2.printReads
                  (rest := comma :: ((commaSeparated ((e :: es).map (fun exp => exp.2.printPieces)) ++ [printClose]).map PrintedToken.value ++ rest))
                  (noComma _))
            · simpa only [hpClose, List.map_append, List.map_cons, List.map_nil, List.singleton_append,
                List.append_assoc] using (ArgsTail.comma ih)
  have hpName : call.name.print.value = Token.word call.name.val := by rfl; have hpOpen : printOpen.value = openParen := by rfl
  simpa only [DirectCall.printPieces, hpName, hpOpen, hpClose, List.map_append, List.map_cons, List.map_nil,
    List.singleton_append, List.append_assoc] using (CallReads.applied call argsRead)

end Gabbro.Core.Ast
