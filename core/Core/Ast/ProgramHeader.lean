module

public import Core.Ast.Program.WrittenTypes

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def Parameter.printPieces (p : Parameter scope) : List PrintedToken :=
  [p.name.print, printColon] ++ p.written.printPieces

mutual
inductive ParamsRead (scope : Scope) : List Token → List (Parameter scope) → List Token → Prop where
  | empty : ParamsRead scope (closeParen :: rest) [] rest
  | first (p : Parameter scope) : TypeReads scope input p.written more → ParamsTail scope more ps rest →
      ParamsRead scope (.word p.name.val :: colon :: input) (p :: ps) rest

inductive ParamsTail (scope : Scope) : List Token → List (Parameter scope) → List Token → Prop where
  | close : ParamsTail scope (closeParen :: rest) [] rest
  | comma : ParamsRead scope input ps rest → ParamsTail scope (comma :: input) ps rest
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

-- Mirror BlockItems.deterministic, applying TypeReads.deterministic to each parameter.
theorem ParamsRead.deterministic (left : ParamsRead scope input a rest) (right : ParamsRead scope input b more) :
    a = b ∧ rest = more := by
  have param_eq : ∀ (p q : Parameter scope), p.name.val = q.name.val → p.written = q.written → p = q := by
    intro p q hname hwritten
    cases p with | mk n w v o =>
    cases q with | mk n' w' v' o' =>
    dsimp at hname hwritten
    have hn : n = n' := Subtype.ext hname
    subst n'; subst w'; rfl
  refine (ParamsRead.rec
    (motive_1 := fun input params rest _deriv => ∀ (input' : List Token) (b : List (Parameter scope)) (more : List Token),
      ParamsRead scope input' b more → input = input' → params = b ∧ rest = more)
    (motive_2 := fun input params rest _deriv => ∀ (input' : List Token) (b : List (Parameter scope)) (more : List Token),
      ParamsTail scope input' b more → input = input' → params = b ∧ rest = more)
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
theorem ParamsRead.consumes (read : ParamsRead scope input ps rest) : rest <:+ input := by
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
theorem ParamsRead.printReads (ps : List (Parameter scope)) :
    ParamsRead scope ((commaSeparated (ps.map Parameter.printPieces) ++ [printClose]).map PrintedToken.value ++ rest)
      ps rest := by
  have comma_cons : ∀ (p : Parameter scope) (ps : List (Parameter scope)),
      commaSeparated ((p :: ps).map Parameter.printPieces) =
        Parameter.printPieces p ++
          (match ps with | [] => [] | _ => [printComma] ++ commaSeparated (ps.map Parameter.printPieces)) := by
    intro p ps
    cases ps with
    | nil => simp only [commaSeparated, List.map_cons, List.map_nil, List.intersperse_nil, List.intersperse_singleton, List.flatten_nil, List.flatten_cons, List.append_nil]
    | cons q qs => simp only [commaSeparated, List.intersperse_cons_cons, List.flatten_cons, List.append_assoc, List.map_cons]
  have hClose : printClose.value = closeParen := by rfl
  have hComma : printComma.value = comma := by rfl
  induction ps with
  | nil =>
      simp only [commaSeparated, List.intersperse_nil, List.flatten_nil, List.map_nil, List.nil_append, hClose]
      exact ParamsRead.empty
  | cons p ps ih =>
      cases ps with
      | nil =>
          simp_all [commaSeparated, hClose]
          apply ParamsRead.first
          · change TypeReads scope (p.written.printPieces.map PrintedToken.value ++ closeParen :: rest) p.written (closeParen :: rest)
            exact p.written.printReads p.valid (rest := closeParen :: rest) (by intro more h; cases h)
          · exact ParamsTail.close
      | cons q qs =>
          rw [comma_cons]
          simp only [List.nil_append, List.map_append, List.append_assoc]
          apply ParamsRead.first
          · simpa [hClose, hComma, List.map_append, List.append_assoc] using
              (p.written.printReads p.valid
                (rest := comma :: ((commaSeparated ((q :: qs).map Parameter.printPieces) ++ [printClose]).map PrintedToken.value ++ rest))
                (by simp_all [hComma, comma, keyword]))
          · simpa [List.map_append, List.append_assoc, hClose] using (ParamsTail.comma ih)

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
  obtain ⟨ia, hia, aArgs⟩ := CallReads.inversion left; obtain ⟨ib, hib, bArgs⟩ := CallReads.inversion right
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
    | nil => simp only [commaSeparated, List.map_cons, List.map_nil, List.intersperse_nil, List.intersperse_singleton, List.flatten_nil, List.flatten_cons, List.append_nil]
    | cons f fs => simp only [commaSeparated, List.intersperse_cons_cons, List.flatten_cons, List.append_assoc, List.map_cons]
  have noComma : ∀ (more : List Token), ¬ Continues 0 (comma :: more) := by
    intro more h
    rcases h with ⟨op, tail, h, _⟩
    cases op with
    | arith a => cases a <;> cases h
    | div => cases h
    | compare c => cases c <;> cases h
    | logic l => cases l <;> cases h
    | index => cases h
    | projection => cases h
  have hComma : printComma.value = comma := by rfl
  have hpClose : printClose.value = closeParen := by rfl
  have argsRead : ArgsRead scope
      ((commaSeparated (call.args.map (fun exp => exp.2.printPieces)) ++ [printClose]).map PrintedToken.value ++ rest)
      call.args rest := by
    induction call.args with
    | nil =>
        simp only [commaSeparated, List.intersperse_nil, List.intersperse_singleton, List.flatten_nil, List.flatten_cons,
          List.map_nil, List.map_cons, List.nil_append, List.append_nil, List.singleton_append, hpClose]
        exact ArgsRead.empty
    | cons exp exps ih =>
        cases exps with
        | nil =>
            simp only [commaSeparated, List.intersperse_nil, List.intersperse_singleton, List.flatten_nil, List.flatten_cons,
              List.map_nil, List.map_cons, List.nil_append, List.append_nil, List.singleton_append, hpClose]
            apply ArgsRead.first
            · simpa only [Expr.printTokens, List.map_append, List.map_cons, List.map_nil, List.singleton_append,
                List.nil_append, List.append_assoc, hpClose] using
                (exp.2.printReads (minimum := 0) noOperatorAtClose)
            · exact ArgsTail.close
        | cons e es =>
            rw [comma_cons]
            apply ArgsRead.first
            · simpa only [Expr.printTokens, hComma, hpClose, List.map_append, List.map_cons, List.map_nil,
                List.singleton_append, List.append_assoc, List.cons_append, List.nil_append] using
                (exp.2.printReads
                  (rest := comma :: ((commaSeparated ((e :: es).map (fun exp => exp.2.printPieces)) ++ [printClose]).map PrintedToken.value ++ rest))
                  (noComma _))
            · simpa only [hpClose, List.map_append, List.map_cons, List.map_nil, List.singleton_append,
                List.append_assoc, List.nil_append] using (ArgsTail.comma ih)
  have hpName : call.name.print.value = Token.word call.name.val := by rfl
  have hpOpen : printOpen.value = openParen := by rfl
  simpa only [DirectCall.printPieces, hpName, hpOpen, hpClose, List.map_append, List.map_cons, List.map_nil,
    List.singleton_append, List.append_assoc, List.cons_append, List.nil_append] using (CallReads.applied call argsRead)

end Gabbro.Core.Ast
