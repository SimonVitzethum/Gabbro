module

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil2

@[expose] public section
namespace Gabbro.Grammatik.Parser

/-- The block opening is distinct from a parenthesized reason binder. -/
theorem strEq_brace_paren : strEq "{" "(" = false := by decide

/-- The handler reader accepts exactly the printer's optional binder and block. -/
theorem callElse_tail (reader : List Token → Except String (SAnw × List Token))
    (name : String) (args : List SExpr) (reason : String) (body : SAnw)
    (rest : List Token) (hk : BlockKopf body)
    (hb : reader (druckAnw body ++ .zeichen ";" :: rest) = .ok (body, .zeichen ";" :: rest)) :
    parseRufMitElse reader name args (.wort "else" ::
      ((if strEq reason "" then [] else [.zeichen "(", nameTok reason, .zeichen ")"]) ++
        (druckAnw body ++ .zeichen ";" :: rest))) =
      .ok (.callElse name args reason body, rest) := by
  by_cases h : strEq reason "" = true
  · have hr : reason = "" := (strEq_eq reason "").mp h
    subst hr
    obtain ⟨ts, hk⟩ := hk
    rw [hk] at hb ⊢
    simp only [List.cons_append] at hb
    simp only [parseRufMitElse, strEq_self, ↓reduceIte, List.nil_append, List.cons_append,
      strEq_brace_paren, Bool.false_eq_true, hb, bind, Except.bind, fordereZeichen, pure, Except.pure]
  · simp only [show strEq reason "" = false by simpa using h, Bool.false_eq_true, ↓reduceIte,
      List.cons_append, List.nil_append, parseRufMitElse,
      strEq_self, nimmName, nameText_nameTok, fordereZeichen, bind, Except.bind, hb, pure, Except.pure]

/-- Generic statement round trip, retaining either a named or discarded reason. -/
theorem anw_callElse (name : String) (args : List SExpr) (reason : String) (body : SAnw)
    (hn : NameGut name) (hw : istAnwWort name = false) (ha : gutListe args = true)
    (hb : BlockBein body) (hk : BlockKopf body) :
    AnwBein (.callElse name args reason body) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, rohToks_nameGut name hn, List.length_append, List.length_singleton,
    List.length_cons, List.length_nil] at hF
  obtain ⟨G, rfl⟩ : ∃ G, F = G + 4 := ⟨F - 4, by omega⟩
  let tail := .wort "else" ::
    ((if strEq reason "" then [] else [.zeichen "(", nameTok reason, .zeichen ")"]) ++
      (druckAnw body ++ .zeichen ";" :: rest))
  have hd : druckAnw (.callElse name args reason body) ++ rest = nameTok name :: .zeichen "(" ::
      (druckToksListe args ++ [.zeichen ")"] ++ tail) := by
    simp only [druckAnw, rohToks_nameGut name hn, tail, List.cons_append, List.nil_append, List.append_assoc]
  have ht : name ≠ "transition" := by intro e; subst e; revert hw; decide
  have placed : parsePlatzStmt (G + 3) (nameTok name :: .zeichen "(" ::
      (druckToksListe args ++ [.zeichen ")"] ++ tail)) = .ok (.callElse name args reason body, rest) := by
    rw [parsePlatzStmt_ident _ _ _ ht]
    have hA := argsM args tail G (args_gut args ha) (by omega)
    have hB := hb (.zeichen ";" :: rest) (G + 1) (by simp only [fbA]; omega)
    simp only [parseKopfStmt]
    rw [kopf_ruf_head, hA]
    change parseRufMitElse (parseBlock (G + 1)) name args tail = _
    exact callElse_tail (parseBlock (G + 1)) name args reason body rest hk hB
  rw [hd]
  exact parseStmt_ident (G + 3) name _ (by
    intro r e
    simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
    (Or.inr hw) placed

end Gabbro.Grammatik.Parser
