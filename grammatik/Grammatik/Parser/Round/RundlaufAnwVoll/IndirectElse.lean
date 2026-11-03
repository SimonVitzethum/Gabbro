module

public import Grammatik.Parser.Round.RundlaufAnwVoll.CallElse

@[expose] public section
namespace Gabbro.Grammatik.Parser

/-- The expression form uses exactly the direct form's optional reason reader. -/
theorem indCallElse_tail (reader : List Token → Except String (SAnw × List Token))
    (pointer : SExpr) (args : List SExpr) (reason : String) (body : SAnw)
    (rest : List Token) (hk : BlockKopf body)
    (hb : reader (druckAnw body ++ .zeichen ";" :: rest) = .ok (body, .zeichen ";" :: rest)) :
    parseIndRufMitElse reader pointer args (.wort "else" ::
      ((if strEq reason "" then [] else [.zeichen "(", nameTok reason, .zeichen ")"]) ++
        (druckAnw body ++ .zeichen ";" :: rest))) =
      .ok (.callIndElse pointer args reason body, rest) := by
  rw [parseIndRufMitElse, callElse_tail reader (druck pointer) args reason body rest hk hb]
  rfl

/-- Every printable pointer expression and argument list round trips with its
    handler; the parser never converts the pointer expression into source text. -/
theorem anw_callIndElse (pointer : SExpr) (args : List SExpr) (reason : String) (body : SAnw)
    (hp : gut pointer = true) (ha : gutListe args = true)
    (hb : BlockBein body) (hk : BlockKopf body) :
    AnwBein (.callIndElse pointer args reason body) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨G, rfl⟩ : ∃ G, F = G + 2 := ⟨F - 2, by omega⟩
  let tail := .wort "else" ::
    ((if strEq reason "" then [] else [.zeichen "(", nameTok reason, .zeichen ")"]) ++
      (druckAnw body ++ .zeichen ";" :: rest))
  have hd : druckAnw (.callIndElse pointer args reason body) ++ rest = .zeichen "(" ::
      (druckToks pointer ++ .zeichen ")" :: .zeichen "(" ::
        (druckToksListe args ++ [.zeichen ")"] ++ tail)) := by
    simp only [druckAnw, tail, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd]
  change parseIndRuf G (parseBlock G) (druckToks pointer ++ .zeichen ")" :: .zeichen "(" ::
    (druckToksListe args ++ [.zeichen ")"] ++ tail)) = _
  have hP := ausdruck pointer hp (.zeichen ")" :: .zeichen "(" ::
    (druckToksListe args ++ [.zeichen ")"] ++ tail)) G rfl rfl rfl (by omega)
  have hA := argsM args tail G (args_gut args ha) (by omega)
  have hB := hb (.zeichen ";" :: rest) G (by simp only [fbA]; omega)
  simp only [parseIndRuf, hP, bind, Except.bind, fordereZeichen, strEq_self, ↓reduceIte]
  rw [hA]
  exact indCallElse_tail (parseBlock G) pointer args reason body rest hk hB

end Gabbro.Grammatik.Parser
