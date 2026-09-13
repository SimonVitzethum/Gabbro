/-
  File:      Grammatik/Parser/ElementTief.lean
  Subject:   T3 PART 3: Gabbro items in depth (SYNTAX.md sections 1-2,
               6, 9-14) over the Lean statement reader.

  The surface types `STyp`/`SEffekt`/`SKlausel`/`FnSig`/`SItemTief`
  with fuel-indexed readers (`parseItemTief`, `parseTopTief`).
  Probes live in `Parser/ElementTiefProben.lean`.
-/
import Grammatik.Parser.Element

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/- A surface type: SYNTAX.md section 2 `typeexpr` without spans or
    checks. `atom` is one name, `pfad` a `::` path, `ptr` a
    `ptr<space, rights>` capability, `index` an `[option] index
    into T`, `bereich` a `base in lo .. hi` range (`exkl` for
    `..<`), `reihe` an array, `wickelnd` a `wrapping` width and
    `einbettet` an `embeds [hi:lo] [scale e]` field. A brace or
    `fn(…)` group (`structty`, `variants`, `fnptr`) rides `roh`,
    balanced but uninterpreted (see CUTS). -/
inductive STyp
  | atom : String → STyp
  | pfad : List String → STyp
  | ptr : String → String → STyp → STyp
  | index : Bool → String → STyp
  | bereich : STyp → SExpr → SExpr → Bool → STyp
  | reihe : STyp → SExpr → STyp
  | wickelnd : STyp → STyp
  | einbettet : STyp → String → Option SExpr → STyp
  | roh : String → STyp
  deriving Repr

-- Shape equality on surface types, as a `Bool`: one recursive
-- function plus the list helper, exactly like
-- `beqSExpr`/`beqSExprList` (which reduce by kernel evaluation).
mutual
def beqSTyp : STyp → STyp → Bool
  | .atom a, .atom b => strEq a b
  | .pfad a, .pfad b => beqWorte a b
  | .ptr r1 w1 t1, .ptr r2 w2 t2 =>
    strEq r1 r2 && strEq w1 w2 && beqSTyp t1 t2
  | .index o1 t1, .index o2 t2 => (o1 == o2) && strEq t1 t2
  | .bereich b1 l1 h1 x1, .bereich b2 l2 h2 x2 =>
    beqSTyp b1 b2 && beqSExpr l1 l2 && beqSExpr h1 h2 && (x1 == x2)
  | .reihe t1 n1, .reihe t2 n2 => beqSTyp t1 t2 && beqSExpr n1 n2
  | .wickelnd t1, .wickelnd t2 => beqSTyp t1 t2
  | .einbettet b1 s1 x1, .einbettet b2 s2 x2 =>
    beqSTyp b1 b2 && strEq s1 s2 && beqOptExpr x1 x2
  | .roh a, .roh b => strEq a b
  | _, _ => false
def beqSTypList : List STyp → List STyp → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSTyp x y && beqSTypList xs ys
  | _, _ => false
end

end Gabbro.Grammatik.Parser
