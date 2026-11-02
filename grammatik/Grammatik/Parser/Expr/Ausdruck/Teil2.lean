module

public import Grammatik.Parser.Expr.Ausdruck.Teil2a

public import Grammatik.Parser.Lex.Lexer
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Expr.Ausdruck.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- Trees that print bare under a prefix operator. `fnref` is not
    among them: `!&f` is refused on both sides, so it prints
    parenthesised and stays stable. -/
def istAtom : SExpr → Bool
  | .bin .. => false
  | .un .. => false
  | .fnref _ => false
  | _ => true

-- The printer: binary operators fully parenthesised, so the
-- printed form parses back with the same shape regardless of
-- precedence or associativity. Mutual with `druckArgs` (not
-- `List.map`): the kernel reduces structural recursion, and the
-- `map` form forced well-founded recursion, which it does not.
mutual
def druck : SExpr → String
  | .lit n => toString n
  | .float s => s
  | .tru => "true"
  | .fls => "false"
  | .variable s => s
  | .field x f => druck x ++ "." ++ f
  | .index x i => druck x ++ "[" ++ druck i ++ "]"
  | .arrow x f => druck x ++ "->" ++ f
  | .un o x =>
    if strEq o "-()" then "-(" ++ druck x ++ ")"
    else if istAtom x then o ++ druck x else o ++ "(" ++ druck x ++ ")"
  | .bin o l r => "(" ++ druck l ++ " " ++ o ++ " " ++ druck r ++ ")"
  | .call f args =>
    match args with
    | [] => if strEq f "None" then "None" else f ++ "()"
    | _ :: _ => f ++ "(" ++ druckArgs args ++ ")"
  | .fnref p => "&" ++ p
  | .built f args => f ++ "(" ++ druckArgs args ++ ")"
  | .old x => "old(" ++ druck x ++ ")"
  | .res => "result"
  | .why g f => g ++ "::" ++ f
  | .ext .text ns _ => "\"" ++ ("".intercalate ns) ++ "\""
  | .ext _ _ _ => "<ext>"
def druckArgs : List SExpr → String
  | [] => ""
  | [x] => druck x
  | x :: xs => druck x ++ ", " ++ druckArgs xs
end

end Gabbro.Grammatik.Parser
