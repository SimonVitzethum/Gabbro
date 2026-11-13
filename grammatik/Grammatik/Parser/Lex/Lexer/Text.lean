module
import all Init.Data.String.Defs
@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- The closed string escape vocabulary. Character literals additionally escape apostrophes;
    strings instead escape double quotes. Unknown escapes have no decoded character. -/
def textEscape : Char → Option Char
  | 'n' => some '\n'
  | 't' => some '\t'
  | 'r' => some '\r'
  | '0' => some (Char.ofNat 0)
  | '\\' => some '\\'
  | '"' => some '"'
  | _ => none

/-- Read a string body, including its closer. Raw newlines and incomplete/unknown escapes
    refuse; an escape consumes both source characters and contributes one value character. -/
def nimmText : List Char → Option (List Char × List Char)
  | [] => none
  | '\n' :: _ => none
  | '"' :: cs => some ([], cs)
  | '\\' :: c :: cs =>
    match textEscape c, nimmText cs with
    | some value, some (h, t) => some (value :: h, t)
    | _, _ => none
  | '\\' :: [] => none
  | c :: cs => match nimmText cs with
    | some (h, t) => some (c :: h, t)
    | none => none

/-- Canonical string content, shared by the source printer and the round-trip renderer.
    Every delimiter, backslash and representable control escape is written explicitly. -/
def druckTextZeichen : List Char → List Char
  | [] => []
  | c :: cs =>
    let head :=
      if c = '\n' then ['\\', 'n']
      else if c = '\t' then ['\\', 't']
      else if c = '\r' then ['\\', 'r']
      else if c = Char.ofNat 0 then ['\\', '0']
      else if c = '\\' then ['\\', '\\']
      else if c = '"' then ['\\', '"']
      else [c]
    head ++ druckTextZeichen cs

end Gabbro.Grammatik.Parser
