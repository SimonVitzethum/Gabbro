module

public import Grammatik.Parser.Lex.Lexer
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

public section

namespace Gabbro.Grammatik.Parser

/-- An ASCII character has exactly the existing decimal number's tokens. -/
theorem lex_character_a :
    lex "'a'" = lex "97" ∧ lex "'a'" = .ok [.num 97, .ende] := by
  decide +kernel

/-- Space and tilde bound the printable range; quote and slash are ordinary bytes. -/
theorem lex_character_printable :
    lex "' ' '~' '\"' '/'" = .ok [.num 32, .num 126, .num 34, .num 47, .ende] := by
  decide +kernel

/-- The newline escape denotes byte 10. -/
theorem lex_character_newline : lex "'\\n'" = .ok [.num 10, .ende] := by
  decide +kernel

/-- The tab escape denotes byte 9. -/
theorem lex_character_tab : lex "'\\t'" = .ok [.num 9, .ende] := by
  decide +kernel

/-- The carriage-return escape denotes byte 13. -/
theorem lex_character_return : lex "'\\r'" = .ok [.num 13, .ende] := by
  decide +kernel

/-- The zero escape denotes byte 0. -/
theorem lex_character_zero : lex "'\\0'" = .ok [.num 0, .ende] := by
  decide +kernel

/-- The backslash escape denotes byte 92. -/
theorem lex_character_backslash : lex "'\\\\'" = .ok [.num 92, .ende] := by
  decide +kernel

/-- The apostrophe escape denotes byte 39. -/
theorem lex_character_apostrophe : lex "'\\''" = .ok [.num 39, .ende] := by
  decide +kernel

/-- Scanning resumes immediately after each closer in an ordinary expression. -/
theorem lex_character_expression :
    lex "b=='a'+'\\n'" = .ok [.ident "b", .zeichen "==", .num 97, .zeichen "+", .num 10, .ende] := by
  decide +kernel

/-- The documentation scanner shares numeric character sugar. -/
theorem lex_character_documentation :
    lexDoku "/// byte\n'a'" = .ok [.doku " byte", .num 97, .ende] := by
  decide +kernel

/-- An empty character literal is a lexer error. -/
theorem lex_character_empty_refused :
    lex "''" = .error (.unbekannt "invalid character literal") := by
  decide +kernel

/-- Two characters do not fit one byte literal. -/
theorem lex_character_multiple_refused :
    lex "'ab'" = .error (.unbekannt "invalid character literal") := by
  decide +kernel

/-- A non-ASCII character is refused even when it is a permitted identifier letter. -/
theorem lex_character_non_ascii_refused :
    lex "'ä'" = .error (.unbekannt "invalid character literal") := by
  decide +kernel

/-- Escape names form a closed set. -/
theorem lex_character_unknown_escape_refused :
    lex "'\\x'" = .error (.unbekannt "invalid character literal") := by
  decide +kernel

/-- Plain and escaped bytes both require a closing apostrophe. -/
theorem lex_character_unclosed_refused :
    lex "'a" = .error (.unbekannt "invalid character literal") ∧
    lex "'\\n" = .error (.unbekannt "invalid character literal") := by
  decide +kernel

/-- A bare opener and an unfinished escape are lexer errors. -/
theorem lex_character_incomplete_refused :
    lex "'" = .error (.unbekannt "invalid character literal") ∧
    lex "'\\" = .error (.unbekannt "invalid character literal") := by
  decide +kernel

/-- Apostrophe and backslash require their explicit escapes. -/
theorem lex_character_unescaped_refused :
    lex "'''" = .error (.unbekannt "invalid character literal") ∧
    lex "'\\'" = .error (.unbekannt "invalid character literal") := by
  decide +kernel

/-- Raw control bytes, including DEL, are outside printable ASCII. -/
theorem lex_character_controls_refused :
    ∀ c ∈ ['\n', '\t', '\r', Char.ofNat 0, Char.ofNat 127],
      lex (String.ofList ['\'', c, '\'']) = .error (.unbekannt "invalid character literal") := by
  decide +kernel

end Gabbro.Grammatik.Parser
