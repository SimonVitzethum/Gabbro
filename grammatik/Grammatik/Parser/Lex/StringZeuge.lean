module
public import Grammatik.Parser.Round.RundlaufLex.Teil2
public import Grammatik.Parser.Expr.Ausdruck.Teil1
public import Grammatik.Parser.Lex.LexerVertrauen
import Grammatik.Kern.Taktik.KernelRfl
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

/-- All six escapes decode once; the escaped quote is content and scanning resumes afterwards. -/
theorem lex_string_escapes_zeuge :
    lex "\"a\\nb\\t\\r\\0\\\\\\\"z\" 7" = .ok
      [.text (String.ofList ['a', '\n', 'b', '\t', '\r', Char.ofNat 0, '\\', '"', 'z']),
       .num 7, .ende] := by kernel_rfl

/-- A backslash followed by `n` as a value differs from a newline value. -/
theorem lex_string_backslash_zeuge :
    lex "\"\\\\n\"" = .ok [.text "\\n", .ende] ∧
    lex "\"\\n\"" = .ok [.text "\n", .ende] :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-- The source printer and renderer both round-trip quotes, backslashes and controls. -/
theorem string_printer_roundtrip_zeuge :
    let value := String.ofList ['a', '\n', '\t', '\r', Char.ofNat 0, '\\', '"', 'z']
    lex (zeigeTok (.text value)) = .ok [.text value, .ende] ∧
    lex (renderText [.text value]) = .ok [.text value, .ende] :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-- Documentation lexing uses the same escape scanner. -/
theorem lex_string_documentation_zeuge :
    lexDoku "/// text\n\"a\\nb\"" = .ok [.doku " text", .text "a\nb", .ende] := by kernel_rfl

/-- Unknown escapes and a backslash without its escaped character are refused. -/
theorem lex_string_escape_refused_zeuge :
    lex "\"a\\qb\"" = .error .offeneZeichenkette ∧
    lex "\"a\\" = .error .offeneZeichenkette :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-- A raw newline and an escaped quote without a later closer are still refused. -/
theorem lex_string_unclosed_zeuge :
    lex "\"a\nb\"" = .error .offeneZeichenkette ∧
    lex "\"a\\\"" = .error .offeneZeichenkette :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-- The source-safety scanner skips escaped quotes, but resumes at the real closer. -/
theorem string_source_skip_zeuge :
    codeZeichen "\"a\\\"b\" tail".toList 64 = "  tail".toList ∧
    lexVertrauen "\"a\\\"b\"" = .ok [.text "a\"b", .ende] :=
  ⟨by kernel_rfl, by kernel_rfl⟩

end Gabbro.Grammatik.Parser
