module

public import Grammatik.Parser.Lex.Lexer
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Expr.Ausdruck.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

def parseTop (toks : List Token) : Except String SExpr :=
  match parseOr (toks.length * 8 + 32) toks with
  | .ok (e, [.ende]) => .ok e
  | .ok (_, _) => .error "trailing tokens"
  | .error e => .error e

/-- From source text: lex, then parse the whole token list. -/
def parseTopAusText (s : String) : Except String SExpr :=
  match lex s with
  | .error e => .error ("lex: " ++ toString (repr e))
  | .ok toks => parseTop toks

/-- Shape equality on parse outcomes, as a `Bool`. -/
def beqTop : Except String SExpr → Except String SExpr → Bool
  | .ok a, .ok b => beqSExpr a b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

/-- Print, then parse back. -/
def parsePrint (e : SExpr) : Except String SExpr :=
  parseTopAusText (druck e)

/-- The weaker round trip of the task: `parsePrint e = e` on a
    decided example set. The set is MICRO on purpose: composed
    `druck`-then-`lex`-then-`parse` kernel evaluation blows past
    the heartbeat limit at seven source characters (measured:
    `(1 + 2)` times out `whnf` at 200000 heartbeats, `(1)` and
    `1 + 2` are instant), so operator trees cannot round-trip by
    `decide`. Their shapes are covered at token level by the
    sondes in `Parser/AusdruckProben.lean` instead; here the five
    legs prove the pipeline mechanism end to end. The general
    `parse_expr_roundtrip` over all parser-produced trees is out
    of reach: it needs `beqSExpr` soundness, fuel sufficiency, and
    printer injectivity -- see CUTS. -/
theorem pp_lit : beqTop (parsePrint (.lit 5)) (.ok (.lit 5)) = true := by
  decide
theorem pp_var : beqTop (parsePrint (.variable "y"))
    (.ok (.variable "y")) = true := by
  decide
theorem pp_wahr : beqTop (parsePrint (.tru)) (.ok (.tru)) = true := by
  decide
theorem pp_falsch : beqTop (parsePrint (.fls))
    (.ok (.fls)) = true := by
  decide +kernel
theorem pp_not : beqTop (parsePrint (.un "!" (.variable "y")))
    (.ok (.un "!" (.variable "y"))) = true := by
  decide

/-- The round trip as one conjunction over the five legs above. -/
theorem print_parse :
    beqTop (parsePrint (.lit 5)) (.ok (.lit 5)) = true ∧
    beqTop (parsePrint (.variable "y")) (.ok (.variable "y")) = true ∧
    beqTop (parsePrint (.tru)) (.ok (.tru)) = true ∧
    beqTop (parsePrint (.fls)) (.ok (.fls)) = true ∧
    beqTop (parsePrint (.un "!" (.variable "y")))
      (.ok (.un "!" (.variable "y"))) = true :=
  ⟨pp_lit, pp_var, pp_wahr, pp_falsch, pp_not⟩

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here, and every shape difference against
  `crates/gabbro-syntax` found by the probes.

  *Every difference below was found by reading `ast.rs`/`parse.rs`
  (`cargo` cannot run in this lane); each is a documented gap, not a
  silent one.*

  1. Spans: every Rust node carries one (`span`, `bis_zu`); no
     `SExpr` does. Positions must be re-attached outside.
  2. `Klammer` vanishes: `(e)` parses to the inner tree. The printer
     re-parenthesises canonically, so `print_parse` still closes.
  3. Call labels (`marken`, «B7») are accepted and dropped: `P(a: 1)`
     parses to `ruf "P" [1]`. Rust keeps the key stream for the
     record check (`m1::verbundwert`).
  4. Floats keep canonical text (`gleit "0.0"`), not the `f64` bits,
     the dyadic flag or `rounded`-exactness `lex.rs`/`parse.rs`
     compute. Whether the literal is exact in its target type is an
     M1 question, not a parsing one.
  5. `result` and `old` read unconditionally. `parse.rs` gates them
     on `im_vertrag` (inside a contract); a context-free reader
     cannot see that flag, so a local named `result` in body
     position would misread (no corpus occurrence).
  6. `count k in D : p` («SG-24») is refused: it needs the `domain`
     and `pred` readers (SYNTAX.md section 5), which are not this
     file. A bare `count` stays a name, exactly as the failed
     lookahead in `parse.rs` does.
  7. `sizeof`/`lenof` over a TYPE (`sizeof(u32)`) is refused: there
     is no `typeexpr` reader here (`typ_oder_ort`). Over places
     (`lenof(Self)`) and `aligned(e, c)` the shape matches.
  8. `Zaehle`, `ArrayLit` (const-initializer only) and `LibraryCall`
     (`@lib#f`) have no constructor and are refused.
  9. String literals are refused in expression position (`P011` in
     `parse.rs` has no string arm either) -- same refusal.
  10. `&T` for a declared carrier reads as `fnref "T"` here; Rust
      separates the `ptr` producer (`Expr.ptrOf`) by declaration
      context this reader does not have.
  11. `beqSExpr`/`beqTop` are not proved sound or complete: the
      probes compare by kernel `Bool` evaluation, not by a
      `beqSExpr a b = true <-> a = b` theorem.
  12. `parseTop` is total but not complete: fuel `length * 8 + 32`
      suffices for every probe (each `decide` checks its own fuel),
      and a huge input may report out-of-fuel instead of parsing.
  13. The general `parse_expr_roundtrip` (for every parser-produced
      tree) is not proved: it needs item 11 (`beqSExpr` soundness)
      plus fuel sufficiency and printer injectivity. `print_parse`
      is the decided set instead -- and the set is MICRO (atoms and
      one prefix) on purpose: composed `druck`-then-`lex`-then-
      `parse` kernel evaluation exhausts the `whnf` heartbeat
      budget (200000) at seven source characters -- measured
      2026-09-13: `(1)` and `1 + 2` decide instantly, `(1 + 2)`
      times out, `1 + 2 + 3` times out. Operator shapes round-trip
      nowhere by `decide`; they are covered at token level by the
      sondes in `Parser/AusdruckProben.lean` instead.
  14. Name predicates (`istKeinPlatz`, `istTypWort`, `istIntWort`)
      and `beqSExpr` compare through character lists (`strEq`,
      `Lexer.lean`): same kernel-speed reason as the keyword
      buckets, and the probes check every predicate leg that a
      corpus expression can reach (`Self`, type words, `R::F`).
  15. The `decide` probes themselves live in
      `Parser/AusdruckProben.lean`: one kernel evaluation per
      theorem keeps every worker small (see that file's header).
  16. `druck` prints a bare-`None` call as `None`, not `None()`:
      `None` parses without parentheses (`parse.rs`), so the
      naive print would not parse back. A `Some` call always
      carries exactly one argument from the parser, so it needs
      no such case.
-/

#print axioms Gabbro.Grammatik.Parser.parseTopAusText
#print axioms Gabbro.Grammatik.Parser.druck
#print axioms Gabbro.Grammatik.Parser.print_parse
