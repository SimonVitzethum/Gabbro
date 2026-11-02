/-
  File:      Grammatik/Parser/Anweisung.lean
  Subject:   T3 PART 2 (PLAN-TRANSLATION-VALIDATION.md section 1): Gabbro
              statements and blocks (SYNTAX.md section 7) over the Lean
              lexer and expression parser.

  The surface tree `SAnw`/`SEnde` with fuel-indexed readers
  (`parseStmt`, `parseBlock`, `parseTopStmt`, `parseTopBlock`).
  Probes live in `Parser/AnweisungProben.lean`.
-/
module

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
public import Grammatik.Parser.Expr.Typ
public import Grammatik.Parser.Stmt.LibraryCall
@[expose] public section


namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/- A surface tree: SYNTAX.md section 7 `stmt`, `block` and
    `endblock` without types, spans or attribute checks. ONE
    inductive on purpose: kernel `decide` does not reduce recursive
    `Bool` equality over a MUTUAL family (measured 2026-09-13 --
    even comparing two empty blocks gets stuck), while
    the single-type form with a list helper reduces like
    `beqSExpr`/`beqSExprList`. A block is the `block` node: a
    statement list with an optional ender. A trailing
    `return`/`leave`/`next` statement is split off as the ender, so
    an `endblock` reads as `block pre (some …)` and a plain `block`
    as `block all none` (see `schliesseBlock`).

    Expressions ride as `SExpr`; headers the reader does not split
    store their raw words (`each` etc. carry the header text).
    Against `ast.rs` `StmtArt`: `bind` = `Let`, `bindElse` =
    `LetSonst`, `set` = `Zuweisung`, `wenn` = `Wenn`, `cases` =
    `Match`, `each`/`retry`/`loop` = `Schleife`, `waive`
    = `Bricht`, `trim` = `Narrow`, `locks` = `Sperrt`,
    `watch` = `Observiert`, `leave` = `Leave`, `weiter` =
    `Next`, `emit` = `Publish`, `erwartet` = `AwaitLoad`,
    `swap` = `Exchange`, `rueck` = `Return`, `ruf` = `Ruf`,
    `lcall` = `LibraryCall`, `alloc` = `Alloc`, `reset` =
    `ResetArena`; `uebergang` is the `stateassign`
    (`transition … : A -> B`), `step` the `advstmt`
    (`advances a -> b`). An `else if` rides as a `elsif` node
    in the `wenn` list, a `match` arm as an `arm` node in the
    `cases` list -- pair-nodes instead of tuple lists, so the
    equality below stays a two-function block like
    `beqSExpr`/`beqSExprList` (see above). Against `parse.rs` `Block`: recovery and
    spans are dropped; a lone `;` (`P033`) is a parse error here. -/
/-- The `endstmt`: `return [expr]`, `leave l`, `next l`. Plain
    (no tree recursion), so plain equality reduces. It stands
    before `SAnw` so the `Repr` instance is in scope. -/
inductive SEnde
  | ret : Option SExpr → SEnde
  | leave : String → SEnde
  | next : String → SEnde
deriving Repr
inductive SAnw
  | bind : Bool → String → Option STyp → SExpr → SAnw
  | bindElse : String → Option STyp → SExpr → String → SAnw → SAnw
  | bindLib : Bool → String → Option STyp → SLibraryCall → SAnw
  | set : SExpr → String → SExpr → SAnw
  | shift : SExpr → String → String → SAnw
  | call : String → List SExpr → SAnw
  | lcall : SLibraryCall → SAnw
  | cond : SExpr → SAnw → List SAnw → Option SAnw → SAnw
  | elsif : SExpr → SAnw → SAnw
  | cases : SExpr → List SAnw → SAnw
  | arm : String → Option String → SAnw → SAnw
  /-- `traverse b [of e] over KIND of S by MODE [decreases …] [touches …] [invariant p] { … }`:
      binder, `of` start, domain kind word (`slots`, `ancestors`, …), domain subject, mode word,
      the raw words of `decreases`/`touches`, the invariant, the body. -/
  | each : String → Option SExpr → String → SExpr → String → String → Option SExpr → SAnw → SAnw
  | retry : String → SAnw → SAnw
  | loop : String → SAnw → SAnw
  | waive : List String → SAnw → SAnw
  | trim : SExpr → String → SAnw → SAnw
  | locks : Bool → SExpr → SAnw → SAnw
  | watch : String → SAnw → SAnw
  | leave : String → SAnw
  | next : String → SAnw
  | emit : SExpr → SExpr → String → SAnw
  | await : String → Option STyp → SExpr → String → SAnw
  | swap : String → Option STyp → SExpr → String → SAnw
  | step : String → String → SAnw
  | ret : Option SExpr → SAnw
  | alloc : Bool → String → Option STyp → String → SExpr → Option SAnw → SAnw
  /-- `reset A [at i count n];` -/
  | reset : String → Option (SExpr × SExpr) → SAnw
  /-- `grow A by e else { … };` -/
  | grow : String → SExpr → SAnw → SAnw
  /-- `free A[i];` -/
  | free : SExpr → SAnw
  /-- `child { … }` -/
  | child : SAnw → SAnw
  /-- `start { f, g };` -/
  | start : List String → SAnw
  | other : String → SAnw
  | block : List SAnw → Option SEnde → SAnw
  /-- `let [mut] x [: T] = alloc T;` -- the call of the provider of the open table `T` (`table T from p`). -/
  | allocVon : Bool → String → Option STyp → String → SAnw
  /-- Optional axiom result binding; `none` introduces no local. -/
  | bindAxiomOpt : String → Option STyp → SExpr → SAnw
  /-- Optional axiom result binding with a reason handler. -/
  | bindAxiomOptElse : String → Option STyp → SExpr → String → SAnw → SAnw
deriving Repr

-- Shape equality on surface trees, as a `Bool`: one recursive
-- function plus the list helper, exactly like
-- `beqSExpr`/`beqSExprList` (which reduce by kernel evaluation).
-- The small non-recursive equalities stand first so the mutual
-- block below can use them.
/-- Equality on enders (plain: no tree recursion). -/
def beqSEnde : SEnde → SEnde → Bool
  | .ret x, .ret y => beqOptExpr x y
  | .leave a, .leave b => strEq a b
  | .next a, .next b => strEq a b
  | _, _ => false

def beqOptPaar : Option (SExpr × SExpr) → Option (SExpr × SExpr) → Bool
  | none, none => true
  | some (a, b), some (c, d) => beqSExpr a c && beqSExpr b d
  | _, _ => false

def beqOptEnde : Option SEnde → Option SEnde → Bool
  | none, none => true
  | some a, some b => beqSEnde a b
  | _, _ => false

mutual
def beqSAnw : SAnw → SAnw → Bool
  | .bindAxiomOpt a t x, .bindAxiomOpt b u y => strEq a b && beqSTypOpt t u && beqSExpr x y
  | .bindAxiomOptElse a t f e b, .bindAxiomOptElse c u g h d =>
    strEq a c && beqSTypOpt t u && beqSExpr f g && strEq e h && beqSAnw b d
  | .bind m a t x, .bind n b u y => m == n && strEq a b && beqSTypOpt t u && beqSExpr x y
  | .bindElse a t f e b, .bindElse c u g h d =>
    strEq a c && beqSTypOpt t u && beqSExpr f g && strEq e h && beqSAnw b d
  | .bindLib m a t c, .bindLib n b u d =>
    m == n && strEq a b && beqSTypOpt t u && beqSLibraryCall c d
  | .set z o x, .set w p y =>
    beqSExpr z w && strEq o p && beqSExpr x y
  | .shift z a b, .shift w c d =>
    beqSExpr z w && strEq a c && strEq b d
  | .call f a, .call g b => strEq f g && beqSExprList a b
  | .lcall c, .lcall d => beqSLibraryCall c d
  | .cond c t ei s, .cond d u fi v =>
    beqSExpr c d && beqSAnw t u && beqSAnwList ei fi && beqOptAnw s v
  | .elsif c t, .elsif d u => beqSExpr c d && beqSAnw t u
  | .cases g a, .cases h b => beqSExpr g h && beqSAnwList a b
  | .arm v b t, .arm w c u =>
    strEq v w && beqOptWort b c && beqSAnw t u
  | .each b o k s m r i d, .each b2 o2 k2 s2 m2 r2 i2 d2 =>
    strEq b b2 && beqOptExpr o o2 && strEq k k2 && beqSExpr s s2 && strEq m m2 && strEq r r2 &&
      beqOptExpr i i2 && beqSAnw d d2
  | .retry h b, .retry i d => strEq h i && beqSAnw b d
  | .loop h b, .loop i d => strEq h i && beqSAnw b d
  | .waive inv b, .waive jnv d =>
    beqWorte inv jnv && beqSAnw b d
  | .trim o z s, .trim p w t =>
    beqSExpr o p && strEq z w && beqSAnw s t
  | .locks g o b, .locks h p d =>
    g == h && beqSExpr o p && beqSAnw b d
  | .watch d b, .watch e c => strEq d e && beqSAnw b c
  | .leave l, .leave m => strEq l m
  | .next l, .next m => strEq l m
  | .emit z w p, .emit y v q =>
    beqSExpr z y && beqSExpr w v && strEq p q
  | .await n t q e, .await m u p f =>
    strEq n m && beqSTypOpt t u && beqSExpr q p && strEq e f
  | .swap n t o k, .swap m u p l =>
    strEq n m && beqSTypOpt t u && beqSExpr o p && strEq k l
  | .step a b, .step c d => strEq a c && strEq b d
  | .ret x, .ret y => beqOptExpr x y
  | .alloc m n y t w s, .alloc k o z u v r =>
    m == k && strEq n o && beqSTypOpt y z && strEq t u && beqSExpr w v && beqOptAnw s r
  | .allocVon m n y t, .allocVon k o z u => m == k && strEq n o && beqSTypOpt y z && strEq t u
  | .reset a x, .reset b y => strEq a b && beqOptPaar x y
  | .grow a e b, .grow c f d => strEq a c && beqSExpr e f && beqSAnw b d
  | .free a, .free b => beqSExpr a b
  | .child a, .child b => beqSAnw a b
  | .start a, .start b => beqWorte a b
  | .other a, .other b => strEq a b
  | .block ss e, .block ts f => beqSAnwList ss ts && beqOptEnde e f
  | _, _ => false
def beqSAnwList : List SAnw → List SAnw → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSAnw x y && beqSAnwList xs ys
  | _, _ => false
def beqOptAnw : Option SAnw → Option SAnw → Bool
  | none, none => true
  | some a, some b => beqSAnw a b
  | _, _ => false
end

-- The equality block above must STAY three functions: larger mutual
-- blocks compile to the irreducible `PSum` fixed point, which
-- `decide` cannot unfold (measured 2026-09-13 -- even comparing two
-- empty blocks gets stuck). Tuple lists would need their own
-- helpers, so `else if` branches ride as `elsif` nodes and
-- `match` arms as `arm` nodes instead.

/-- Split a trailing `return`/`leave`/`next` off a statement list:
    an `endblock` reads as `block pre (some …)`, a plain `block` as
    `block all none`. -/
def schliesseBlock : List SAnw → SAnw
  | [] => .block [] none
  | ss => match ss.getLast? with
    | some (.ret x) => .block ss.dropLast (some (.ret x))
    | some (.leave l) => .block ss.dropLast (some (.leave l))
    | some (.next l) => .block ss.dropLast (some (.next l))
    | _ => .block ss none

-- The statement levels of SYNTAX.md section 7 (`stmt`, `block`,
-- `endblock`), each with fuel: every call passes strictly less fuel,
-- so the block terminates by `f`. Against `parse.rs`: the head-word
-- dispatch (`wort_ist_anweisungskopf` via `istKopfForm`), the
-- `let`-form order (`alloc`/`@` before the expression, then
-- `awaits`/`exchange`/`else`), the call-or-assignment split
-- (`zuweisung_oder_ruf`) and the block-end rule (no trailing `;`
-- after a block form, `P033`) match one by one. Predicates, domains,
-- `xform` bodies, payload lists and type ascriptions ride as raw
-- words (see CUTS).
/-- The raw words of a `traverse` header up to `invariant` or the body `{` (brace-free clauses). -/
def traverseRest : List Token → Except String (String × List Token)
  | [] => .error "loop without body"
  | (.zeichen "{" :: rest) => .ok ("", .zeichen "{" :: rest)
  | (.wort s :: rest) =>
    if strEq s "invariant" then .ok ("", .wort s :: rest)
    else match traverseRest rest with
      | .error e => .error e
      | .ok (h, r) => .ok (s ++ " " ++ h, r)
  | (t :: rest) => match traverseRest rest with
    | .error e => .error e
    | .ok (h, r) => .ok (zeigeTok t ++ " " ++ h, r)
