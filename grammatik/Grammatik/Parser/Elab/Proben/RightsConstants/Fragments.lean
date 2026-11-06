module
public import Grammatik.Parser.Stmt.LibraryFixtureScanning

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

@[expose] public section
namespace Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
open Gabbro.Grammatik Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning
set_option maxRecDepth 100000

-- Chunk data projections unfold only named transparent values. The actual lexer
-- success and arbitrary-continuation scanner proofs have opaque proof cuts.
scoped macro "rights_cut " name:ident " as " text:str : command => do
  let letters : Array (Lean.TSyntax `term) := text.getString.toList.toArray.map fun char =>
    ⟨(Lean.Syntax.mkCharLit char).raw⟩
  let charsName := Lean.mkIdentFrom name (name.getId.appendAfter "_characters")
  let lexicalName := Lean.mkIdentFrom name (name.getId.appendAfter "_lexical")
  let tokensName := Lean.mkIdentFrom name (name.getId.appendAfter "_tokens")
  let countName := Lean.mkIdentFrom name (name.getId.appendAfter "_step_count")
  let stepsName := Lean.mkIdentFrom name (name.getId.appendAfter "_steps")
  let scannedName := Lean.mkIdentFrom name (name.getId.appendAfter "_scanned")
  let characters : Lean.TSyntax `command ← `(command|
    def $charsName : List Char := [$letters,*])
  let lexical : Lean.TSyntax `command ← `(command|
    def $lexicalName : { emitted : List Token // lexL $charsName = .ok emitted } := by
      refine ⟨?emitted, ?decoded⟩
      case decoded => as_aux_lemma => cbv <;> exact Eq.refl _)
  let tokens : Lean.TSyntax `command ← `(command|
    def $tokensName : List Token := ($lexicalName).val.dropLast)
  let count : Lean.TSyntax `command ← `(command|
    def $countName : { count : Nat //
        (($charsName).filter istLeer).length + ($lexicalName).val.length - 1 = count } := by
      refine ⟨?count, ?counted⟩
      case counted => as_aux_lemma => cbv <;> exact Eq.refl _)
  let steps : Lean.TSyntax `command ← `(command|
    def $stepsName : Nat := ($countName).val)
  let scanned : Lean.TSyntax `command ← `(command|
    theorem $scannedName (rest : List Char) (remaining : Nat) :
        scan false ($charsName ++ rest) (remaining + $stepsName) =
          ($tokensName).foldr (fun token answer => Except.map (token :: ·) answer)
            (scan false rest remaining) := by cbv)
  let chunk : Lean.TSyntax `command ← `(command|
    def $name : Chunk where
      characters := $charsName
      tokens := $tokensName
      steps := $stepsName
      scanned := $scannedName)
  return ⟨Lean.mkNullNode #[characters, lexical, tokens, count, steps, scanned, chunk]⟩


open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
namespace Inputs

rights_cut cut0 as "module m { impl fn f() { advances setup -> live; } }"
rights_cut cut1 as "module m { table T count 2 { slot { b : bool, } } impl fn "
rights_cut cut2 as "u(r : ptr<normal, own> T, i : index into T) -> bool effects "
rights_cut cut3 as "{ reads r.slots, writes r.slots } { r.slots[i].b = true; "
rights_cut cut4 as "return r.slots[i].b; } }"
rights_cut cut5 as "u(r : ptr<normal, w+r> T, i : index into T) -> bool effects "
rights_cut cut6 as "u(r : ptr<normal, w> T, i : index into T) -> bool effects { "
rights_cut cut7 as "reads r.slots, writes r.slots } { r.slots[i].b = true; "
rights_cut cut8 as "u(r : ptr<normal, w> T, i : index into T) effects { writes "
rights_cut cut9 as "r.slots } { r.slots[i].b = true; } }"
rights_cut cut10 as "module m { linear type Marke; table T count 2 owner Marke { "
rights_cut cut11 as "slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> "
rights_cut cut12 as "T, i : index into T) -> bool effects { reads r.slots, writes "
rights_cut cut13 as "r.slots, borrows Marke } { r.slots[i].b = true; return "
rights_cut cut14 as "r.slots[i].b; } }"
rights_cut cut15 as "r.slots } { r.slots[i].b = true; return r.slots[i].b; } }"
rights_cut cut16 as "module m { linear type Marke; linear type Fremd; table T "
rights_cut cut17 as "count 2 owner Marke { slot { b : bool, } } impl fn u(r : "
rights_cut cut18 as "ptr<normal, rw+own@Marke> T, i : index into T) -> bool "
rights_cut cut19 as "effects { reads r.slots, writes r.slots, borrows Fremd } { "
rights_cut cut20 as "r.slots[i].b = true; return r.slots[i].b; } }"
rights_cut cut21 as "module m { table T count 2 owner Marke { slot { b : bool, } "
rights_cut cut22 as "} type Marke = u32; }"
rights_cut cut23 as "module m { impl fn f(m : u8) -> u8 { return ~m; } impl fn "
rights_cut cut24 as "g(w : u8) -> bool { return (w ^ u8::max) == ~w; } }"
rights_cut cut25 as "module m { impl fn f(x : u8 in 0 .. 15) -> u8 { return ~x; } "
rights_cut cut26 as "impl fn k(w : u16 in 0 .. 255) -> u16 { return ~w; } }"
rights_cut cut27 as "module m { impl fn f(x : u32) -> u32 { return ~(x + 1); } }"
rights_cut cut28 as "module m { impl fn f(x : i32) -> i32 { return ~x; } }"
rights_cut cut29 as "module m { const A : u32 = 6 * 7; const B : u32 = A + 2 * (A "
rights_cut cut30 as "^ 3) - (A >> 1); impl fn f() -> u32 { return B; } }"
rights_cut cut31 as "module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in "
rights_cut cut32 as "0 .. 2000 { return n + n; } const C : u32 = doppelt(21); "
rights_cut cut33 as "impl fn f() -> u32 { return C; } }"
rights_cut cut34 as "module m { const X : u8 = 200 + 100; impl fn f() -> u8 { "
rights_cut cut35 as "return X; } }"
rights_cut cut36 as "module m { const Y : u32 = 3 - 5; impl fn f() -> u32 { "
rights_cut cut37 as "return Y; } }"
rights_cut cut38 as "0 .. 2000 { return n + n; } const C : u32 = doppelt(2000); "
rights_cut cut39 as "slot { b : bool, } } impl fn minter(r : ptr<normal, "
rights_cut cut40 as "rw+own@Marke> T, i : index into T) -> bool effects { reads "
rights_cut cut41 as "r.slots, writes r.slots, mints Marke } { r.slots[i].b = "
rights_cut cut42 as "true; return r.slots[i].b; } }"
rights_cut cut43 as "slot { b : bool, } } impl fn mover(p : ptr<normal, "
rights_cut cut44 as "p.slots, writes p.slots, moves Marke } { p.slots[i].b = "
rights_cut cut45 as "true; return p.slots[i].b; } impl fn caller(r : ptr<normal, "
rights_cut cut46 as "r.slots, writes r.slots, moves Marke } { mover(r, i); return "
rights_cut cut47 as "slot { b : bool, } } reason G { Weg = 1 \"weg\" exhaustive } "
rights_cut cut48 as "impl fn mover(p : ptr<normal, rw+own@Marke> T, i : index "
rights_cut cut49 as "into T) -> bool or G effects { reads p.slots, writes "
rights_cut cut50 as "p.slots, moves Marke } { p.slots[i].b = true; return G::Weg; "
rights_cut cut51 as "} }"
rights_cut cut52 as "slot { b : bool, } } impl fn a() -> bool effects { mints "
rights_cut cut53 as "Marke } { return true; } impl fn b() -> bool effects { mints "
rights_cut cut54 as "Marke } { return true; } }"
rights_cut cut55 as "count 2 owner Marke { slot { b : bool, } } impl fn a() -> "
rights_cut cut56 as "bool effects { mints Fremd } { return true; } }"
rights_cut cut57 as "bool effects { moves Fremd } { return true; } }"
rights_cut cut58 as "slot { b : bool, } } impl fn a() -> bool effects { borrows "
rights_cut cut59 as "Marke, moves Marke } { return true; } }"
rights_cut cut60 as "slot { b : bool, } } impl fn mover(i : index into T) -> bool "
rights_cut cut61 as "effects { moves Marke } { return true; } impl fn caller() { "
rights_cut cut62 as "mover(0); } }"
rights_cut cut63 as "slot { b : bool, } } impl fn finish() effects { consumes "
rights_cut cut64 as "Marke } { retires Marke; } impl fn main() -> u8 effects { "
rights_cut cut65 as "consumes Marke } { finish(); return 23; } }"
rights_cut cut66 as "Marke } {  } impl fn main() -> u8 effects { consumes Marke } "
rights_cut cut67 as "{ finish(); return 23; } }"
rights_cut cut68 as "slot { b : bool, } } impl fn f() effects { borrows Marke } { "
rights_cut cut69 as "retires Marke; } }"
rights_cut cut70 as "module m { linear type Marke; impl fn f() { retires Marke; } "
rights_cut cut71 as "}"
rights_cut cut72 as "Marke } { retires Marke; retires Marke; } impl fn main() -> "
rights_cut cut73 as "u8 effects { consumes Marke } { finish(); return 23; } }"
rights_cut cut74 as "module m { linear type Duty; impl fn gate() effects { "
rights_cut cut75 as "consumes Duty } { retires Duty; } impl fn caller() effects { "
rights_cut cut76 as "consumes Duty } { gate(); } }"
rights_cut cut77 as "slot { b : bool, } } impl fn f() effects { moves Marke } { "
rights_cut cut78 as "slot { b : bool, } } reason R { Gone = 1 \"gone\" exhaustive } "
rights_cut cut79 as "impl fn f() -> bool or R effects { consumes Marke } { "
rights_cut cut80 as "retires Marke; return R::Gone; } }"
rights_cut cut81 as "module m { linear ghost type Phase order { cold, warm, hot "
rights_cut cut82 as "}; table T count 2 owner Phase { slot { b : bool, } } impl "
rights_cut cut83 as "fn finish() effects { consumes Phase } { advances cold -> "
rights_cut cut84 as "warm; advances warm -> hot; retires Phase; } }"
rights_cut cut85 as "module m { linear type Plain; linear type Phase order { "
rights_cut cut86 as "cold, warm, hot }; linear type Pair order { first, second }; "
rights_cut cut87 as "impl fn f() { } }"
rights_cut cut88 as "module m { linear type Phase order { cold, warm, hot }; impl "
rights_cut cut89 as "warm; advances warm -> hot; advances hot -> cold; } }"
rights_cut cut90 as "hot; } }"
rights_cut cut91 as "warm; advances warm -> cold; } }"
rights_cut cut92 as "fn finish() effects { consumes Phase } { advances warm -> "
rights_cut cut93 as "warm; advances cold -> warm; } }"
rights_cut cut94 as "fn finish() effects { consumes Phase } { advances missing -> "
rights_cut cut95 as "warm; } }"
rights_cut cut96 as "module m { linear type Phase order { cold, warm, hot }; "
rights_cut cut97 as "table T count 2 owner Phase { slot { b : bool, } } impl fn "
rights_cut cut98 as "f() effects { borrows Phase } { advances cold -> warm; } }"
rights_cut cut99 as "linear type Other order { cold, warm }; impl fn f() effects "
rights_cut cut100 as "{ consumes Phase } { advances cold -> warm; } }"
rights_cut cut101 as "module m { linear type Phase order { cold, cold, hot }; impl "
rights_cut cut102 as "fn f() { } }"


end Inputs
end Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
