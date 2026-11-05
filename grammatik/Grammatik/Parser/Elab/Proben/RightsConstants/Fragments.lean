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

scoped macro "rights_cut " text:str : term => do
  let letters : Array (Lean.TSyntax `term) := text.getString.toList.toArray.map fun char =>
    ⟨(Lean.Syntax.mkCharLit char).raw⟩
  `(show Chunk from by
    let chars : List Char := [$letters,*]
    let emitted : List Token := ?emitted
    have decoded : lexL chars = .ok emitted := by cbv <;> exact Eq.refl _
    refine {
      characters := chars
      tokens := emitted.dropLast
      steps := (chars.filter istLeer).length + emitted.length - 1
      scanned := ?_ }
    intro rest remaining
    cbv)


open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
namespace Inputs

def cut0 : Chunk := rights_cut "module m { impl fn f() { advances setup -> live; } }"
def cut1 : Chunk := rights_cut "module m { table T count 2 { slot { b : bool, } } impl fn "
def cut2 : Chunk := rights_cut "u(r : ptr<normal, own> T, i : index into T) -> bool effects "
def cut3 : Chunk := rights_cut "{ reads r.slots, writes r.slots } { r.slots[i].b = true; "
def cut4 : Chunk := rights_cut "return r.slots[i].b; } }"
def cut5 : Chunk := rights_cut "u(r : ptr<normal, w+r> T, i : index into T) -> bool effects "
def cut6 : Chunk := rights_cut "u(r : ptr<normal, w> T, i : index into T) -> bool effects { "
def cut7 : Chunk := rights_cut "reads r.slots, writes r.slots } { r.slots[i].b = true; "
def cut8 : Chunk := rights_cut "u(r : ptr<normal, w> T, i : index into T) effects { writes "
def cut9 : Chunk := rights_cut "r.slots } { r.slots[i].b = true; } }"
def cut10 : Chunk := rights_cut "module m { linear type Marke; table T count 2 owner Marke { "
def cut11 : Chunk := rights_cut "slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> "
def cut12 : Chunk := rights_cut "T, i : index into T) -> bool effects { reads r.slots, writes "
def cut13 : Chunk := rights_cut "r.slots, borrows Marke } { r.slots[i].b = true; return "
def cut14 : Chunk := rights_cut "r.slots[i].b; } }"
def cut15 : Chunk := rights_cut "r.slots } { r.slots[i].b = true; return r.slots[i].b; } }"
def cut16 : Chunk := rights_cut "module m { linear type Marke; linear type Fremd; table T "
def cut17 : Chunk := rights_cut "count 2 owner Marke { slot { b : bool, } } impl fn u(r : "
def cut18 : Chunk := rights_cut "ptr<normal, rw+own@Marke> T, i : index into T) -> bool "
def cut19 : Chunk := rights_cut "effects { reads r.slots, writes r.slots, borrows Fremd } { "
def cut20 : Chunk := rights_cut "r.slots[i].b = true; return r.slots[i].b; } }"
def cut21 : Chunk := rights_cut "module m { table T count 2 owner Marke { slot { b : bool, } "
def cut22 : Chunk := rights_cut "} type Marke = u32; }"
def cut23 : Chunk := rights_cut "module m { impl fn f(m : u8) -> u8 { return ~m; } impl fn "
def cut24 : Chunk := rights_cut "g(w : u8) -> bool { return (w ^ u8::max) == ~w; } }"
def cut25 : Chunk := rights_cut "module m { impl fn f(x : u8 in 0 .. 15) -> u8 { return ~x; } "
def cut26 : Chunk := rights_cut "impl fn k(w : u16 in 0 .. 255) -> u16 { return ~w; } }"
def cut27 : Chunk := rights_cut "module m { impl fn f(x : u32) -> u32 { return ~(x + 1); } }"
def cut28 : Chunk := rights_cut "module m { impl fn f(x : i32) -> i32 { return ~x; } }"
def cut29 : Chunk := rights_cut "module m { const A : u32 = 6 * 7; const B : u32 = A + 2 * (A "
def cut30 : Chunk := rights_cut "^ 3) - (A >> 1); impl fn f() -> u32 { return B; } }"
def cut31 : Chunk := rights_cut "module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in "
def cut32 : Chunk := rights_cut "0 .. 2000 { return n + n; } const C : u32 = doppelt(21); "
def cut33 : Chunk := rights_cut "impl fn f() -> u32 { return C; } }"
def cut34 : Chunk := rights_cut "module m { const X : u8 = 200 + 100; impl fn f() -> u8 { "
def cut35 : Chunk := rights_cut "return X; } }"
def cut36 : Chunk := rights_cut "module m { const Y : u32 = 3 - 5; impl fn f() -> u32 { "
def cut37 : Chunk := rights_cut "return Y; } }"
def cut38 : Chunk := rights_cut "0 .. 2000 { return n + n; } const C : u32 = doppelt(2000); "
def cut39 : Chunk := rights_cut "slot { b : bool, } } impl fn minter(r : ptr<normal, "
def cut40 : Chunk := rights_cut "rw+own@Marke> T, i : index into T) -> bool effects { reads "
def cut41 : Chunk := rights_cut "r.slots, writes r.slots, mints Marke } { r.slots[i].b = "
def cut42 : Chunk := rights_cut "true; return r.slots[i].b; } }"
def cut43 : Chunk := rights_cut "slot { b : bool, } } impl fn mover(p : ptr<normal, "
def cut44 : Chunk := rights_cut "p.slots, writes p.slots, moves Marke } { p.slots[i].b = "
def cut45 : Chunk := rights_cut "true; return p.slots[i].b; } impl fn caller(r : ptr<normal, "
def cut46 : Chunk := rights_cut "r.slots, writes r.slots, moves Marke } { mover(r, i); return "
def cut47 : Chunk := rights_cut "slot { b : bool, } } reason G { Weg = 1 \"weg\" exhaustive } "
def cut48 : Chunk := rights_cut "impl fn mover(p : ptr<normal, rw+own@Marke> T, i : index "
def cut49 : Chunk := rights_cut "into T) -> bool or G effects { reads p.slots, writes "
def cut50 : Chunk := rights_cut "p.slots, moves Marke } { p.slots[i].b = true; return G::Weg; "
def cut51 : Chunk := rights_cut "} }"
def cut52 : Chunk := rights_cut "slot { b : bool, } } impl fn a() -> bool effects { mints "
def cut53 : Chunk := rights_cut "Marke } { return true; } impl fn b() -> bool effects { mints "
def cut54 : Chunk := rights_cut "Marke } { return true; } }"
def cut55 : Chunk := rights_cut "count 2 owner Marke { slot { b : bool, } } impl fn a() -> "
def cut56 : Chunk := rights_cut "bool effects { mints Fremd } { return true; } }"
def cut57 : Chunk := rights_cut "bool effects { moves Fremd } { return true; } }"
def cut58 : Chunk := rights_cut "slot { b : bool, } } impl fn a() -> bool effects { borrows "
def cut59 : Chunk := rights_cut "Marke, moves Marke } { return true; } }"
def cut60 : Chunk := rights_cut "slot { b : bool, } } impl fn mover(i : index into T) -> bool "
def cut61 : Chunk := rights_cut "effects { moves Marke } { return true; } impl fn caller() { "
def cut62 : Chunk := rights_cut "mover(0); } }"
def cut63 : Chunk := rights_cut "slot { b : bool, } } impl fn finish() effects { consumes "
def cut64 : Chunk := rights_cut "Marke } { retires Marke; } impl fn main() -> u8 effects { "
def cut65 : Chunk := rights_cut "consumes Marke } { finish(); return 23; } }"
def cut66 : Chunk := rights_cut "Marke } {  } impl fn main() -> u8 effects { consumes Marke } "
def cut67 : Chunk := rights_cut "{ finish(); return 23; } }"
def cut68 : Chunk := rights_cut "slot { b : bool, } } impl fn f() effects { borrows Marke } { "
def cut69 : Chunk := rights_cut "retires Marke; } }"
def cut70 : Chunk := rights_cut "module m { linear type Marke; impl fn f() { retires Marke; } "
def cut71 : Chunk := rights_cut "}"
def cut72 : Chunk := rights_cut "Marke } { retires Marke; retires Marke; } impl fn main() -> "
def cut73 : Chunk := rights_cut "u8 effects { consumes Marke } { finish(); return 23; } }"
def cut74 : Chunk := rights_cut "module m { linear type Duty; impl fn gate() effects { "
def cut75 : Chunk := rights_cut "consumes Duty } { retires Duty; } impl fn caller() effects { "
def cut76 : Chunk := rights_cut "consumes Duty } { gate(); } }"
def cut77 : Chunk := rights_cut "slot { b : bool, } } impl fn f() effects { moves Marke } { "
def cut78 : Chunk := rights_cut "slot { b : bool, } } reason R { Gone = 1 \"gone\" exhaustive } "
def cut79 : Chunk := rights_cut "impl fn f() -> bool or R effects { consumes Marke } { "
def cut80 : Chunk := rights_cut "retires Marke; return R::Gone; } }"
def cut81 : Chunk := rights_cut "module m { linear ghost type Phase order { cold, warm, hot "
def cut82 : Chunk := rights_cut "}; table T count 2 owner Phase { slot { b : bool, } } impl "
def cut83 : Chunk := rights_cut "fn finish() effects { consumes Phase } { advances cold -> "
def cut84 : Chunk := rights_cut "warm; advances warm -> hot; retires Phase; } }"
def cut85 : Chunk := rights_cut "module m { linear type Plain; linear type Phase order { "
def cut86 : Chunk := rights_cut "cold, warm, hot }; linear type Pair order { first, second }; "
def cut87 : Chunk := rights_cut "impl fn f() { } }"
def cut88 : Chunk := rights_cut "module m { linear type Phase order { cold, warm, hot }; impl "
def cut89 : Chunk := rights_cut "warm; advances warm -> hot; advances hot -> cold; } }"
def cut90 : Chunk := rights_cut "hot; } }"
def cut91 : Chunk := rights_cut "warm; advances warm -> cold; } }"
def cut92 : Chunk := rights_cut "fn finish() effects { consumes Phase } { advances warm -> "
def cut93 : Chunk := rights_cut "warm; advances cold -> warm; } }"
def cut94 : Chunk := rights_cut "fn finish() effects { consumes Phase } { advances missing -> "
def cut95 : Chunk := rights_cut "warm; } }"
def cut96 : Chunk := rights_cut "module m { linear type Phase order { cold, warm, hot }; "
def cut97 : Chunk := rights_cut "table T count 2 owner Phase { slot { b : bool, } } impl fn "
def cut98 : Chunk := rights_cut "f() effects { borrows Phase } { advances cold -> warm; } }"
def cut99 : Chunk := rights_cut "linear type Other order { cold, warm }; impl fn f() effects "
def cut100 : Chunk := rights_cut "{ consumes Phase } { advances cold -> warm; } }"
def cut101 : Chunk := rights_cut "module m { linear type Phase order { cold, cold, hot }; impl "
def cut102 : Chunk := rights_cut "fn f() { } }"


end Inputs
end Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
