module
public import Grammatik.Parser.Elab.Proben.RightsConstants.Fragments

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

-- Separate each small numeric certificate from later multi-fragment inputs.
scoped macro "bound_fragment " fragment:ident " as " text:str : command => do
  let bound := Lean.mkIdentFrom fragment (fragment.getId.appendAfter "_bounded")
  let named := Lean.mkIdentFrom fragment (fragment.getId.appendAfter "_text")
  let bounded ← `(command| theorem $bound :
      decide (($fragment : Chunk).steps ≤ ($fragment : Chunk).characters.length) = true := by
        cbv)
  let decoded ← `(command| theorem $named :
      String.ofList ($fragment : Chunk).characters = $text := by cbv)
  return Lean.mkNullNode #[bounded, decoded]

open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
namespace Inputs

bound_fragment cut0 as "module m { impl fn f() { advances setup -> live; } }"
bound_fragment cut1 as "module m { table T count 2 { slot { b : bool, } } impl fn "
bound_fragment cut2 as "u(r : ptr<normal, own> T, i : index into T) -> bool effects "
bound_fragment cut3 as "{ reads r.slots, writes r.slots } { r.slots[i].b = true; "
bound_fragment cut4 as "return r.slots[i].b; } }"
bound_fragment cut5 as "u(r : ptr<normal, w+r> T, i : index into T) -> bool effects "
bound_fragment cut6 as "u(r : ptr<normal, w> T, i : index into T) -> bool effects { "
bound_fragment cut7 as "reads r.slots, writes r.slots } { r.slots[i].b = true; "
bound_fragment cut8 as "u(r : ptr<normal, w> T, i : index into T) effects { writes "
bound_fragment cut9 as "r.slots } { r.slots[i].b = true; } }"
bound_fragment cut10 as "module m { linear type Marke; table T count 2 owner Marke { "
bound_fragment cut11 as "slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> "
bound_fragment cut12 as "T, i : index into T) -> bool effects { reads r.slots, writes "
bound_fragment cut13 as "r.slots, borrows Marke } { r.slots[i].b = true; return "
bound_fragment cut14 as "r.slots[i].b; } }"
bound_fragment cut15 as "r.slots } { r.slots[i].b = true; return r.slots[i].b; } }"
bound_fragment cut16 as "module m { linear type Marke; linear type Fremd; table T "
bound_fragment cut17 as "count 2 owner Marke { slot { b : bool, } } impl fn u(r : "
bound_fragment cut18 as "ptr<normal, rw+own@Marke> T, i : index into T) -> bool "
bound_fragment cut19 as "effects { reads r.slots, writes r.slots, borrows Fremd } { "
bound_fragment cut20 as "r.slots[i].b = true; return r.slots[i].b; } }"
bound_fragment cut21 as "module m { table T count 2 owner Marke { slot { b : bool, } "
bound_fragment cut22 as "} type Marke = u32; }"
bound_fragment cut23 as "module m { impl fn f(m : u8) -> u8 { return ~m; } impl fn "
bound_fragment cut24 as "g(w : u8) -> bool { return (w ^ u8::max) == ~w; } }"
bound_fragment cut25 as "module m { impl fn f(x : u8 in 0 .. 15) -> u8 { return ~x; } "
bound_fragment cut26 as "impl fn k(w : u16 in 0 .. 255) -> u16 { return ~w; } }"
bound_fragment cut27 as "module m { impl fn f(x : u32) -> u32 { return ~(x + 1); } }"
bound_fragment cut28 as "module m { impl fn f(x : i32) -> i32 { return ~x; } }"
bound_fragment cut29 as "module m { const A : u32 = 6 * 7; const B : u32 = A + 2 * (A "
bound_fragment cut30 as "^ 3) - (A >> 1); impl fn f() -> u32 { return B; } }"
bound_fragment cut31 as "module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in "
bound_fragment cut32 as "0 .. 2000 { return n + n; } const C : u32 = doppelt(21); "
bound_fragment cut33 as "impl fn f() -> u32 { return C; } }"
bound_fragment cut34 as "module m { const X : u8 = 200 + 100; impl fn f() -> u8 { "
bound_fragment cut35 as "return X; } }"
bound_fragment cut36 as "module m { const Y : u32 = 3 - 5; impl fn f() -> u32 { "
bound_fragment cut37 as "return Y; } }"
bound_fragment cut38 as "0 .. 2000 { return n + n; } const C : u32 = doppelt(2000); "
bound_fragment cut39 as "slot { b : bool, } } impl fn minter(r : ptr<normal, "
bound_fragment cut40 as "rw+own@Marke> T, i : index into T) -> bool effects { reads "
bound_fragment cut41 as "r.slots, writes r.slots, mints Marke } { r.slots[i].b = "
bound_fragment cut42 as "true; return r.slots[i].b; } }"
bound_fragment cut43 as "slot { b : bool, } } impl fn mover(p : ptr<normal, "
bound_fragment cut44 as "p.slots, writes p.slots, moves Marke } { p.slots[i].b = "
bound_fragment cut45 as "true; return p.slots[i].b; } impl fn caller(r : ptr<normal, "
bound_fragment cut46 as "r.slots, writes r.slots, moves Marke } { mover(r, i); return "
bound_fragment cut47 as "slot { b : bool, } } reason G { Weg = 1 \"weg\" exhaustive } "
bound_fragment cut48 as "impl fn mover(p : ptr<normal, rw+own@Marke> T, i : index "
bound_fragment cut49 as "into T) -> bool or G effects { reads p.slots, writes "
bound_fragment cut50 as "p.slots, moves Marke } { p.slots[i].b = true; return G::Weg; "
bound_fragment cut51 as "} }"
bound_fragment cut52 as "slot { b : bool, } } impl fn a() -> bool effects { mints "
bound_fragment cut53 as "Marke } { return true; } impl fn b() -> bool effects { mints "
bound_fragment cut54 as "Marke } { return true; } }"
bound_fragment cut55 as "count 2 owner Marke { slot { b : bool, } } impl fn a() -> "
bound_fragment cut56 as "bool effects { mints Fremd } { return true; } }"
bound_fragment cut57 as "bool effects { moves Fremd } { return true; } }"
bound_fragment cut58 as "slot { b : bool, } } impl fn a() -> bool effects { borrows "
bound_fragment cut59 as "Marke, moves Marke } { return true; } }"
bound_fragment cut60 as "slot { b : bool, } } impl fn mover(i : index into T) -> bool "
bound_fragment cut61 as "effects { moves Marke } { return true; } impl fn caller() { "
bound_fragment cut62 as "mover(0); } }"
bound_fragment cut63 as "slot { b : bool, } } impl fn finish() effects { consumes "
bound_fragment cut64 as "Marke } { retires Marke; } impl fn main() -> u8 effects { "
bound_fragment cut65 as "consumes Marke } { finish(); return 23; } }"
bound_fragment cut66 as "Marke } {  } impl fn main() -> u8 effects { consumes Marke } "
bound_fragment cut67 as "{ finish(); return 23; } }"
bound_fragment cut68 as "slot { b : bool, } } impl fn f() effects { borrows Marke } { "
bound_fragment cut69 as "retires Marke; } }"
bound_fragment cut70 as "module m { linear type Marke; impl fn f() { retires Marke; } "
bound_fragment cut71 as "}"
bound_fragment cut72 as "Marke } { retires Marke; retires Marke; } impl fn main() -> "
bound_fragment cut73 as "u8 effects { consumes Marke } { finish(); return 23; } }"
bound_fragment cut74 as "module m { linear type Duty; impl fn gate() effects { "
bound_fragment cut75 as "consumes Duty } { retires Duty; } impl fn caller() effects { "
bound_fragment cut76 as "consumes Duty } { gate(); } }"
bound_fragment cut77 as "slot { b : bool, } } impl fn f() effects { moves Marke } { "
bound_fragment cut78 as "slot { b : bool, } } reason R { Gone = 1 \"gone\" exhaustive } "
bound_fragment cut79 as "impl fn f() -> bool or R effects { consumes Marke } { "
bound_fragment cut80 as "retires Marke; return R::Gone; } }"
bound_fragment cut81 as "module m { linear ghost type Phase order { cold, warm, hot "
bound_fragment cut82 as "}; table T count 2 owner Phase { slot { b : bool, } } impl "
bound_fragment cut83 as "fn finish() effects { consumes Phase } { advances cold -> "
bound_fragment cut84 as "warm; advances warm -> hot; retires Phase; } }"
bound_fragment cut85 as "module m { linear type Plain; linear type Phase order { "
bound_fragment cut86 as "cold, warm, hot }; linear type Pair order { first, second }; "
bound_fragment cut87 as "impl fn f() { } }"
bound_fragment cut88 as "module m { linear type Phase order { cold, warm, hot }; impl "
bound_fragment cut89 as "warm; advances warm -> hot; advances hot -> cold; } }"
bound_fragment cut90 as "hot; } }"
bound_fragment cut91 as "warm; advances warm -> cold; } }"
bound_fragment cut92 as "fn finish() effects { consumes Phase } { advances warm -> "
bound_fragment cut93 as "warm; advances cold -> warm; } }"
bound_fragment cut94 as "fn finish() effects { consumes Phase } { advances missing -> "
bound_fragment cut95 as "warm; } }"
bound_fragment cut96 as "module m { linear type Phase order { cold, warm, hot }; "
bound_fragment cut97 as "table T count 2 owner Phase { slot { b : bool, } } impl fn "
bound_fragment cut98 as "f() effects { borrows Phase } { advances cold -> warm; } }"
bound_fragment cut99 as "linear type Other order { cold, warm }; impl fn f() effects "
bound_fragment cut100 as "{ consumes Phase } { advances cold -> warm; } }"
bound_fragment cut101 as "module m { linear type Phase order { cold, cold, hot }; impl "
bound_fragment cut102 as "fn f() { } }"

end Inputs
end Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
