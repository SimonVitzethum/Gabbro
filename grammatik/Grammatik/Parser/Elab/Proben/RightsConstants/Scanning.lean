module
public import Grammatik.Parser.Elab.Proben.RightsConstants.Data
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

/-- One actual source with the canonical lexer equation already fixed. -/
structure Input (source : String) where
  characters : List Char
  tokens : List Token
  text : source = String.ofList characters
  lexed : lexL characters = .ok tokens

def Input.of_chunks {source : String} (pieces : List Chunk)
    (text : source = String.ofList (Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning.characters pieces))
    (room : steps pieces ≤ (Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning.characters pieces).length + 1) : Input source :=
  ⟨Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning.characters pieces, Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning.tokens pieces,
    text, lex_chunks pieces room⟩

-- Infer the token data from the real short lexer result. The final certificate
-- checks this exact fragment again with an arbitrary scanner continuation.
scoped macro "rights_cut " text:str : term =>
  `((by
    let chars : List Char := ($text : String).toList
    let emitted : List Token := ?emitted
    have decoded : lexL chars = .ok emitted := by cbv <;> exact Eq.refl _
    refine {
      characters := chars
      tokens := emitted.dropLast
      steps := (chars.filter istLeer).length + emitted.length - 1
      scanned := ?_ }
    intro rest remaining
    cbv) : Chunk)

scoped macro "rights_input " source:term " with_cuts " cuts:term " with_text " fragments:term : term =>
  `((by
    let pieces : List Chunk := $cuts
    let fragments : List String := $fragments
    have charsEq : Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning.characters pieces =
        fragments.flatMap String.toList := by rfl
    refine Input.of_chunks (source := $source) pieces ?text ?room
    case text =>
      rw [charsEq]
      simp only [fragments, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        String.ofList_append, String.ofList_toList]
      cbv
    case room => cbv <;> omega) : Input $source)

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

def advanceBare : Input "module m { impl fn f() { advances setup -> live; } }" := rights_input "module m { impl fn f() { advances setup -> live; } }"
  with_cuts [cut0]
  with_text ["module m { impl fn f() { advances setup -> live; } }"]

def own1 : Input Gabbro.Grammatik.Parser.UebersetzeProben11.own1 := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.own1
  with_cuts [cut1, cut2, cut3, cut4]
  with_text ["module m { table T count 2 { slot { b : bool, } } impl fn ", "u(r : ptr<normal, own> T, i : index into T) -> bool effects ", "{ reads r.slots, writes r.slots } { r.slots[i].b = true; ", "return r.slots[i].b; } }"]

def rightsUnion : Input (Gabbro.Grammatik.Parser.UebersetzeProben11.tableRights "w+r") := rights_input (Gabbro.Grammatik.Parser.UebersetzeProben11.tableRights "w+r")
  with_cuts [cut1, cut5, cut3, cut4]
  with_text ["module m { table T count 2 { slot { b : bool, } } impl fn ", "u(r : ptr<normal, w+r> T, i : index into T) -> bool effects ", "{ reads r.slots, writes r.slots } { r.slots[i].b = true; ", "return r.slots[i].b; } }"]

def writeOnly : Input (Gabbro.Grammatik.Parser.UebersetzeProben11.tableRights "w") := rights_input (Gabbro.Grammatik.Parser.UebersetzeProben11.tableRights "w")
  with_cuts [cut1, cut6, cut7, cut4]
  with_text ["module m { table T count 2 { slot { b : bool, } } impl fn ", "u(r : ptr<normal, w> T, i : index into T) -> bool effects { ", "reads r.slots, writes r.slots } { r.slots[i].b = true; ", "return r.slots[i].b; } }"]

def storeOnly : Input Gabbro.Grammatik.Parser.UebersetzeProben11.storeOnly := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.storeOnly
  with_cuts [cut1, cut8, cut9]
  with_text ["module m { table T count 2 { slot { b : bool, } } impl fn ", "u(r : ptr<normal, w> T, i : index into T) effects { writes ", "r.slots } { r.slots[i].b = true; } }"]

def ownAtMarke : Input Gabbro.Grammatik.Parser.UebersetzeProben11.ownAtMarke := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.ownAtMarke
  with_cuts [cut10, cut11, cut12, cut13, cut14]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> ", "T, i : index into T) -> bool effects { reads r.slots, writes ", "r.slots, borrows Marke } { r.slots[i].b = true; return ", "r.slots[i].b; } }"]

def ownAtMarkeOhneLeiht : Input Gabbro.Grammatik.Parser.UebersetzeProben11.ownAtMarkeOhneLeiht := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.ownAtMarkeOhneLeiht
  with_cuts [cut10, cut11, cut12, cut15]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> ", "T, i : index into T) -> bool effects { reads r.slots, writes ", "r.slots } { r.slots[i].b = true; return r.slots[i].b; } }"]

def ownAtMarkeFremdLeiht : Input Gabbro.Grammatik.Parser.UebersetzeProben11.ownAtMarkeFremdLeiht := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.ownAtMarkeFremdLeiht
  with_cuts [cut16, cut17, cut18, cut19, cut20]
  with_text ["module m { linear type Marke; linear type Fremd; table T ", "count 2 owner Marke { slot { b : bool, } } impl fn u(r : ", "ptr<normal, rw+own@Marke> T, i : index into T) -> bool ", "effects { reads r.slots, writes r.slots, borrows Fremd } { ", "r.slots[i].b = true; return r.slots[i].b; } }"]

def ownerOhneLinear : Input Gabbro.Grammatik.Parser.UebersetzeProben11.ownerOhneLinear := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.ownerOhneLinear
  with_cuts [cut21, cut22]
  with_text ["module m { table T count 2 owner Marke { slot { b : bool, } ", "} type Marke = u32; }"]

def bnot1 : Input Gabbro.Grammatik.Parser.UebersetzeProben11.bnot1 := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.bnot1
  with_cuts [cut23, cut24]
  with_text ["module m { impl fn f(m : u8) -> u8 { return ~m; } impl fn ", "g(w : u8) -> bool { return (w ^ u8::max) == ~w; } }"]

def bnot_schmal : Input Gabbro.Grammatik.Parser.UebersetzeProben11.bnot_schmal := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.bnot_schmal
  with_cuts [cut25, cut26]
  with_text ["module m { impl fn f(x : u8 in 0 .. 15) -> u8 { return ~x; } ", "impl fn k(w : u16 in 0 .. 255) -> u16 { return ~w; } }"]

def bnot_ausdruck : Input Gabbro.Grammatik.Parser.UebersetzeProben11.bnot_ausdruck := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.bnot_ausdruck
  with_cuts [cut27]
  with_text ["module m { impl fn f(x : u32) -> u32 { return ~(x + 1); } }"]

def bnot_vorzeichen : Input Gabbro.Grammatik.Parser.UebersetzeProben11.bnot_vorzeichen := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.bnot_vorzeichen
  with_cuts [cut28]
  with_text ["module m { impl fn f(x : i32) -> i32 { return ~x; } }"]

def konst_ausdruck : Input Gabbro.Grammatik.Parser.UebersetzeProben11.konst_ausdruck := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.konst_ausdruck
  with_cuts [cut29, cut30]
  with_text ["module m { const A : u32 = 6 * 7; const B : u32 = A + 2 * (A ", "^ 3) - (A >> 1); impl fn f() -> u32 { return B; } }"]

def konst_fn : Input Gabbro.Grammatik.Parser.UebersetzeProben11.konst_fn := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.konst_fn
  with_cuts [cut31, cut32, cut33]
  with_text ["module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in ", "0 .. 2000 { return n + n; } const C : u32 = doppelt(21); ", "impl fn f() -> u32 { return C; } }"]

def konst_ueberlauf : Input Gabbro.Grammatik.Parser.UebersetzeProben11.konst_ueberlauf := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.konst_ueberlauf
  with_cuts [cut34, cut35]
  with_text ["module m { const X : u8 = 200 + 100; impl fn f() -> u8 { ", "return X; } }"]

def konst_negativ : Input Gabbro.Grammatik.Parser.UebersetzeProben11.konst_negativ := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.konst_negativ
  with_cuts [cut36, cut37]
  with_text ["module m { const Y : u32 = 3 - 5; impl fn f() -> u32 { ", "return Y; } }"]

def konst_argument : Input Gabbro.Grammatik.Parser.UebersetzeProben11.konst_argument := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.konst_argument
  with_cuts [cut31, cut38, cut33]
  with_text ["module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in ", "0 .. 2000 { return n + n; } const C : u32 = doppelt(2000); ", "impl fn f() -> u32 { return C; } }"]

def mintAtMarke : Input Gabbro.Grammatik.Parser.UebersetzeProben11.mintAtMarke := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.mintAtMarke
  with_cuts [cut10, cut39, cut40, cut41, cut42]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn minter(r : ptr<normal, ", "rw+own@Marke> T, i : index into T) -> bool effects { reads ", "r.slots, writes r.slots, mints Marke } { r.slots[i].b = ", "true; return r.slots[i].b; } }"]

def moveAtMarke : Input Gabbro.Grammatik.Parser.UebersetzeProben11.moveAtMarke := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.moveAtMarke
  with_cuts [cut10, cut43, cut40, cut44, cut45, cut40, cut46, cut14]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn mover(p : ptr<normal, ", "rw+own@Marke> T, i : index into T) -> bool effects { reads ", "p.slots, writes p.slots, moves Marke } { p.slots[i].b = ", "true; return p.slots[i].b; } impl fn caller(r : ptr<normal, ", "rw+own@Marke> T, i : index into T) -> bool effects { reads ", "r.slots, writes r.slots, moves Marke } { mover(r, i); return ", "r.slots[i].b; } }"]

def moveReasonAtMarke : Input Gabbro.Grammatik.Parser.UebersetzeProben11.moveReasonAtMarke := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.moveReasonAtMarke
  with_cuts [cut10, cut47, cut48, cut49, cut50, cut51]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } reason G { Weg = 1 \"weg\" exhaustive } ", "impl fn mover(p : ptr<normal, rw+own@Marke> T, i : index ", "into T) -> bool or G effects { reads p.slots, writes ", "p.slots, moves Marke } { p.slots[i].b = true; return G::Weg; ", "} }"]

def mintTwice : Input Gabbro.Grammatik.Parser.UebersetzeProben11.mintTwice := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.mintTwice
  with_cuts [cut10, cut52, cut53, cut54]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn a() -> bool effects { mints ", "Marke } { return true; } impl fn b() -> bool effects { mints ", "Marke } { return true; } }"]

def mintFremd : Input Gabbro.Grammatik.Parser.UebersetzeProben11.mintFremd := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.mintFremd
  with_cuts [cut16, cut55, cut56]
  with_text ["module m { linear type Marke; linear type Fremd; table T ", "count 2 owner Marke { slot { b : bool, } } impl fn a() -> ", "bool effects { mints Fremd } { return true; } }"]

def moveFremd : Input Gabbro.Grammatik.Parser.UebersetzeProben11.moveFremd := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.moveFremd
  with_cuts [cut16, cut55, cut57]
  with_text ["module m { linear type Marke; linear type Fremd; table T ", "count 2 owner Marke { slot { b : bool, } } impl fn a() -> ", "bool effects { moves Fremd } { return true; } }"]

def moveBorrowed : Input Gabbro.Grammatik.Parser.UebersetzeProben11.moveBorrowed := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.moveBorrowed
  with_cuts [cut10, cut58, cut59]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn a() -> bool effects { borrows ", "Marke, moves Marke } { return true; } }"]

def moveDropped : Input Gabbro.Grammatik.Parser.UebersetzeProben11.moveDropped := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.moveDropped
  with_cuts [cut10, cut60, cut61, cut62]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn mover(i : index into T) -> bool ", "effects { moves Marke } { return true; } impl fn caller() { ", "mover(0); } }"]

def terminalMoveRetires : Input Gabbro.Grammatik.Parser.UebersetzeProben11.terminalMoveRetires := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.terminalMoveRetires
  with_cuts [cut10, cut63, cut64, cut65]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn finish() effects { consumes ", "Marke } { retires Marke; } impl fn main() -> u8 effects { ", "consumes Marke } { finish(); return 23; } }"]

def terminalMoveDropped : Input (Gabbro.Grammatik.Parser.UebersetzeProben11.terminalMoveSource "") := rights_input (Gabbro.Grammatik.Parser.UebersetzeProben11.terminalMoveSource "")
  with_cuts [cut10, cut63, cut66, cut67]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn finish() effects { consumes ", "Marke } {  } impl fn main() -> u8 effects { consumes Marke } ", "{ finish(); return 23; } }"]

def borrowedRetire : Input Gabbro.Grammatik.Parser.UebersetzeProben11.borrowedRetire := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.borrowedRetire
  with_cuts [cut10, cut68, cut69]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn f() effects { borrows Marke } { ", "retires Marke; } }"]

def unheldRetire : Input Gabbro.Grammatik.Parser.UebersetzeProben11.unheldRetire := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.unheldRetire
  with_cuts [cut70, cut71]
  with_text ["module m { linear type Marke; impl fn f() { retires Marke; } ", "}"]

def repeatedRetire : Input (Gabbro.Grammatik.Parser.UebersetzeProben11.terminalMoveSource "retires Marke; retires Marke;") := rights_input (Gabbro.Grammatik.Parser.UebersetzeProben11.terminalMoveSource "retires Marke; retires Marke;")
  with_cuts [cut10, cut63, cut72, cut73]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn finish() effects { consumes ", "Marke } { retires Marke; retires Marke; } impl fn main() -> ", "u8 effects { consumes Marke } { finish(); return 23; } }"]

def ordinaryRetire : Input Gabbro.Grammatik.Parser.UebersetzeProben11.ordinaryRetire := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.ordinaryRetire
  with_cuts [cut74, cut75, cut76]
  with_text ["module m { linear type Duty; impl fn gate() effects { ", "consumes Duty } { retires Duty; } impl fn caller() effects { ", "consumes Duty } { gate(); } }"]

def handbackRetire : Input Gabbro.Grammatik.Parser.UebersetzeProben11.handbackRetire := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.handbackRetire
  with_cuts [cut10, cut77, cut69]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn f() effects { moves Marke } { ", "retires Marke; } }"]

def terminalReasonRetire : Input Gabbro.Grammatik.Parser.UebersetzeProben11.terminalReasonRetire := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.terminalReasonRetire
  with_cuts [cut10, cut78, cut79, cut80]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } reason R { Gone = 1 \"gone\" exhaustive } ", "impl fn f() -> bool or R effects { consumes Marke } { ", "retires Marke; return R::Gone; } }"]

def stagedOwner : Input Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwner := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwner
  with_cuts [cut81, cut82, cut83, cut84]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances warm -> hot; retires Phase; } }"]

def stagedCounts : Input "module m { linear type Plain; linear type Phase order { cold, warm, hot }; linear type Pair order { first, second }; impl fn f() { } }" := rights_input "module m { linear type Plain; linear type Phase order { cold, warm, hot }; linear type Pair order { first, second }; impl fn f() { } }"
  with_cuts [cut85, cut86, cut87]
  with_text ["module m { linear type Plain; linear type Phase order { ", "cold, warm, hot }; linear type Pair order { first, second }; ", "impl fn f() { } }"]

def stagedOrdinary : Input Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOrdinary := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOrdinary
  with_cuts [cut88, cut83, cut84]
  with_text ["module m { linear type Phase order { cold, warm, hot }; impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances warm -> hot; retires Phase; } }"]

def stagedLast : Input (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances cold -> warm; advances warm -> hot; advances hot -> cold;") := rights_input (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances cold -> warm; advances warm -> hot; advances hot -> cold;")
  with_cuts [cut81, cut82, cut83, cut89]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances warm -> hot; advances hot -> cold; } }"]

def stagedSkip : Input (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances cold -> hot;") := rights_input (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances cold -> hot;")
  with_cuts [cut81, cut82, cut83, cut90]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "hot; } }"]

def stagedBackward : Input (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances cold -> warm; advances warm -> cold;") := rights_input (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances cold -> warm; advances warm -> cold;")
  with_cuts [cut81, cut82, cut83, cut91]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances warm -> cold; } }"]

def stagedWrongInput : Input (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances warm -> hot;") := rights_input (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances warm -> hot;")
  with_cuts [cut81, cut82, cut92, cut90]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances warm -> ", "hot; } }"]

def stagedRepeated : Input (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances cold -> warm; advances cold -> warm;") := rights_input (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances cold -> warm; advances cold -> warm;")
  with_cuts [cut81, cut82, cut83, cut93]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances cold -> warm; } }"]

def stagedUnknown : Input (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances missing -> warm;") := rights_input (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances missing -> warm;")
  with_cuts [cut81, cut82, cut94, cut95]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances missing -> ", "warm; } }"]

def stagedBorrowed : Input Gabbro.Grammatik.Parser.UebersetzeProben11.stagedBorrowed := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.stagedBorrowed
  with_cuts [cut96, cut97, cut98]
  with_text ["module m { linear type Phase order { cold, warm, hot }; ", "table T count 2 owner Phase { slot { b : bool, } } impl fn ", "f() effects { borrows Phase } { advances cold -> warm; } }"]

def stagedAmbiguous : Input Gabbro.Grammatik.Parser.UebersetzeProben11.stagedAmbiguous := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.stagedAmbiguous
  with_cuts [cut96, cut99, cut100]
  with_text ["module m { linear type Phase order { cold, warm, hot }; ", "linear type Other order { cold, warm }; impl fn f() effects ", "{ consumes Phase } { advances cold -> warm; } }"]

def stagedDuplicate : Input Gabbro.Grammatik.Parser.UebersetzeProben11.stagedDuplicate := rights_input Gabbro.Grammatik.Parser.UebersetzeProben11.stagedDuplicate
  with_cuts [cut101, cut102]
  with_text ["module m { linear type Phase order { cold, cold, hot }; impl ", "fn f() { } }"]

end Inputs
end Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
