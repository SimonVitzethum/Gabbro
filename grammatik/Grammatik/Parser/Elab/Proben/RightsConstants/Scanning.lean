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
macro "rights_cut " text:str : term =>
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

macro "rights_input " source:term " cuts " cuts:term " text " fragments:term : term =>
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

namespace Inputs

private def cut0 : Chunk := rights_cut "module m { impl fn f() { advances setup -> live; } }"
private def cut1 : Chunk := rights_cut "module m { table T count 2 { slot { b : bool, } } impl fn "
private def cut2 : Chunk := rights_cut "u(r : ptr<normal, own> T, i : index into T) -> bool effects "
private def cut3 : Chunk := rights_cut "{ reads r.slots, writes r.slots } { r.slots[i].b = true; "
private def cut4 : Chunk := rights_cut "return r.slots[i].b; } }"
private def cut5 : Chunk := rights_cut "u(r : ptr<normal, w+r> T, i : index into T) -> bool effects "
private def cut6 : Chunk := rights_cut "u(r : ptr<normal, w> T, i : index into T) -> bool effects { "
private def cut7 : Chunk := rights_cut "reads r.slots, writes r.slots } { r.slots[i].b = true; "
private def cut8 : Chunk := rights_cut "u(r : ptr<normal, w> T, i : index into T) effects { writes "
private def cut9 : Chunk := rights_cut "r.slots } { r.slots[i].b = true; } }"
private def cut10 : Chunk := rights_cut "module m { linear type Marke; table T count 2 owner Marke { "
private def cut11 : Chunk := rights_cut "slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> "
private def cut12 : Chunk := rights_cut "T, i : index into T) -> bool effects { reads r.slots, writes "
private def cut13 : Chunk := rights_cut "r.slots, borrows Marke } { r.slots[i].b = true; return "
private def cut14 : Chunk := rights_cut "r.slots[i].b; } }"
private def cut15 : Chunk := rights_cut "r.slots } { r.slots[i].b = true; return r.slots[i].b; } }"
private def cut16 : Chunk := rights_cut "module m { linear type Marke; linear type Fremd; table T "
private def cut17 : Chunk := rights_cut "count 2 owner Marke { slot { b : bool, } } impl fn u(r : "
private def cut18 : Chunk := rights_cut "ptr<normal, rw+own@Marke> T, i : index into T) -> bool "
private def cut19 : Chunk := rights_cut "effects { reads r.slots, writes r.slots, borrows Fremd } { "
private def cut20 : Chunk := rights_cut "r.slots[i].b = true; return r.slots[i].b; } }"
private def cut21 : Chunk := rights_cut "module m { table T count 2 owner Marke { slot { b : bool, } "
private def cut22 : Chunk := rights_cut "} type Marke = u32; }"
private def cut23 : Chunk := rights_cut "module m { impl fn f(m : u8) -> u8 { return ~m; } impl fn "
private def cut24 : Chunk := rights_cut "g(w : u8) -> bool { return (w ^ u8::max) == ~w; } }"
private def cut25 : Chunk := rights_cut "module m { impl fn f(x : u8 in 0 .. 15) -> u8 { return ~x; } "
private def cut26 : Chunk := rights_cut "impl fn k(w : u16 in 0 .. 255) -> u16 { return ~w; } }"
private def cut27 : Chunk := rights_cut "module m { impl fn f(x : u32) -> u32 { return ~(x + 1); } }"
private def cut28 : Chunk := rights_cut "module m { impl fn f(x : i32) -> i32 { return ~x; } }"
private def cut29 : Chunk := rights_cut "module m { const A : u32 = 6 * 7; const B : u32 = A + 2 * (A "
private def cut30 : Chunk := rights_cut "^ 3) - (A >> 1); impl fn f() -> u32 { return B; } }"
private def cut31 : Chunk := rights_cut "module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in "
private def cut32 : Chunk := rights_cut "0 .. 2000 { return n + n; } const C : u32 = doppelt(21); "
private def cut33 : Chunk := rights_cut "impl fn f() -> u32 { return C; } }"
private def cut34 : Chunk := rights_cut "module m { const X : u8 = 200 + 100; impl fn f() -> u8 { "
private def cut35 : Chunk := rights_cut "return X; } }"
private def cut36 : Chunk := rights_cut "module m { const Y : u32 = 3 - 5; impl fn f() -> u32 { "
private def cut37 : Chunk := rights_cut "return Y; } }"
private def cut38 : Chunk := rights_cut "0 .. 2000 { return n + n; } const C : u32 = doppelt(2000); "
private def cut39 : Chunk := rights_cut "slot { b : bool, } } impl fn minter(r : ptr<normal, "
private def cut40 : Chunk := rights_cut "rw+own@Marke> T, i : index into T) -> bool effects { reads "
private def cut41 : Chunk := rights_cut "r.slots, writes r.slots, mints Marke } { r.slots[i].b = "
private def cut42 : Chunk := rights_cut "true; return r.slots[i].b; } }"
private def cut43 : Chunk := rights_cut "slot { b : bool, } } impl fn mover(p : ptr<normal, "
private def cut44 : Chunk := rights_cut "p.slots, writes p.slots, moves Marke } { p.slots[i].b = "
private def cut45 : Chunk := rights_cut "true; return p.slots[i].b; } impl fn caller(r : ptr<normal, "
private def cut46 : Chunk := rights_cut "r.slots, writes r.slots, moves Marke } { mover(r, i); return "
private def cut47 : Chunk := rights_cut "slot { b : bool, } } reason G { Weg = 1 \"weg\" exhaustive } "
private def cut48 : Chunk := rights_cut "impl fn mover(p : ptr<normal, rw+own@Marke> T, i : index "
private def cut49 : Chunk := rights_cut "into T) -> bool or G effects { reads p.slots, writes "
private def cut50 : Chunk := rights_cut "p.slots, moves Marke } { p.slots[i].b = true; return G::Weg; "
private def cut51 : Chunk := rights_cut "} }"
private def cut52 : Chunk := rights_cut "slot { b : bool, } } impl fn a() -> bool effects { mints "
private def cut53 : Chunk := rights_cut "Marke } { return true; } impl fn b() -> bool effects { mints "
private def cut54 : Chunk := rights_cut "Marke } { return true; } }"
private def cut55 : Chunk := rights_cut "count 2 owner Marke { slot { b : bool, } } impl fn a() -> "
private def cut56 : Chunk := rights_cut "bool effects { mints Fremd } { return true; } }"
private def cut57 : Chunk := rights_cut "bool effects { moves Fremd } { return true; } }"
private def cut58 : Chunk := rights_cut "slot { b : bool, } } impl fn a() -> bool effects { borrows "
private def cut59 : Chunk := rights_cut "Marke, moves Marke } { return true; } }"
private def cut60 : Chunk := rights_cut "slot { b : bool, } } impl fn mover(i : index into T) -> bool "
private def cut61 : Chunk := rights_cut "effects { moves Marke } { return true; } impl fn caller() { "
private def cut62 : Chunk := rights_cut "mover(0); } }"
private def cut63 : Chunk := rights_cut "slot { b : bool, } } impl fn finish() effects { consumes "
private def cut64 : Chunk := rights_cut "Marke } { retires Marke; } impl fn main() -> u8 effects { "
private def cut65 : Chunk := rights_cut "consumes Marke } { finish(); return 23; } }"
private def cut66 : Chunk := rights_cut "Marke } {  } impl fn main() -> u8 effects { consumes Marke } "
private def cut67 : Chunk := rights_cut "{ finish(); return 23; } }"
private def cut68 : Chunk := rights_cut "slot { b : bool, } } impl fn f() effects { borrows Marke } { "
private def cut69 : Chunk := rights_cut "retires Marke; } }"
private def cut70 : Chunk := rights_cut "module m { linear type Marke; impl fn f() { retires Marke; } "
private def cut71 : Chunk := rights_cut "}"
private def cut72 : Chunk := rights_cut "Marke } { retires Marke; retires Marke; } impl fn main() -> "
private def cut73 : Chunk := rights_cut "u8 effects { consumes Marke } { finish(); return 23; } }"
private def cut74 : Chunk := rights_cut "module m { linear type Duty; impl fn gate() effects { "
private def cut75 : Chunk := rights_cut "consumes Duty } { retires Duty; } impl fn caller() effects { "
private def cut76 : Chunk := rights_cut "consumes Duty } { gate(); } }"
private def cut77 : Chunk := rights_cut "slot { b : bool, } } impl fn f() effects { moves Marke } { "
private def cut78 : Chunk := rights_cut "slot { b : bool, } } reason R { Gone = 1 \"gone\" exhaustive } "
private def cut79 : Chunk := rights_cut "impl fn f() -> bool or R effects { consumes Marke } { "
private def cut80 : Chunk := rights_cut "retires Marke; return R::Gone; } }"
private def cut81 : Chunk := rights_cut "module m { linear ghost type Phase order { cold, warm, hot "
private def cut82 : Chunk := rights_cut "}; table T count 2 owner Phase { slot { b : bool, } } impl "
private def cut83 : Chunk := rights_cut "fn finish() effects { consumes Phase } { advances cold -> "
private def cut84 : Chunk := rights_cut "warm; advances warm -> hot; retires Phase; } }"
private def cut85 : Chunk := rights_cut "module m { linear type Plain; linear type Phase order { "
private def cut86 : Chunk := rights_cut "cold, warm, hot }; linear type Pair order { first, second }; "
private def cut87 : Chunk := rights_cut "impl fn f() { } }"
private def cut88 : Chunk := rights_cut "module m { linear type Phase order { cold, warm, hot }; impl "
private def cut89 : Chunk := rights_cut "warm; advances warm -> hot; advances hot -> cold; } }"
private def cut90 : Chunk := rights_cut "hot; } }"
private def cut91 : Chunk := rights_cut "warm; advances warm -> cold; } }"
private def cut92 : Chunk := rights_cut "fn finish() effects { consumes Phase } { advances warm -> "
private def cut93 : Chunk := rights_cut "warm; advances cold -> warm; } }"
private def cut94 : Chunk := rights_cut "fn finish() effects { consumes Phase } { advances missing -> "
private def cut95 : Chunk := rights_cut "warm; } }"
private def cut96 : Chunk := rights_cut "module m { linear type Phase order { cold, warm, hot }; "
private def cut97 : Chunk := rights_cut "table T count 2 owner Phase { slot { b : bool, } } impl fn "
private def cut98 : Chunk := rights_cut "f() effects { borrows Phase } { advances cold -> warm; } }"
private def cut99 : Chunk := rights_cut "linear type Other order { cold, warm }; impl fn f() effects "
private def cut100 : Chunk := rights_cut "{ consumes Phase } { advances cold -> warm; } }"
private def cut101 : Chunk := rights_cut "module m { linear type Phase order { cold, cold, hot }; impl "
private def cut102 : Chunk := rights_cut "fn f() { } }"

def advanceBare : Input "module m { impl fn f() { advances setup -> live; } }" := rights_input "module m { impl fn f() { advances setup -> live; } }"
  cuts [cut0]
  text ["module m { impl fn f() { advances setup -> live; } }"]

def own1 : Input own1 := rights_input own1
  cuts [cut1, cut2, cut3, cut4]
  text ["module m { table T count 2 { slot { b : bool, } } impl fn ", "u(r : ptr<normal, own> T, i : index into T) -> bool effects ", "{ reads r.slots, writes r.slots } { r.slots[i].b = true; ", "return r.slots[i].b; } }"]

def rightsUnion : Input (tableRights "w+r") := rights_input (tableRights "w+r")
  cuts [cut1, cut5, cut3, cut4]
  text ["module m { table T count 2 { slot { b : bool, } } impl fn ", "u(r : ptr<normal, w+r> T, i : index into T) -> bool effects ", "{ reads r.slots, writes r.slots } { r.slots[i].b = true; ", "return r.slots[i].b; } }"]

def writeOnly : Input (tableRights "w") := rights_input (tableRights "w")
  cuts [cut1, cut6, cut7, cut4]
  text ["module m { table T count 2 { slot { b : bool, } } impl fn ", "u(r : ptr<normal, w> T, i : index into T) -> bool effects { ", "reads r.slots, writes r.slots } { r.slots[i].b = true; ", "return r.slots[i].b; } }"]

def storeOnly : Input storeOnly := rights_input storeOnly
  cuts [cut1, cut8, cut9]
  text ["module m { table T count 2 { slot { b : bool, } } impl fn ", "u(r : ptr<normal, w> T, i : index into T) effects { writes ", "r.slots } { r.slots[i].b = true; } }"]

def ownAtMarke : Input ownAtMarke := rights_input ownAtMarke
  cuts [cut10, cut11, cut12, cut13, cut14]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> ", "T, i : index into T) -> bool effects { reads r.slots, writes ", "r.slots, borrows Marke } { r.slots[i].b = true; return ", "r.slots[i].b; } }"]

def ownAtMarkeOhneLeiht : Input ownAtMarkeOhneLeiht := rights_input ownAtMarkeOhneLeiht
  cuts [cut10, cut11, cut12, cut15]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> ", "T, i : index into T) -> bool effects { reads r.slots, writes ", "r.slots } { r.slots[i].b = true; return r.slots[i].b; } }"]

def ownAtMarkeFremdLeiht : Input ownAtMarkeFremdLeiht := rights_input ownAtMarkeFremdLeiht
  cuts [cut16, cut17, cut18, cut19, cut20]
  text ["module m { linear type Marke; linear type Fremd; table T ", "count 2 owner Marke { slot { b : bool, } } impl fn u(r : ", "ptr<normal, rw+own@Marke> T, i : index into T) -> bool ", "effects { reads r.slots, writes r.slots, borrows Fremd } { ", "r.slots[i].b = true; return r.slots[i].b; } }"]

def ownerOhneLinear : Input ownerOhneLinear := rights_input ownerOhneLinear
  cuts [cut21, cut22]
  text ["module m { table T count 2 owner Marke { slot { b : bool, } ", "} type Marke = u32; }"]

def bnot1 : Input bnot1 := rights_input bnot1
  cuts [cut23, cut24]
  text ["module m { impl fn f(m : u8) -> u8 { return ~m; } impl fn ", "g(w : u8) -> bool { return (w ^ u8::max) == ~w; } }"]

def bnot_schmal : Input bnot_schmal := rights_input bnot_schmal
  cuts [cut25, cut26]
  text ["module m { impl fn f(x : u8 in 0 .. 15) -> u8 { return ~x; } ", "impl fn k(w : u16 in 0 .. 255) -> u16 { return ~w; } }"]

def bnot_ausdruck : Input bnot_ausdruck := rights_input bnot_ausdruck
  cuts [cut27]
  text ["module m { impl fn f(x : u32) -> u32 { return ~(x + 1); } }"]

def bnot_vorzeichen : Input bnot_vorzeichen := rights_input bnot_vorzeichen
  cuts [cut28]
  text ["module m { impl fn f(x : i32) -> i32 { return ~x; } }"]

def konst_ausdruck : Input konst_ausdruck := rights_input konst_ausdruck
  cuts [cut29, cut30]
  text ["module m { const A : u32 = 6 * 7; const B : u32 = A + 2 * (A ", "^ 3) - (A >> 1); impl fn f() -> u32 { return B; } }"]

def konst_fn : Input konst_fn := rights_input konst_fn
  cuts [cut31, cut32, cut33]
  text ["module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in ", "0 .. 2000 { return n + n; } const C : u32 = doppelt(21); ", "impl fn f() -> u32 { return C; } }"]

def konst_ueberlauf : Input konst_ueberlauf := rights_input konst_ueberlauf
  cuts [cut34, cut35]
  text ["module m { const X : u8 = 200 + 100; impl fn f() -> u8 { ", "return X; } }"]

def konst_negativ : Input konst_negativ := rights_input konst_negativ
  cuts [cut36, cut37]
  text ["module m { const Y : u32 = 3 - 5; impl fn f() -> u32 { ", "return Y; } }"]

def konst_argument : Input konst_argument := rights_input konst_argument
  cuts [cut31, cut38, cut33]
  text ["module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in ", "0 .. 2000 { return n + n; } const C : u32 = doppelt(2000); ", "impl fn f() -> u32 { return C; } }"]

def mintAtMarke : Input mintAtMarke := rights_input mintAtMarke
  cuts [cut10, cut39, cut40, cut41, cut42]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn minter(r : ptr<normal, ", "rw+own@Marke> T, i : index into T) -> bool effects { reads ", "r.slots, writes r.slots, mints Marke } { r.slots[i].b = ", "true; return r.slots[i].b; } }"]

def moveAtMarke : Input moveAtMarke := rights_input moveAtMarke
  cuts [cut10, cut43, cut40, cut44, cut45, cut40, cut46, cut14]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn mover(p : ptr<normal, ", "rw+own@Marke> T, i : index into T) -> bool effects { reads ", "p.slots, writes p.slots, moves Marke } { p.slots[i].b = ", "true; return p.slots[i].b; } impl fn caller(r : ptr<normal, ", "rw+own@Marke> T, i : index into T) -> bool effects { reads ", "r.slots, writes r.slots, moves Marke } { mover(r, i); return ", "r.slots[i].b; } }"]

def moveReasonAtMarke : Input moveReasonAtMarke := rights_input moveReasonAtMarke
  cuts [cut10, cut47, cut48, cut49, cut50, cut51]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } reason G { Weg = 1 \"weg\" exhaustive } ", "impl fn mover(p : ptr<normal, rw+own@Marke> T, i : index ", "into T) -> bool or G effects { reads p.slots, writes ", "p.slots, moves Marke } { p.slots[i].b = true; return G::Weg; ", "} }"]

def mintTwice : Input mintTwice := rights_input mintTwice
  cuts [cut10, cut52, cut53, cut54]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn a() -> bool effects { mints ", "Marke } { return true; } impl fn b() -> bool effects { mints ", "Marke } { return true; } }"]

def mintFremd : Input mintFremd := rights_input mintFremd
  cuts [cut16, cut55, cut56]
  text ["module m { linear type Marke; linear type Fremd; table T ", "count 2 owner Marke { slot { b : bool, } } impl fn a() -> ", "bool effects { mints Fremd } { return true; } }"]

def moveFremd : Input moveFremd := rights_input moveFremd
  cuts [cut16, cut55, cut57]
  text ["module m { linear type Marke; linear type Fremd; table T ", "count 2 owner Marke { slot { b : bool, } } impl fn a() -> ", "bool effects { moves Fremd } { return true; } }"]

def moveBorrowed : Input moveBorrowed := rights_input moveBorrowed
  cuts [cut10, cut58, cut59]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn a() -> bool effects { borrows ", "Marke, moves Marke } { return true; } }"]

def moveDropped : Input moveDropped := rights_input moveDropped
  cuts [cut10, cut60, cut61, cut62]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn mover(i : index into T) -> bool ", "effects { moves Marke } { return true; } impl fn caller() { ", "mover(0); } }"]

def terminalMoveRetires : Input terminalMoveRetires := rights_input terminalMoveRetires
  cuts [cut10, cut63, cut64, cut65]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn finish() effects { consumes ", "Marke } { retires Marke; } impl fn main() -> u8 effects { ", "consumes Marke } { finish(); return 23; } }"]

def terminalMoveDropped : Input (terminalMoveSource "") := rights_input (terminalMoveSource "")
  cuts [cut10, cut63, cut66, cut67]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn finish() effects { consumes ", "Marke } {  } impl fn main() -> u8 effects { consumes Marke } ", "{ finish(); return 23; } }"]

def borrowedRetire : Input borrowedRetire := rights_input borrowedRetire
  cuts [cut10, cut68, cut69]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn f() effects { borrows Marke } { ", "retires Marke; } }"]

def unheldRetire : Input unheldRetire := rights_input unheldRetire
  cuts [cut70, cut71]
  text ["module m { linear type Marke; impl fn f() { retires Marke; } ", "}"]

def repeatedRetire : Input (terminalMoveSource "retires Marke; retires Marke;") := rights_input (terminalMoveSource "retires Marke; retires Marke;")
  cuts [cut10, cut63, cut72, cut73]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn finish() effects { consumes ", "Marke } { retires Marke; retires Marke; } impl fn main() -> ", "u8 effects { consumes Marke } { finish(); return 23; } }"]

def ordinaryRetire : Input ordinaryRetire := rights_input ordinaryRetire
  cuts [cut74, cut75, cut76]
  text ["module m { linear type Duty; impl fn gate() effects { ", "consumes Duty } { retires Duty; } impl fn caller() effects { ", "consumes Duty } { gate(); } }"]

def handbackRetire : Input handbackRetire := rights_input handbackRetire
  cuts [cut10, cut77, cut69]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn f() effects { moves Marke } { ", "retires Marke; } }"]

def terminalReasonRetire : Input terminalReasonRetire := rights_input terminalReasonRetire
  cuts [cut10, cut78, cut79, cut80]
  text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } reason R { Gone = 1 \"gone\" exhaustive } ", "impl fn f() -> bool or R effects { consumes Marke } { ", "retires Marke; return R::Gone; } }"]

def stagedOwner : Input stagedOwner := rights_input stagedOwner
  cuts [cut81, cut82, cut83, cut84]
  text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances warm -> hot; retires Phase; } }"]

def stagedCounts : Input "module m { linear type Plain; linear type Phase order { cold, warm, hot }; linear type Pair order { first, second }; impl fn f() { } }" := rights_input "module m { linear type Plain; linear type Phase order { cold, warm, hot }; linear type Pair order { first, second }; impl fn f() { } }"
  cuts [cut85, cut86, cut87]
  text ["module m { linear type Plain; linear type Phase order { ", "cold, warm, hot }; linear type Pair order { first, second }; ", "impl fn f() { } }"]

def stagedOrdinary : Input stagedOrdinary := rights_input stagedOrdinary
  cuts [cut88, cut83, cut84]
  text ["module m { linear type Phase order { cold, warm, hot }; impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances warm -> hot; retires Phase; } }"]

def stagedLast : Input (stagedOwnerSource "advances cold -> warm; advances warm -> hot; advances hot -> cold;") := rights_input (stagedOwnerSource "advances cold -> warm; advances warm -> hot; advances hot -> cold;")
  cuts [cut81, cut82, cut83, cut89]
  text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances warm -> hot; advances hot -> cold; } }"]

def stagedSkip : Input (stagedOwnerSource "advances cold -> hot;") := rights_input (stagedOwnerSource "advances cold -> hot;")
  cuts [cut81, cut82, cut83, cut90]
  text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "hot; } }"]

def stagedBackward : Input (stagedOwnerSource "advances cold -> warm; advances warm -> cold;") := rights_input (stagedOwnerSource "advances cold -> warm; advances warm -> cold;")
  cuts [cut81, cut82, cut83, cut91]
  text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances warm -> cold; } }"]

def stagedWrongInput : Input (stagedOwnerSource "advances warm -> hot;") := rights_input (stagedOwnerSource "advances warm -> hot;")
  cuts [cut81, cut82, cut92, cut90]
  text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances warm -> ", "hot; } }"]

def stagedRepeated : Input (stagedOwnerSource "advances cold -> warm; advances cold -> warm;") := rights_input (stagedOwnerSource "advances cold -> warm; advances cold -> warm;")
  cuts [cut81, cut82, cut83, cut93]
  text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances cold -> warm; } }"]

def stagedUnknown : Input (stagedOwnerSource "advances missing -> warm;") := rights_input (stagedOwnerSource "advances missing -> warm;")
  cuts [cut81, cut82, cut94, cut95]
  text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances missing -> ", "warm; } }"]

def stagedBorrowed : Input stagedBorrowed := rights_input stagedBorrowed
  cuts [cut96, cut97, cut98]
  text ["module m { linear type Phase order { cold, warm, hot }; ", "table T count 2 owner Phase { slot { b : bool, } } impl fn ", "f() effects { borrows Phase } { advances cold -> warm; } }"]

def stagedAmbiguous : Input stagedAmbiguous := rights_input stagedAmbiguous
  cuts [cut96, cut99, cut100]
  text ["module m { linear type Phase order { cold, warm, hot }; ", "linear type Other order { cold, warm }; impl fn f() effects ", "{ consumes Phase } { advances cold -> warm; } }"]

def stagedDuplicate : Input stagedDuplicate := rights_input stagedDuplicate
  cuts [cut101, cut102]
  text ["module m { linear type Phase order { cold, cold, hot }; impl ", "fn f() { } }"]

end Inputs
end Gabbro.Grammatik.Parser.UebersetzeProben11.Phases

