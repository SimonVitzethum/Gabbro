module
public import Grammatik.Parser.Elab.Proben.RightsConstants.Data
public import Grammatik.Parser.Elab.Proben.RightsConstants.Fragments
public import Grammatik.Parser.Elab.Proben.RightsConstants.Bounds
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

theorem steps_bound (pieces : List Chunk) :
    pieces.all (fun piece => decide (piece.steps ≤ piece.characters.length)) = true →
      steps pieces ≤ (Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning.characters pieces).length := by
  induction pieces with
  | nil => intro _; exact Nat.le_refl _
  | cons piece pieces ih =>
    intro bounded
    simp only [List.all_cons, Bool.and_eq_true] at bounded
    simp only [steps, Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning.characters,
      List.flatMap_cons, List.length_append]
    exact Nat.add_le_add (of_decide_eq_true bounded.1) (ih bounded.2)

-- Infer the token data from the real short lexer result. The final certificate
-- checks this exact fragment again with an arbitrary scanner continuation.

scoped macro "rights_input " source:term " with_cuts " "[" cuts:ident,* "]"
    " with_text " "[" fragments:str,* "]" : term => do
  let text := fragments.getElems.foldl (fun text fragment => text ++ fragment.getString) ""
  let letters : Array (Lean.TSyntax `term) := text.toList.toArray.map fun char =>
    ⟨(Lean.Syntax.mkCharLit char).raw⟩
  let mut bounded : Lean.TSyntax `term ← `(Eq.refl true)
  for piece in cuts.getElems.reverse do
    let proof : Lean.TSyntax `term :=
      ⟨(Lean.mkIdentFrom piece (piece.getId.appendAfter "_bounded")).raw⟩
    bounded ← `(Bool.and_eq_true_iff.mpr ⟨$proof, $bounded⟩)
  `(show Input $source from by
    let pieces : List Chunk := [$cuts,*]
    have charsEq : Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning.characters pieces =
        ([$letters,*] : List Char) := by rfl
    refine Input.of_chunks (source := $source) pieces ?text ?room
    case text =>
      rw [charsEq] <;> cbv
    case room =>
      exact Nat.le_trans (steps_bound pieces $bounded) (Nat.le_succ _))

open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
namespace Inputs


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
