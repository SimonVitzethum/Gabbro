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

def Input.of_chunks {source : String} {spellings : List String} (pieces : List Chunk)
    (certificate : ChunkCertificate pieces spellings)
    (text : source = String.join spellings) : Input source :=
  ⟨Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning.characters pieces, Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning.tokens pieces,
    text.trans certificate.joined_text.symm, lex_chunks pieces certificate.room⟩

-- Give the actual chunk list, fragment spellings and proofs their own declarations
-- before constructing Input. Data stays transparent; no large local lets need
-- to be abstracted or substituted while the final constructor is checked.

scoped macro "rights_input " name:ident " : " source:term
    " with_cuts " "[" cuts:ident,* "]" " with_text " "[" fragments:str,* "]" : command => do
  unless cuts.getElems.size == fragments.getElems.size do
    Lean.Macro.throwError "each scanner cut needs its exact original spelling"
  let chunkName := Lean.mkIdentFrom name (name.getId.appendAfter "_chunks")
  let spellingsName := Lean.mkIdentFrom name (name.getId.appendAfter "_spellings")
  let certificateName := Lean.mkIdentFrom name (name.getId.appendAfter "_certificate")
  let sourceName := Lean.mkIdentFrom name (name.getId.appendAfter "_source_eq")
  let mut pieces : Lean.TSyntax `term ← `(([] : List Chunk))
  let mut spellings : Lean.TSyntax `term ← `(([] : List String))
  let mut certificate : Lean.TSyntax `term ← `(ChunkCertificate.empty)
  for (cutName, fragment) in (cuts.getElems.zip fragments.getElems).toList.reverse do
    let piece : Lean.TSyntax `term := ⟨cutName.raw⟩
    let literal : Lean.TSyntax `term := ⟨fragment.raw⟩
    let decoded : Lean.TSyntax `term :=
      ⟨(Lean.mkIdentFrom cutName (cutName.getId.appendAfter "_text")).raw⟩
    let bounded : Lean.TSyntax `term :=
      ⟨(Lean.mkIdentFrom cutName (cutName.getId.appendAfter "_bounded")).raw⟩
    certificate ← `(ChunkCertificate.cons (piece := $piece) (pieces := $pieces)
      (front := $literal) (back := $spellings) $decoded $bounded $certificate)
    pieces ← `($piece :: $pieces)
    spellings ← `($literal :: $spellings)
  let chunks : Lean.TSyntax `command ← `(command|
    def $chunkName : List Chunk := [$cuts,*])
  let spelled : Lean.TSyntax `command ← `(command|
    def $spellingsName : List String := $spellings)
  let certified : Lean.TSyntax `command ← `(command|
    theorem $certificateName : ChunkCertificate $chunkName $spellingsName := by
      change ChunkCertificate $pieces $spellings
      exact $certificate)
  let original : Lean.TSyntax `command ← `(command|
    theorem $sourceName : $source = String.join $spellingsName := by cbv)
  let input : Lean.TSyntax `command ← `(command|
    def $name : Input $source :=
      Input.of_chunks (source := $source) $chunkName $certificateName $sourceName)
  return ⟨Lean.mkNullNode #[chunks, spelled, certified, original, input]⟩

open scoped Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
namespace Inputs


rights_input advanceBare : "module m { impl fn f() { advances setup -> live; } }"
  with_cuts [cut0]
  with_text ["module m { impl fn f() { advances setup -> live; } }"]

rights_input own1 : Gabbro.Grammatik.Parser.UebersetzeProben11.own1
  with_cuts [cut1, cut2, cut3, cut4]
  with_text ["module m { table T count 2 { slot { b : bool, } } impl fn ", "u(r : ptr<normal, own> T, i : index into T) -> bool effects ", "{ reads r.slots, writes r.slots } { r.slots[i].b = true; ", "return r.slots[i].b; } }"]

rights_input rightsUnion : (Gabbro.Grammatik.Parser.UebersetzeProben11.tableRights "w+r")
  with_cuts [cut1, cut5, cut3, cut4]
  with_text ["module m { table T count 2 { slot { b : bool, } } impl fn ", "u(r : ptr<normal, w+r> T, i : index into T) -> bool effects ", "{ reads r.slots, writes r.slots } { r.slots[i].b = true; ", "return r.slots[i].b; } }"]

rights_input writeOnly : (Gabbro.Grammatik.Parser.UebersetzeProben11.tableRights "w")
  with_cuts [cut1, cut6, cut7, cut4]
  with_text ["module m { table T count 2 { slot { b : bool, } } impl fn ", "u(r : ptr<normal, w> T, i : index into T) -> bool effects { ", "reads r.slots, writes r.slots } { r.slots[i].b = true; ", "return r.slots[i].b; } }"]

rights_input storeOnly : Gabbro.Grammatik.Parser.UebersetzeProben11.storeOnly
  with_cuts [cut1, cut8, cut9]
  with_text ["module m { table T count 2 { slot { b : bool, } } impl fn ", "u(r : ptr<normal, w> T, i : index into T) effects { writes ", "r.slots } { r.slots[i].b = true; } }"]

rights_input ownAtMarke : Gabbro.Grammatik.Parser.UebersetzeProben11.ownAtMarke
  with_cuts [cut10, cut11, cut12, cut13, cut14]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> ", "T, i : index into T) -> bool effects { reads r.slots, writes ", "r.slots, borrows Marke } { r.slots[i].b = true; return ", "r.slots[i].b; } }"]

rights_input ownAtMarkeOhneLeiht : Gabbro.Grammatik.Parser.UebersetzeProben11.ownAtMarkeOhneLeiht
  with_cuts [cut10, cut11, cut12, cut15]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> ", "T, i : index into T) -> bool effects { reads r.slots, writes ", "r.slots } { r.slots[i].b = true; return r.slots[i].b; } }"]

rights_input ownAtMarkeFremdLeiht : Gabbro.Grammatik.Parser.UebersetzeProben11.ownAtMarkeFremdLeiht
  with_cuts [cut16, cut17, cut18, cut19, cut20]
  with_text ["module m { linear type Marke; linear type Fremd; table T ", "count 2 owner Marke { slot { b : bool, } } impl fn u(r : ", "ptr<normal, rw+own@Marke> T, i : index into T) -> bool ", "effects { reads r.slots, writes r.slots, borrows Fremd } { ", "r.slots[i].b = true; return r.slots[i].b; } }"]

rights_input ownerOhneLinear : Gabbro.Grammatik.Parser.UebersetzeProben11.ownerOhneLinear
  with_cuts [cut21, cut22]
  with_text ["module m { table T count 2 owner Marke { slot { b : bool, } ", "} type Marke = u32; }"]

rights_input bnot1 : Gabbro.Grammatik.Parser.UebersetzeProben11.bnot1
  with_cuts [cut23, cut24]
  with_text ["module m { impl fn f(m : u8) -> u8 { return ~m; } impl fn ", "g(w : u8) -> bool { return (w ^ u8::max) == ~w; } }"]

rights_input bnot_schmal : Gabbro.Grammatik.Parser.UebersetzeProben11.bnot_schmal
  with_cuts [cut25, cut26]
  with_text ["module m { impl fn f(x : u8 in 0 .. 15) -> u8 { return ~x; } ", "impl fn k(w : u16 in 0 .. 255) -> u16 { return ~w; } }"]

rights_input bnot_ausdruck : Gabbro.Grammatik.Parser.UebersetzeProben11.bnot_ausdruck
  with_cuts [cut27]
  with_text ["module m { impl fn f(x : u32) -> u32 { return ~(x + 1); } }"]

rights_input bnot_vorzeichen : Gabbro.Grammatik.Parser.UebersetzeProben11.bnot_vorzeichen
  with_cuts [cut28]
  with_text ["module m { impl fn f(x : i32) -> i32 { return ~x; } }"]

rights_input konst_ausdruck : Gabbro.Grammatik.Parser.UebersetzeProben11.konst_ausdruck
  with_cuts [cut29, cut30]
  with_text ["module m { const A : u32 = 6 * 7; const B : u32 = A + 2 * (A ", "^ 3) - (A >> 1); impl fn f() -> u32 { return B; } }"]

rights_input konst_fn : Gabbro.Grammatik.Parser.UebersetzeProben11.konst_fn
  with_cuts [cut31, cut32, cut33]
  with_text ["module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in ", "0 .. 2000 { return n + n; } const C : u32 = doppelt(21); ", "impl fn f() -> u32 { return C; } }"]

rights_input konst_ueberlauf : Gabbro.Grammatik.Parser.UebersetzeProben11.konst_ueberlauf
  with_cuts [cut34, cut35]
  with_text ["module m { const X : u8 = 200 + 100; impl fn f() -> u8 { ", "return X; } }"]

rights_input konst_negativ : Gabbro.Grammatik.Parser.UebersetzeProben11.konst_negativ
  with_cuts [cut36, cut37]
  with_text ["module m { const Y : u32 = 3 - 5; impl fn f() -> u32 { ", "return Y; } }"]

rights_input konst_argument : Gabbro.Grammatik.Parser.UebersetzeProben11.konst_argument
  with_cuts [cut31, cut38, cut33]
  with_text ["module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in ", "0 .. 2000 { return n + n; } const C : u32 = doppelt(2000); ", "impl fn f() -> u32 { return C; } }"]

rights_input mintAtMarke : Gabbro.Grammatik.Parser.UebersetzeProben11.mintAtMarke
  with_cuts [cut10, cut39, cut40, cut41, cut42]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn minter(r : ptr<normal, ", "rw+own@Marke> T, i : index into T) -> bool effects { reads ", "r.slots, writes r.slots, mints Marke } { r.slots[i].b = ", "true; return r.slots[i].b; } }"]

rights_input moveAtMarke : Gabbro.Grammatik.Parser.UebersetzeProben11.moveAtMarke
  with_cuts [cut10, cut43, cut40, cut44, cut45, cut40, cut46, cut14]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn mover(p : ptr<normal, ", "rw+own@Marke> T, i : index into T) -> bool effects { reads ", "p.slots, writes p.slots, moves Marke } { p.slots[i].b = ", "true; return p.slots[i].b; } impl fn caller(r : ptr<normal, ", "rw+own@Marke> T, i : index into T) -> bool effects { reads ", "r.slots, writes r.slots, moves Marke } { mover(r, i); return ", "r.slots[i].b; } }"]

rights_input moveReasonAtMarke : Gabbro.Grammatik.Parser.UebersetzeProben11.moveReasonAtMarke
  with_cuts [cut10, cut47, cut48, cut49, cut50, cut51]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } reason G { Weg = 1 \"weg\" exhaustive } ", "impl fn mover(p : ptr<normal, rw+own@Marke> T, i : index ", "into T) -> bool or G effects { reads p.slots, writes ", "p.slots, moves Marke } { p.slots[i].b = true; return G::Weg; ", "} }"]

rights_input mintTwice : Gabbro.Grammatik.Parser.UebersetzeProben11.mintTwice
  with_cuts [cut10, cut52, cut53, cut54]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn a() -> bool effects { mints ", "Marke } { return true; } impl fn b() -> bool effects { mints ", "Marke } { return true; } }"]

rights_input mintFremd : Gabbro.Grammatik.Parser.UebersetzeProben11.mintFremd
  with_cuts [cut16, cut55, cut56]
  with_text ["module m { linear type Marke; linear type Fremd; table T ", "count 2 owner Marke { slot { b : bool, } } impl fn a() -> ", "bool effects { mints Fremd } { return true; } }"]

rights_input moveFremd : Gabbro.Grammatik.Parser.UebersetzeProben11.moveFremd
  with_cuts [cut16, cut55, cut57]
  with_text ["module m { linear type Marke; linear type Fremd; table T ", "count 2 owner Marke { slot { b : bool, } } impl fn a() -> ", "bool effects { moves Fremd } { return true; } }"]

rights_input moveBorrowed : Gabbro.Grammatik.Parser.UebersetzeProben11.moveBorrowed
  with_cuts [cut10, cut58, cut59]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn a() -> bool effects { borrows ", "Marke, moves Marke } { return true; } }"]

rights_input moveDropped : Gabbro.Grammatik.Parser.UebersetzeProben11.moveDropped
  with_cuts [cut10, cut60, cut61, cut62]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn mover(i : index into T) -> bool ", "effects { moves Marke } { return true; } impl fn caller() { ", "mover(0); } }"]

rights_input terminalMoveRetires : Gabbro.Grammatik.Parser.UebersetzeProben11.terminalMoveRetires
  with_cuts [cut10, cut63, cut64, cut65]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn finish() effects { consumes ", "Marke } { retires Marke; } impl fn main() -> u8 effects { ", "consumes Marke } { finish(); return 23; } }"]

rights_input terminalMoveDropped : (Gabbro.Grammatik.Parser.UebersetzeProben11.terminalMoveSource "")
  with_cuts [cut10, cut63, cut66, cut67]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn finish() effects { consumes ", "Marke } {  } impl fn main() -> u8 effects { consumes Marke } ", "{ finish(); return 23; } }"]

rights_input borrowedRetire : Gabbro.Grammatik.Parser.UebersetzeProben11.borrowedRetire
  with_cuts [cut10, cut68, cut69]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn f() effects { borrows Marke } { ", "retires Marke; } }"]

rights_input unheldRetire : Gabbro.Grammatik.Parser.UebersetzeProben11.unheldRetire
  with_cuts [cut70, cut71]
  with_text ["module m { linear type Marke; impl fn f() { retires Marke; } ", "}"]

rights_input repeatedRetire : (Gabbro.Grammatik.Parser.UebersetzeProben11.terminalMoveSource "retires Marke; retires Marke;")
  with_cuts [cut10, cut63, cut72, cut73]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn finish() effects { consumes ", "Marke } { retires Marke; retires Marke; } impl fn main() -> ", "u8 effects { consumes Marke } { finish(); return 23; } }"]

rights_input ordinaryRetire : Gabbro.Grammatik.Parser.UebersetzeProben11.ordinaryRetire
  with_cuts [cut74, cut75, cut76]
  with_text ["module m { linear type Duty; impl fn gate() effects { ", "consumes Duty } { retires Duty; } impl fn caller() effects { ", "consumes Duty } { gate(); } }"]

rights_input handbackRetire : Gabbro.Grammatik.Parser.UebersetzeProben11.handbackRetire
  with_cuts [cut10, cut77, cut69]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } impl fn f() effects { moves Marke } { ", "retires Marke; } }"]

rights_input terminalReasonRetire : Gabbro.Grammatik.Parser.UebersetzeProben11.terminalReasonRetire
  with_cuts [cut10, cut78, cut79, cut80]
  with_text ["module m { linear type Marke; table T count 2 owner Marke { ", "slot { b : bool, } } reason R { Gone = 1 \"gone\" exhaustive } ", "impl fn f() -> bool or R effects { consumes Marke } { ", "retires Marke; return R::Gone; } }"]

rights_input stagedOwner : Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwner
  with_cuts [cut81, cut82, cut83, cut84]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances warm -> hot; retires Phase; } }"]

rights_input stagedCounts : "module m { linear type Plain; linear type Phase order { cold, warm, hot }; linear type Pair order { first, second }; impl fn f() { } }"
  with_cuts [cut85, cut86, cut87]
  with_text ["module m { linear type Plain; linear type Phase order { ", "cold, warm, hot }; linear type Pair order { first, second }; ", "impl fn f() { } }"]

rights_input stagedOrdinary : Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOrdinary
  with_cuts [cut88, cut83, cut84]
  with_text ["module m { linear type Phase order { cold, warm, hot }; impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances warm -> hot; retires Phase; } }"]

rights_input stagedLast : (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances cold -> warm; advances warm -> hot; advances hot -> cold;")
  with_cuts [cut81, cut82, cut83, cut89]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances warm -> hot; advances hot -> cold; } }"]

rights_input stagedSkip : (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances cold -> hot;")
  with_cuts [cut81, cut82, cut83, cut90]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "hot; } }"]

rights_input stagedBackward : (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances cold -> warm; advances warm -> cold;")
  with_cuts [cut81, cut82, cut83, cut91]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances warm -> cold; } }"]

rights_input stagedWrongInput : (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances warm -> hot;")
  with_cuts [cut81, cut82, cut92, cut90]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances warm -> ", "hot; } }"]

rights_input stagedRepeated : (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances cold -> warm; advances cold -> warm;")
  with_cuts [cut81, cut82, cut83, cut93]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances cold -> ", "warm; advances cold -> warm; } }"]

rights_input stagedUnknown : (Gabbro.Grammatik.Parser.UebersetzeProben11.stagedOwnerSource "advances missing -> warm;")
  with_cuts [cut81, cut82, cut94, cut95]
  with_text ["module m { linear ghost type Phase order { cold, warm, hot ", "}; table T count 2 owner Phase { slot { b : bool, } } impl ", "fn finish() effects { consumes Phase } { advances missing -> ", "warm; } }"]

rights_input stagedBorrowed : Gabbro.Grammatik.Parser.UebersetzeProben11.stagedBorrowed
  with_cuts [cut96, cut97, cut98]
  with_text ["module m { linear type Phase order { cold, warm, hot }; ", "table T count 2 owner Phase { slot { b : bool, } } impl fn ", "f() effects { borrows Phase } { advances cold -> warm; } }"]

rights_input stagedAmbiguous : Gabbro.Grammatik.Parser.UebersetzeProben11.stagedAmbiguous
  with_cuts [cut96, cut99, cut100]
  with_text ["module m { linear type Phase order { cold, warm, hot }; ", "linear type Other order { cold, warm }; impl fn f() effects ", "{ consumes Phase } { advances cold -> warm; } }"]

rights_input stagedDuplicate : Gabbro.Grammatik.Parser.UebersetzeProben11.stagedDuplicate
  with_cuts [cut101, cut102]
  with_text ["module m { linear type Phase order { cold, cold, hot }; impl ", "fn f() { } }"]

end Inputs
end Gabbro.Grammatik.Parser.UebersetzeProben11.Phases
