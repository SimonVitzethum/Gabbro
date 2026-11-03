/-
  File:      Grammatik/Parser/Elab/UebersetzeProben11.lean
  Subject:   Walls 4 and 5: `own`/`~p` and constants (split from `UebersetzeProben`: the kernel probes of one file share one memory budget).
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben11

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeProben (stufe)

set_option maxRecDepth 100000

/-! ## Wall 4: `own` pointers and the complement `~p` over the declared storage width -/

/-- One table program with the source rights supplied at its capability parameter. -/
def tableRights (rights : String) : String :=
  "module m { table T count 2 { slot { b : bool, } } impl fn u(r : ptr<normal, " ++ rights ++
  "> T, i : index into T) -> bool effects { reads r.slots, writes r.slots } { r.slots[i].b = true; return r.slots[i].b; } }"

/-- Ownership cannot be erased into ordinary read/write permission. This source declares no owner mark. -/
def own1 : String := tableRights "own"
theorem own1_refused : stufe own1 = "elab: pointer rights without checked data/owner form: own" := by
  decide +kernel

/-- Both explicit read and write rights reach the existing checked table operations. -/
theorem rights_union_ok : stufe (tableRights "w+r") = "OK" := by decide +kernel

/-- A write-only pointer can store, but its subsequent read is refused. -/
theorem write_only_refused :
    stufe (tableRights "w") = "elab: read through pointer without read right" := by
  decide +kernel

/-- Write-only source reaches the ordinary checked table-store lowering. -/
def storeOnly : String :=
  "module m { table T count 2 { slot { b : bool, } } impl fn u(r : ptr<normal, w> T, i : index into T) effects { writes r.slots } { r.slots[i].b = true; } }"

theorem write_only_store_ok : stufe storeOnly = "OK" := by decide +kernel

/-- C12: a function borrowing an owner-guarded table reads and writes through
    its `own@Marke` capability and returns the mark: the `borrows Marke` loan
    holds the mark for the call (`OwnerFlow.loans`), `thruOwn`/`assignThruOwn`
    lower on the underlying table exactly like `thru`/`assignThru`, and the
    loan comes back at return (`Vertrag.ende`). -/
def ownAtMarke : String :=
  "module m { linear type Marke; table T count 2 owner Marke { slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> T, i : index into T) -> bool effects { reads r.slots, writes r.slots, borrows Marke } { r.slots[i].b = true; return r.slots[i].b; } }"
theorem ownAtMarke_borrow_ok : stufe ownAtMarke = "OK" := by
  decide +kernel

/-- C12: the same access without the loan is refused: the owner guard is not
    held, so the lowering finds no guard (`darf` over the `.inr` entry). -/
def ownAtMarkeOhneLeiht : String :=
  "module m { linear type Marke; table T count 2 owner Marke { slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> T, i : index into T) -> bool effects { reads r.slots, writes r.slots } { r.slots[i].b = true; return r.slots[i].b; } }"
theorem ownAtMarke_ohneLeiht_refused :
    stufe ownAtMarkeOhneLeiht = "lower: access without held guard" := by
  decide +kernel

/-- C12: borrowing a mark no table owns is refused by name: a call-scoped
    loan is only an owner handback, never a mint. -/
def ownAtMarkeFremdLeiht : String :=
  "module m { linear type Marke; linear type Fremd; table T count 2 owner Marke { slot { b : bool, } } impl fn u(r : ptr<normal, rw+own@Marke> T, i : index into T) -> bool effects { reads r.slots, writes r.slots, borrows Fremd } { r.slots[i].b = true; return r.slots[i].b; } }"
theorem ownAtMarke_fremdLeiht_refused :
    stufe ownAtMarkeFremdLeiht = "elab: loan without owner: Fremd" := by
  decide +kernel

/-- C12: a table `owner M` where `M` is no declared linear mark is refused by name.
    The guard would be unholdable (no mark to hold), so the front end refuses it
    instead of elaborating it. Mirrors gift probe 0934 (Rust D265). -/
def ownerOhneLinear : String :=
  "module m { table T count 2 owner Marke { slot { b : bool, } } type Marke = u32; }"
theorem ownerOhneLinear_refused : stufe ownerOhneLinear = "elab: owner without declared linear mark: Marke" := by
  decide +kernel

/-- WITNESS (`beispiele/62`, `61`): `~p` is `p ^ (2^w - 1)` over the parameter's declared storage width. -/
def bnot1 : String :=
  "module m { impl fn f(m : u8) -> u8 { return ~m; } impl fn g(w : u8) -> bool { return (w ^ u8::max) == ~w; } }"
theorem bnot1_ok : stufe bnot1 = "OK" := by decide +kernel

/-- WITNESS: the width is the DECLARED word's, not the range's: `u8 in 0 .. 15` is stored in 8 bits, so
    its complement is `255 - x` (`beispiele/61`, `hohes_nibble`), and `u16 in 0 .. 255` in 16. -/
def bnot_schmal : String :=
  "module m { impl fn f(x : u8 in 0 .. 15) -> u8 { return ~x; } impl fn k(w : u16 in 0 .. 255) -> u16 { return ~w; } }"
theorem bnot_schmal_ok : stufe bnot_schmal = "OK" := by decide +kernel

/-- PLANTED DEFECT: the complement of an EXPRESSION has no known width here -- it is refused, not
    guessed from a range (a range would give `15 - x` for `0 .. 15`, where the C says `255 - x`). -/
def bnot_ausdruck : String :=
  "module m { impl fn f(x : u32) -> u32 { return ~(x + 1); } }"
theorem bnot_ausdruck_refused : stufe bnot_ausdruck = "elab: value without G form" := by decide +kernel

/-- PLANTED DEFECT: the complement of a signed parameter (its width has no unsigned reading). -/
def bnot_vorzeichen : String :=
  "module m { impl fn f(x : i32) -> i32 { return ~x; } }"
theorem bnot_vorzeichen_refused :
    stufe bnot_vorzeichen = "elab: complement of unknown width" := by decide +kernel

/-! ## Wall 5: compile-time constants -- expressions and `const fn` calls -/

/-- WITNESS (`beispiele/93`, shortened): a constant computed from earlier constants with `+ - * ^ >>`. -/
def konst_ausdruck : String :=
  "module m { const A : u32 = 6 * 7; const B : u32 = A + 2 * (A ^ 3) - (A >> 1); impl fn f() -> u32 { return B; } }"
theorem konst_ausdruck_ok : stufe konst_ausdruck = "OK" := by decide +kernel

/-- WITNESS: a constant computed by a `const fn` call (arguments checked against the parameter's range). -/
def konst_fn : String :=
  "module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in 0 .. 2000 { return n + n; } const C : u32 = doppelt(21); impl fn f() -> u32 { return C; } }"
theorem konst_fn_ok : stufe konst_fn = "OK" := by decide +kernel

/-- PLANTED DEFECT: an intermediate value outside the declared type (`200 + 100` in a `u8`): the emitted C
    would wrap, the exact value would not -- the constant is UNKNOWN, so its use is refused. -/
def konst_ueberlauf : String :=
  "module m { const X : u8 = 200 + 100; impl fn f() -> u8 { return X; } }"
theorem konst_ueberlauf_refused : stufe konst_ueberlauf = "elab: name unknown: X" := by decide +kernel

/-- PLANTED DEFECT: a negative intermediate in an unsigned constant. -/
def konst_negativ : String :=
  "module m { const Y : u32 = 3 - 5; impl fn f() -> u32 { return Y; } }"
theorem konst_negativ_refused : stufe konst_negativ = "elab: name unknown: Y" := by decide +kernel

/-- PLANTED DEFECT: an argument outside the `const fn` parameter's range. -/
def konst_argument : String :=
  "module m { const fn doppelt(n : u32 in 0 .. 1000) -> u32 in 0 .. 2000 { return n + n; } const C : u32 = doppelt(2000); impl fn f() -> u32 { return C; } }"
theorem konst_argument_refused : stufe konst_argument = "elab: name unknown: C" := by decide +kernel

/-! ## C09: owner mint and linear handoff -/

/-- C09: the minter holds its fresh owner from the start frame and reads and
    writes through it: `mints Marke` is the checked `OwnerFlow.mints` output --
    held at entry (`anfang`), returned (`ende`), never ordinary production. -/
def mintAtMarke : String :=
  "module m { linear type Marke; table T count 2 owner Marke { slot { b : bool, } } impl fn minter(r : ptr<normal, rw+own@Marke> T, i : index into T) -> bool effects { reads r.slots, writes r.slots, mints Marke } { r.slots[i].b = true; return r.slots[i].b; } }"
theorem mintAtMarke_ok : stufe mintAtMarke = "OK" := by
  decide +kernel

/-- C09: a linear handoff through a call: the caller holds the mark, the
    callee receives the same nominal identity for the call and hands it back
    on return (`moves Marke` is the `OwnerMove` handback). The capability rides
    a variable, as a fresh `&T` has no owned form. -/
def moveAtMarke : String :=
  "module m { linear type Marke; table T count 2 owner Marke { slot { b : bool, } } impl fn mover(p : ptr<normal, rw+own@Marke> T, i : index into T) -> bool effects { reads p.slots, writes p.slots, moves Marke } { p.slots[i].b = true; return p.slots[i].b; } impl fn caller(r : ptr<normal, rw+own@Marke> T, i : index into T) -> bool effects { reads r.slots, writes r.slots, moves Marke } { mover(r, i); return r.slots[i].b; } }"
theorem moveAtMarke_ok : stufe moveAtMarke = "OK" := by
  decide +kernel

/-- C09: the handed-back mark comes back on the reason channel too: the
    reason return balances against the same `ende`, so the moved output is
    received on either channel. -/
def moveReasonAtMarke : String :=
  "module m { linear type Marke; table T count 2 owner Marke { slot { b : bool, } } reason G { Weg = 1 \"weg\" exhaustive } impl fn mover(p : ptr<normal, rw+own@Marke> T, i : index into T) -> bool or G effects { reads p.slots, writes p.slots, moves Marke } { p.slots[i].b = true; return G::Weg; } }"
theorem moveReasonAtMarke_ok : stufe moveReasonAtMarke = "OK" := by
  decide +kernel

/-- C09: the second mint of the same instance is refused: one-shot mint
    authority per region instance. -/
def mintTwice : String :=
  "module m { linear type Marke; table T count 2 owner Marke { slot { b : bool, } } impl fn a() -> bool effects { mints Marke } { return true; } impl fn b() -> bool effects { mints Marke } { return true; } }"
theorem mintTwice_refused : stufe mintTwice = "elab: duplicate mint: Marke" := by
  decide +kernel

/-- C09: minting a mark no table owns is refused: a mint is only an owner
    handback from a declared owner, never a creation from nothing. -/
def mintFremd : String :=
  "module m { linear type Marke; linear type Fremd; table T count 2 owner Marke { slot { b : bool, } } impl fn a() -> bool effects { mints Fremd } { return true; } }"
theorem mintFremd_refused : stufe mintFremd = "elab: mint without owner: Fremd" := by
  decide +kernel

/-- C09: moving a mark no table owns is refused, like the loan twin. -/
def moveFremd : String :=
  "module m { linear type Marke; linear type Fremd; table T count 2 owner Marke { slot { b : bool, } } impl fn a() -> bool effects { moves Fremd } { return true; } }"
theorem moveFremd_refused : stufe moveFremd = "elab: move without owner: Fremd" := by
  decide +kernel

/-- C09: a mark both borrowed and moved is refused: one occurrence per owner
    identity across stages. -/
def moveBorrowed : String :=
  "module m { linear type Marke; table T count 2 owner Marke { slot { b : bool, } } impl fn a() -> bool effects { borrows Marke, moves Marke } { return true; } }"
theorem moveBorrowed_refused :
    stufe moveBorrowed = "elab: mark both borrowed and moved: Marke" := by
  decide +kernel

/-- C09: moving a mark the caller does not hold is refused at the call: the
    escrow cannot hand over a binding the caller never had. The callee takes
    no capability, so the call -- not the argument -- is what fails. -/
def moveDropped : String :=
  "module m { linear type Marke; table T count 2 owner Marke { slot { b : bool, } } impl fn mover(i : index into T) -> bool effects { moves Marke } { return true; } impl fn caller() { mover(0); } }"
theorem moveDropped_refused :
    stufe moveDropped = "lower: call without held mark" := by
  decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben11
