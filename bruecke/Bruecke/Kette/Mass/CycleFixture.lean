module
public import Bruecke.Kette.Quelle
public import Bruecke.Pruefung
public import Grammatik.Parser.Elab.UebersetzePipeline
import Grammatik.Parser.Stmt.LibraryFixtureProofs
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
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


/-!
# Finding F2, measured: with full callee contracts on a cycle the bridge would be FALSE

Three functions over one table `T` (two slots, field `v : 0 .. 10`), in the parser's fragment:

    fn h()  ensures false               { h(); }
    fn g()  ensures T.slots[0].v == 7   { h(); }
    fn f()  ensures T.slots[1].v == 5   { g(); }

Every duty GabbroV states for them HOLDS (`alle_pflichten`): a duty assumes the callees'
contracts for EVERY entry state (`Contract`), and no environment keeps `h`'s (`ensures false`) or
`g`'s (a claim about a slot `g` does not write) -- so each duty is true by vacuity. Premise (b) of
the goal theorem FAILS (`nicht_koerperGutR`): its handler class asks a callee's contract only
where the call is made, and a handler may answer `g` normally where slot 0 happens to be 7 -- then
`f` returns with slot 1 at 0. The rank check refuses the unit (`rang_faellt`: `h` calls itself),
and so do the measure duties of recursive units (`keine_massPflicht`): under every well-founded
measure, `h` may assume its own contract only strictly below its entry, so its duty is no longer
vacuous -- and the chain would otherwise prove the failing premise.
-/

namespace Gabbro.Bruecke.Zyklus

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Bruecke

attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

def uZ : UProg :=
  { tabs := [{ name := "T", count := 2, cols := [("v", (0, 10))], breiten := [] }],
    locks := [],
    fns := [
      { name := "f", params := [], kinds := [], res := none, held := [], puts := [],
        gives := [.cmp "==" (.tab "T" "v" (.lit 1)) (.lit 5)], body := [.call "g" []],
        ret := .empty, decreases := none, measureConstants := [] },
      { name := "g", params := [], kinds := [], res := none, held := [], puts := [],
        gives := [.cmp "==" (.tab "T" "v" (.lit 0)) (.lit 7)], body := [.call "h" []],
        ret := .empty, decreases := none, measureConstants := [] },
      { name := "h", params := [], kinds := [], res := none, held := [], puts := [],
        gives := [.fls], body := [.call "h" []], ret := .empty, decreases := none, measureConstants := [] }] }

theorem low_some : (lowerAllg uZ).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 3 := bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases choices with rfl | rfl | rfl
    all_goals constructor <;> cbv

def PZ : Programm (declOf uZ) := ((lowerAllg uZ).toOption.get low_some).1
def fsZ : List (declOf uZ).Fn := ((lowerAllg uZ).toOption.get low_some).2

theorem lowZ : lowerAllg uZ = .ok (PZ, fsZ) := except_ok_get low_some

theorem getragenZ : GetragenG uZ (fun _ => True) :=
  getragenG_of_bools (by cbv) (by cbv) (by cbv)

/-- The rank check refuses the unit: `h` calls itself. -/
theorem rang_faellt : rangB uZ (rangAuto uZ) = false := by decide

/-- ... and no rank exists at all. -/
theorem kein_rang : ∀ rk, ¬ Rang uZ rk := by
  intro rk h
  have := h ⟨2, by decide⟩ "h" [] (CallsIn.discard (by decide))
  exact Nat.lt_irrefl _ this

/-! ## Every duty holds -- by vacuity -/


end Gabbro.Bruecke.Zyklus
