module
public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Parser.Elab.UebersetzeAllg2
public import Grammatik.Parser.Elab.UebersetzeAllg3
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
# S4 (start part): `StartPflicht` for a unit whose starts owe nothing

`StartPflicht E` (goal theorem, premise (b)): every lock invariant holds at the declared initial
memory, and every declared start's `requires` holds at that memory with its declared arguments.
GabbroV's duty files ASSUME the corresponding `Initially`. For a unit the Lean parser elaborates
(`uebersetzeAllg`) both halves are decided by the unit's SHAPE, not by a proof about a memory:
the parser's lowering writes `requires := .tru` for every function (a `Held(L)` requirement is the
caller's lock duty, carried by the signature), and the family of lock invariants is the empty one.
`startPflicht_wahr` states exactly that, once: the two hypotheses are checked per unit by `rfl`.
A unit that WRITES a `requires` or a lock invariant needs a real duty at the initial memory --
`Initially` in the duty files -- and lies outside the parser's fragment today (see the report).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

theorem startPflicht_wahr {D : Deklaration} (E : Einheit D)
    (hS : ∀ L, E.S.inv L E.sp0 = true) (hR : ∀ f, E.P.requires f = .tru) : StartPflicht E :=
  ⟨hS, fun a _ => by
    unfold ReqAmEintritt
    rw [hR]
    rfl⟩

end Gabbro.Bruecke

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- **The parser's lowering writes no `requires`** (`progOfFn`: `requires := fun _ => .tru`), for
    every program it accepts -- so the second half of `StartPflicht` costs nothing there. -/
theorem lowerAllg_requires (u : UProg) (P : Programm (declOf u)) (fs : List (declOf u).Fn)
    (h : lowerAllg u = .ok (P, fs)) : ∀ f, P.requires f = .tru := by
  unfold lowerAllg at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with h1
      injection h1 with h2 h3
      subst h2
      intro f
      rfl

end Gabbro.Bruecke
