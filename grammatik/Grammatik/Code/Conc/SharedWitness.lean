import Grammatik.Code.Conc.Shared
import Grammatik.Code.Conc.Witness

/-
  File:      Grammatik/Code/Conc/SharedWitness.lean
  Subject:   TRACK L, PHASE L3 -- WITNESSES that the relaxed representation and the GX interface are not vacuous.

  On the declaration of `Conc/Witness.lean` (one table, ONE atomic global holding a machine word) at the 64-bit target:
    * `cLayOk` -- the layout assumptions hold, with the global SHARED (`shAtomic` needs it atomic: it is);
    * `rep_free_witness` -- a world in which the shared global holds 5 and a memory in which its cell holds 0 satisfy
      `Rep`: the relaxation is real, not an empty hypothesis;
    * `rep_strong_fails` -- the same pair does NOT satisfy `Rep` once the global is not shared: the cell is tied there;
    * `shared_read_refused` -- a plain read of a shared global is refused by `lowerE` (only `await` reads it);
    * `sees_shared_witness` -- the interface answers a value the memory does not hold.
-/

namespace Gabbro.Code.Lower.WitC

open Gabbro.Grammatik

section C64

local instance confS64 : Conf := ⟨64, false, Or.inr rfl⟩

/-- The same layout with the global NOT shared. -/
def cLayN : Layout cD := { cLay with shared := fun _ => false }

theorem cLayOk : LayoutOk cLay where
  tab := fun _ => rfl
  fld := fun t f _ => by cases t; cases f; exact ⟨0, by decide +kernel⟩
  inj := fun _ _ _ _ _ _ => rfl
  tinj := fun _ _ _ => rfl
  gdis := fun t g => by cases t; cases g; decide
  ginj := fun _ _ _ => rfl
  shAtomic := fun _ _ => rfl
  fsm := fun _ _ => Nat.two_pow_pos _

/-- The table block (one byte) and the word cell of the global, both zero. -/
def mem0 : Mem := ((Mem.alloc ⟨fun _ => none, 0⟩ 1 true).1.alloc 8 true).1

/-- Every slot `0`, the global `5`. -/
def wld5 : World cD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun _ => ⟨5, by decide, by decide⟩, []⟩

theorem rep_free_witness : Rep cLay wld5 mem0 := by
  refine ⟨?_, ?_⟩
  · intro t k f hs h0 h1
    have hk : k = 0 := by
      have : k < 1 := h1
      omega
    subst hk
    cases t
    cases f
    decide +kernel
  · intro g hs
    cases g
    exact ⟨⟨Val.ofInt 64 0, by decide +kernel⟩, fun h => absurd h (by decide)⟩

theorem rep_strong_fails : ¬ Rep cLayN wld5 mem0 := by
  intro h
  have := (h.2 () (by decide)).2 rfl
  revert this
  decide +kernel

theorem shared_read_refused :
    lowerE cLay [] (Gabbro.Grammatik.Expr.glob (D := cD) (Γ := []) (Λ := []) () (fun w hw => absurd hw List.not_mem_nil)) 0
      = none := by
  decide +kernel

theorem sees_shared_witness :
    Sees.shared cLay mem0 (cLay.ggblk ()) 0 (memTy (cD.gtyp ())) .acq (encM cLay (cD.gtyp ()) (wld5.globs ())) ∧
      mem0.load (cLay.ggblk ()) 0 (memTy (cD.gtyp ())) ≠ some (encM cLay (cD.gtyp ()) (wld5.globs ())) :=
  ⟨sees_shared_at cLay mem0 () rfl .acq _ (by decide), by decide +kernel⟩

end C64

end Gabbro.Code.Lower.WitC
