/-
  File:      Grammatik/Zielsatz/RuheLift/Zeuge.lean
  Subject:   The witness of the idle-root lift (`ruheLift_ziel_zeuge`) on the two-thread fixture `mE` of the goal
             theorem (Zielsatz/Kern/SpecProben.lean): every premise of `ruheLift_ziel` jointly -- the concrete
             checker of before lifted to the rely (`akzeptiert_pruefer.alsX`), (b) with the rely, the hardware
             assumptions of `mO`, the declared start `hauptA` on thread 0 (no signature lock), no `atomic` global, and
             the decomposed prefix `privA[0] = 7` of `hauptA`'s body. NON-DEGENERATE: the machine of `mE.P.mitRuhe`
             the prefix translates to has a memory different from the loaded one, and every leg of `Ziel` holds there.
-/
module
public import Grammatik.Zielsatz.RuheLift.Korollar
public import Grammatik.Zielsatz.Kern.Proben
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

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

/-- The call handler the decomposed prefix of the witness runs under; the prefix makes no call. -/
def ruheLiftR : ∀ g : mD.Fn, World mD → Env mD (mD.params g) → RufAusgang g :=
  fun g _ _ => .logik (.abstieg g)

/-- **The idle-root lift on `mE`**: from `gabbro_ziel`'s own premises, the machine of `mE.P.mitRuhe` that thread 0
    reaches from the start `initEin 0 hauptA` behind `hauptA`'s first statement `privA[0] = 7` has a changed memory,
    and every leg of `Ziel` holds there -- by `ruheLift_ziel`, not by hand. -/
theorem ruheLift_ziel_zeuge [RootNativeFloat.Hardware] :
    ∃ Me : RufMaschineG mD.mitRuhe,
      RufErreichbarG mE.P.mitRuhe mO.mitRuhe 0
        (RufStartG mE.P.mitRuhe (speicherR mE.sp0) (initEin 0 mHauptA .nil)) Me ∧
      Me.speicher ≠ speicherR mE.sp0 ∧
      Ziel mE.P.mitRuhe mE.S.mitRuhe mO.mitRuhe 0
        (RufStartG mE.P.mitRuhe (speicherR mE.sp0) (initEin 0 mHauptA .nil)) Me := by
  have hA0 : AkzeptiertSpec mE.P mE.S mFs mE.ws mE.akku :=
    akzeptiertSpec_of mFs_voll mLocks_voll mCs_voll [] mP_akzeptiert
  have hC0 : akzeptiert_pruefer.akzeptiert mE mFs [()] mCs = true := by
    show Akzeptiert mP mSI mFs [()] mCs [mHauptA, mHauptB] [] = true
    exact mP_akzeptiert
  have hC : akzeptiert_pruefer.alsX.akzeptiert mE mFs [()] mCs = true :=
    Pruefer.alsX_akzeptiert akzeptiert_pruefer (E := mE) rfl rfl hC0
  obtain ⟨Me, hr, hR, hZ⟩ := ruheLift_ziel akzeptiert_pruefer.alsX mE ⟨mFs, mFs_voll⟩ ⟨[()], mLocks_voll⟩
    ⟨mCs, mCs_voll⟩ hC (nutzerPflichtA_of_akzeptiert mFs_voll hA0 mE_nutzerPflicht) mO
    ⟨mO_gut, mO_lokal, axVertragO_wahr mO, inferInstance⟩ 0 ruheLiftR 0 mHauptA .nil
    (List.mem_append_left _ List.mem_cons_self) rfl (fun g => nomatch g) (Agl := fun _ => False)
    (Zerlegt.schritt (mr := false) _ _ _ _ _ _ _ _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _))
      (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _) (Zerlegt.halt _ _ _))
  refine ⟨Me, hr, ?_, hZ⟩
  obtain ⟨⟨_, hZM⟩, _, _⟩ := hR
  intro h
  have e := congrArg (fun s : Speicher mD.mitRuhe => (s.slots MTab.privA 0 () : Zahl 0 100).n) h
  rw [hZM.2] at e
  revert e
  decide

#print axioms Gabbro.Grammatik.Zielsatz.ruheLift_ziel_zeuge

end Gabbro.Grammatik.Zielsatz
