module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge
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
public import Grammatik.Proben.HelferZeuge.Teil1
public import Grammatik.Proben.HelferZeuge.Teil1a

@[expose] public section

namespace Gabbro.Grammatik

/-- **Witness of `ziel_ort_sperre_fortschritt`** (inhabitation): on the loop
    program `lP` of `ZielOrtGanzZeuge.lean` (the empty lock-invariant family)
    a reached machine stands at the `traverse` boundary, and the new progress
    corollary -- WITHOUT the `HeldGenau` hypothesis -- yields a step there. -/
theorem ziel_ort_sperre_fortschritt_zeuge :
    ∃ M2 : RufMaschineG zD, RufErreichbarG lP zO 0 (RufStartG lP zSp lInit) M2 ∧
      AnPruefungG M2 0 ∧ ∃ M3 : RufMaschineG zD, RufSchrittG lP zO 0 M2 0 M3 := by
  obtain ⟨M2, hr2, hA, _, _⟩ := ziel_ort_ganz_fortschritt_zeuge
  exact ⟨M2, hr2, hA, ziel_ort_sperre_fortschritt lP zO 0 (axWahr zD) (SperrInv.leer zD) zFs zSp
    lInit zO_gut zO_lokal (axVertragO_wahr zO) axEnsLokal_wahr sperrInvOk_leer zFs_voll
    lP_fragmentG (fussSperreB_of_G _ _ _ lP_fussG) (fun f => koerperGutS_leer (lP_koerperZ f))
    lP_start (fun _ => rfl) lInit_exklusiv M2 hr2 0 hA⟩

#print axioms hilfe_alt_untypbar
#print axioms ntStufen
#print axioms ntP_zertifiziert
#print axioms helfer_zeuge
#print axioms ziel_ort_sperre_fortschritt_zeuge

end Gabbro.Grammatik
