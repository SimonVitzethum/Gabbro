/-
  The checker Bool without the closedness check.

  On a complete member list `abgAlleB` is constant (`abgAlleB_wahr`), so `AkzeptiertXVoll`,
  which leaves it out, is `AkzeptiertX`. Compiled callers with the complete list of functions
  run this form; the closedness check alone cost about n^4 body walks.
-/
module
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert
public import Grammatik.Zielsatz.Faeden.Verbund.Abgeschlossen
@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration} [DecidableEq D.Fn] [DecidableEq D.Ax]

/-- `AkzeptiertX` for a complete member list. -/
def AkzeptiertXVoll (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (ls : List D.Lock)
    (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn)
    (aks : List (Kernzelle.AccumulatorDecl D) := []) (checks : List (CheckDecl D) := [])
    (aqs : List D.Ax := []) (guests : List (GuestBoundary D) := []) : Bool :=
  programmImFragmentG P fs && fussWXB P S fs ws && stufenB P fs &&
    sperrOrteB S ls && wurzelnB ws && einzelnPoolB P fs cs ws && rennB P fs cs ws &&
    antwortenB P fs && maskenB P fs && schnittstellenB P fs && libraryB P fs && Kernzelle.accumulatorB P fs (tabsOf cs) (globsOf cs) aqs aks && checkB P (tabsOf cs) (globsOf cs) fs checks && resetB cs && scopesOkProgB P fs && GuestBoundary.admissionB guests

/-- **On a complete member list the two checkers agree.** -/
theorem akzeptiertX_voll (P : Programm D) (S : SperrInv D) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn)
    (aks : List (Kernzelle.AccumulatorDecl D)) (checks : List (CheckDecl D))
    (aqs : List D.Ax) (guests : List (GuestBoundary D)) :
    AkzeptiertX P S fs ls cs ws aks checks aqs guests =
      AkzeptiertXVoll P S fs ls cs ws aks checks aqs guests := by
  simp only [AkzeptiertX, AkzeptiertXVoll, abgAlleB_wahr P hvoll, Bool.and_true]

end Gabbro.Grammatik.Zielsatz
