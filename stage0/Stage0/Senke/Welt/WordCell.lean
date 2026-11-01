/- A word stored into a one-word cell: the single-word view of the complete cell store. -/
module
public import Stage0.Senke.Welt.Schreib
public import Stage0.Senke.Ausdruck.Aggregat.Scalar
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration}

theorem weltAt_slotWord [Kern] {m : Runner.Mem} {L : Lay D} {σ : World D} {t : D.Tab} {f : D.Feld t} {kn : Nat}
    {v : Wert D (D.typ t f)} {w : Runner.W} (width : valueWords (D.typ t f) = 1) (hW : WeltAt m L σ)
    (hl : LayIn L) (hd : LayDis L) (hk : (kn : Int) < L.count t) (encoded : Enc L (D.typ t f) v w) :
    WeltAt (write m (BitVec.ofNat 64 (L.elem t f kn)) 8 w.toNat) L (σ.storeSlot t kn f v) := by
  obtain ⟨valid, words⟩ := Enc.single (D.typ t f) v w width encoded
  have stored := weltAt_slot hW hl hd hk valid
  rw [words] at stored
  exact stored

theorem weltAt_globWord [Kern] {m : Runner.Mem} {L : Lay D} {σ : World D} {g : D.Glob}
    {v : Wert D (D.gtyp g)} {w : Runner.W} (width : valueWords (D.gtyp g) = 1) (hW : WeltAt m L σ)
    (hl : LayIn L) (hd : LayDis L) (encoded : Enc L (D.gtyp g) v w) :
    WeltAt (write m (BitVec.ofNat 64 (L.ga g)) 8 w.toNat) L (σ.storeGlob g v) := by
  obtain ⟨valid, words⟩ := Enc.single (D.gtyp g) v w width encoded
  have stored := weltAt_glob hW hl hd valid
  rw [words] at stored
  exact stored

end Gabbro.Stage0.Senke
