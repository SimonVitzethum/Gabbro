module
public import Bruecke.Anweisung.Lokal.Ruf
@[expose] public section

/-!
# Numeric binder inversion used by positional statement simulations

The visible source-name projection is used only for the existing expression theorem.
The canonical state relation and all binder updates are positional (`Werte.lean`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. The values -/

theorem lowBindWert_side {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {d : Option (Int × Int)} {v : USide} {ls : LowSide u Γ Λ}
    (h : lowBindWert u Γ Λ fn d v = .ok ls) : lowSideVal u Γ Λ fn v = .ok ls := by
  unfold lowBindWert at h
  split at h
  · cases h
  · rename_i s' hs'
    split at h
    · cases h
      exact hs'
    · split at h
      · cases h
        exact hs'
      · cases h

end Gabbro.Bruecke
