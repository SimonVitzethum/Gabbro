/-
  File:      core/Core/Ziel/Korrektheit/Beweise/BildGueltig.lean
  Subject:   THE PROOF of `BildGueltigAussage`, the pinned image-validity leg of the goal theorem
             (`Core/Ziel/Korrektheit/Zusammensetzung.lean`).

  Elaboration of a source unit binds the fixed image `Ast.Semantik.bild` and the selected platform's
  catalogue (`Fragment.einheit`), so `(einheitVon P t).bild` is the constant image and
  `(einheitVon P t).katalog.plattform.ziel` reduces to `P.ziel`. The admission premise is therefore not
  needed: validity of the image holds for every source tree. Its three conjuncts are the image format
  (`.elf`, present on every approved platform by `ziele_gut`), the in-bounds condition on image bytes,
  and the presence of a byte at every entry. No statement is changed and no witness or per-program fact
  is used.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- The fixed loader image is valid on the target selected by any source elaboration. -/
theorem bildGueltig_einheitVon (P : Katalog.Plattform) (t : Ast.Unit) :
    (einheitVon P t).bild.gueltig (einheitVon P t).katalog.plattform.ziel := by
  change (Ast.Semantik.bild : Katalog.Bild).gueltig P.ziel
  rcases Katalog.ziele_gut P with ⟨_, _, _, _, _, _, _, _, _, helf⟩
  refine ⟨helf, ?_, ?_⟩
  · intro a byte present
    change (if a = 0 then some 0 else none) = some byte at present
    split at present
    · subst a
      exact Nat.pow_pos (Nat.zero_lt_succ _)
    · cases present
  · intro entry mem
    have entryZero : entry = 0 := List.mem_singleton.mp mem
    subst entry
    exact ⟨0, rfl⟩

/-- The image of an admitted unit is valid. -/
theorem bildGueltig (P : Katalog.Plattform) : BildGueltigAussage P :=
  fun t _ => bildGueltig_einheitVon P t

end Gabbro.Core.Ziel.Korrektheit
