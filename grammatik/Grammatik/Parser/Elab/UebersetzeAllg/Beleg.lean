module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-! ## Hardware provenance of foreign bodies

    The named `assume` of a generated core query travels from the surface
    declaration (`SItemTief.accT`) to the query head (`UFnKopf.annahme`) to
    the elaborated foreign body (`UAx.beleg`, the index into `UProg.annahmen`
    resolved at elaboration) to the declaration (`D.axHerkunft`, `D.axBeleg`).
    A dangling index reads as `none`: an unresolved origin is refused, never
    inferred. -/

/-- Hardware provenance of a foreign body: `hardware` exactly when its `beleg`
    names a declared `assume`. -/
def herkunftAt (u : UProg) (a : Fin u.axs.length) : Option AxOrigin :=
  match (u.axs.get a).beleg with
  | none => if (u.axs.get a).software then some .software else none
  | some i => if (u.axs.get a).software then none
      else if i < u.annahmen.length then some .hardware else none

/-- The named assumption witnessing a hardware origin, if any. -/
def belegAt (u : UProg) (a : Fin u.axs.length) :
    Option (Option (Fin u.annahmen.length)) :=
  match (u.axs.get a).beleg with
  | none => none
  | some i => if h : i < u.annahmen.length then some (some ⟨i, h⟩) else none

/-- A foreign body without an origin has no provenance. -/
theorem herkunftAt_ohne {u : UProg} {a : Fin u.axs.length}
    (h : (u.axs.get a).beleg = none)
    (hs : (u.axs.get a).software = false) : herkunftAt u a = none := by
  unfold herkunftAt
  simp only [List.get_eq_getElem] at h hs
  simp [h, hs]

/-- A foreign body without an origin has no witness. -/
theorem belegAt_ohne {u : UProg} {a : Fin u.axs.length}
    (h : (u.axs.get a).beleg = none) : belegAt u a = none := by
  unfold belegAt
  rw [h]

end Gabbro.Grammatik.Parser.UebersetzeAllg
