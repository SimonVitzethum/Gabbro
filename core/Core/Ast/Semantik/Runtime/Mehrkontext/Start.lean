/-
  File:      core/Core/Ast/Semantik/Runtime/Mehrkontext/Start.lean
  Subject:   THE START OF THE CONTEXTS OF A PROGRAM (MK-01). The boot data gives the entry context the first
             instruction and the arrival regions, and every other context a resting frame at the entry of its
             own body (`Fragment.eintritte`). A handler or NMI handler that the machine delivers
             (`Zustandseintritt`) therefore runs its own body, not the entry body
             (`handler_beginnt_im_rumpf`); the arrival regions belong to exactly one context
             (`startdaten_regionen_eindeutig`).
-/
module

public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Semantik.Runtime.Mehrkontext.Kopf

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

section Startdaten

variable (scope : Scope) (eintritte : Kontext → Option Nat) (kern : Option Nat)
  (platform : Plattform) (regions : List Strecke)

/-- The entry context starts at the first instruction. -/
theorem startdaten_eintritt_pc :
    ((startdaten scope eintritte kern platform regions).lokal eintritt).pc = 0 := by
  simp only [startdaten, if_pos rfl, if_true]

/-- **Every other context rests with its frame at the entry of its own body.** -/
theorem startdaten_rumpf_pc {c : Kontext} (h : c ≠ eintritt) :
    ((startdaten scope eintritte kern platform regions).lokal c).pc = (eintritte c).getD 0 := by
  simp only [startdaten, if_neg h]

theorem startdaten_ruht {c : Kontext} (h : c ≠ eintritt) :
    (startdaten scope eintritte kern platform regions).status c = .ruht := by
  simp only [startdaten, if_neg h]

theorem startdaten_laeuft :
    (startdaten scope eintritte kern platform regions).status eintritt = .laeuft := by
  simp only [startdaten, if_pos rfl, if_true]

/-- **The arrival regions belong to exactly one context.** No other context's boot frame lists
    one, so a region is bound by the frame of the entry context alone until a program hands it
    over. -/
theorem startdaten_regionen_eindeutig {c : Kontext} (h : c ≠ eintritt) :
    ((startdaten scope eintritte kern platform regions).lokal c).arrivalRegions = [] := by
  simp only [startdaten, if_neg h]

/-- A boot frame has neither returned nor stopped, whichever context it belongs to. -/
theorem startdaten_unbewegt (c : Kontext) :
    ((startdaten scope eintritte kern platform regions).lokal c).rueckgabe = none ∧
      ((startdaten scope eintritte kern platform regions).lokal c).stopp = none :=
  ⟨rfl, rfl⟩

end Startdaten

/-- **A delivered handler runs its own body.** After the machine delivers an interrupt to the
    context `c` of the fragment (`Zustandseintritt`), the head of `c` is the instruction at the
    entry of its body, and not the first instruction of the program. -/
theorem handler_beginnt_im_rumpf (p : Fragment) (platform : Plattform) (start : AussenStart)
    (k : Kern) (id : Nat × Nat) (c : Kontext) (nmi : Bool) (hc : c ≠ eintritt) {pos : Nat}
    (entry : p.eintritte c = some pos) :
    kopf p.code (Zustandseintritt (I.start (p.einheit platform) start).2 k id c nmi) c =
      p.code[pos]? := by
  have status : (Zustandseintritt (I.start (p.einheit platform) start).2 k id c nmi).status c =
      .laeuft := by
    simp only [Zustandseintritt, Function.update_self]
  have frame : (Zustandseintritt (I.start (p.einheit platform) start).2 k id c nmi).lokal c =
      (startdaten p.eingang p.eintritte (start.assignment 0) platform start.regions).lokal c := rfl
  rw [kopf_laufend status (by rw [frame]; exact (startdaten_unbewegt ..).1)
    (by rw [frame]; exact (startdaten_unbewegt ..).2), frame,
    startdaten_rumpf_pc _ _ _ _ _ hc, entry]
  rfl

end Gabbro.Core.Ast.Semantik
