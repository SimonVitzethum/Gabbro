/-
  Loaded image to actual instruction fetch (lane 560).

  Connects the checked `Bild` file/virtual mapping and its actual memory
  construction (`geladen`, `abteilFinden`, `ladenByte`) to the byte fetch
  (`Byteschritt.geholt`, `fetchDekodiert`, `byteschritt`). The checked map
  is a premise; fetched-byte equality and the loaded execution step are
  derived conclusions. No source refinement or hardware correspondence is
  claimed here; both stay explicitly open (see CUTS).
-/
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- Execution state over a canonically loaded image: registers, flags and
    `rip` are caller-chosen; memory is the checked `geladen` construction,
    never a second loader. -/
def bildZustand (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) : Zustand :=
  { register := reg
    flags := fl
    rip := rip
    speicher := geladen bild bias }

/-- The loaded state carries the canonically loaded memory. -/
theorem bildZustand_speicher (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) :
    (bildZustand bild bias rip reg fl).speicher = geladen bild bias := by
  rfl

/-! ## 1. Checked-map inversion: the acceptance Bool as premise.

    Each fact below takes `wohlgeformt p bild = true` as a premise and
    derives one per-section obligation for a member section. -/

/-- INVERSION (sizes): an accepted image checks every section's size. -/
theorem wohlgeformt_groesse (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : wohlgeformt p bild = true) :
    groesseOk s = true := by
  have h2 := h
  simp only [wohlgeformt, Bool.and_eq_true] at h2
  have hall : bild.abschnitte.all groesseOk = true :=
    h2.1.1.1.1.1.1.1.1.1.1
  exact (List.all_eq_true.mp hall) s hmem

/-- INVERSION (file containment): every section of an accepted image lies
    inside the file. -/
theorem wohlgeformt_datei (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : wohlgeformt p bild = true) :
    s.dateiOff + s.dateiLen ≤ bild.datei.length := by
  have h2 := h
  simp only [wohlgeformt, Bool.and_eq_true] at h2
  have hall : bild.abschnitte.all (dateiOk bild.datei) = true :=
    h2.1.1.1.1.1.1.1.1.1.2
  have hs : dateiOk bild.datei s = true :=
    (List.all_eq_true.mp hall) s hmem
  exact of_decide_eq_true hs

/-- INVERSION (W^X): no section of an accepted image is writable and
    executable at once. -/
theorem wohlgeformt_wx (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : wohlgeformt p bild = true) :
    wxOk s = true := by
  have h2 := h
  simp only [wohlgeformt, Bool.and_eq_true] at h2
  have hall : bild.abschnitte.all wxOk = true :=
    h2.1.1.1.1.1.2
  exact (List.all_eq_true.mp hall) s hmem

/-- INVERSION (alignment): the biased base of every section of an accepted
    image meets its declared alignment. -/
theorem wohlgeformt_ausr (p : Profil) (bild : Bild) (s : Abschnitt)
    (bias : Nat) (hbias : bias = effBias bild.modus)
    (hmem : s ∈ bild.abschnitte) (h : wohlgeformt p bild = true) :
    0 < s.ausr ∧ (bias + s.vaddr) % s.ausr = 0 := by
  have h2 := h
  simp only [wohlgeformt, Bool.and_eq_true] at h2
  have hall : bild.abschnitte.all (ausrOk (effBias bild.modus)) = true :=
    h2.1.1.1.1.1.1.2
  have hs : ausrOk (effBias bild.modus) s = true :=
    (List.all_eq_true.mp hall) s hmem
  rw [← hbias] at hs
  exact of_decide_eq_true hs

/- CUTS:
   - Skeleton only: the fetch-interior equality, BSS, permission
     distinction, store execution and negative probes are not yet proved.
   - No source refinement claim and no hardware correspondence claim.
-/

#print axioms bildZustand_speicher

end Gabbro.Grammatik.X86
