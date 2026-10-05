/-
  Validator soundness for the decidable part (lane 1223).

  Packages exactly what `valX86` decides (`ValidatorSkeleton.valX86`:
  checked mapping AND whole-section decode coverage from each section
  base): mapping and coverage projections, per-section full decode,
  loaded-byte agreement through the accepted `geladen` construction,
  and the coherent-machine fetch identity (`HwLoadedImage`). This is
  NOT source refinement; the full closing theorem stays OPEN (CUTS).
-/
import Grammatik.X86.ValidatorExecution
import Grammatik.X86.ValidationBudget
import Grammatik.X86.HwLoadedImage

namespace Gabbro.Grammatik.X86

/-- SOUNDNESS, mapping leg: admission implies the checked mapping.
    Reuses `valX86_wohlgeformt`; no claim beyond the decided Bool. -/
theorem valSound_mapping (p : Profil) (bild : Bild)
    (h : valX86 p bild = true) :
    wohlgeformt p bild = true :=
  valX86_wohlgeformt p bild h

/-- SOUNDNESS, coverage leg: admission implies whole-image decode
    coverage. Reuses `valX86_deckung`; coverage starts at each
    section base (interior entries are a pinned gap, see CUTS). -/
theorem valSound_deckung (p : Profil) (bild : Bild)
    (h : valX86 p bild = true) :
    bildDeckung bild = true :=
  valX86_deckung p bild h

/-- SOUNDNESS, per-section leg: admission covers EVERY member section
    (executable sections decode fully, data sections carry `true`).
    Derived from the coverage projection through the same `all` the
    definition uses; no second register. -/
theorem valSound_abschnitt (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : valX86 p bild = true) :
    abschnittDeckung bild s = true := by
  have hd := valSound_deckung p bild h
  unfold bildDeckung at hd
  exact (List.all_eq_true.mp hd) s hmem

/-- SOUNDNESS, no-stray-bytes leg: every executable member section
    fully decodes from its base under fuel `dateiLen + 1` (one byte
    per instruction plus the empty program). This is whole-section
    decode from the base only; interior offsets are a pinned gap. -/
theorem valSound_exec_vollex (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (hexe : s.ausfuehrbar = true)
    (h : valX86 p bild = true) :
    validAllFuel (s.dateiLen + 1) (abschnittBytes bild s) = true := by
  have ha := valSound_abschnitt p bild s hmem h
  unfold abschnittDeckung at ha
  simp only [hexe, if_true] at ha
  exact ha

/-- SOUNDNESS, traversal leg (generic): full validation means the
    fuel traversal succeeds with no remainder. Timeout (`none`) and
    leftover bytes never validate; the proof inverts the `validAllFuel`
    match, so every premise shapes the conclusion. -/
theorem validAllFuel_gibt_traversierung (fuel : Nat) (bs : List Byte)
    (h : validAllFuel fuel bs = true) :
    ∃ ins, decodeFuel fuel bs = some (ins, []) := by
  unfold validAllFuel at h
  generalize hg : decodeFuel fuel bs = g at h ⊢
  cases g with
  | none =>
    simp at h
  | some pr =>
    obtain ⟨ins, rest⟩ := pr
    cases rest with
    | nil =>
      exact ⟨ins, rfl⟩
    | cons _ _ =>
      simp at h

/-- SOUNDNESS, traversal leg (applied): every executable member
    section of an admitted image traverses with no remainder. -/
theorem valSound_exec_traversierung (p : Profil) (bild : Bild)
    (s : Abschnitt) (hmem : s ∈ bild.abschnitte)
    (hexe : s.ausfuehrbar = true) (h : valX86 p bild = true) :
    ∃ ins, decodeFuel (s.dateiLen + 1) (abschnittBytes bild s) =
      some (ins, []) :=
  validAllFuel_gibt_traversierung _ _
    (valSound_exec_vollex p bild s hmem hexe h)

/- CUTS (partial; extended with each added leg):
    Proved here: mapping and coverage projections of `valX86`,
    per-section coverage, whole-section full decode from the base,
    and its no-remainder traversal inversion.
    OPEN (never a premise here): `valX86_sound_full`: no claim that
    an admitted image is the emitted form of any source program, or
    refines any contract, duty, cost, lock or budget; no hardware
    claim (silicon, caches, TLBs, store buffers, interrupts, faults,
    timing); no multi-step control-flow or TSO/GX bridge claim.
-/

#print axioms valSound_mapping
#print axioms valSound_deckung
#print axioms valSound_abschnitt
#print axioms valSound_exec_vollex
#print axioms validAllFuel_gibt_traversierung
#print axioms valSound_exec_traversierung

end Gabbro.Grammatik.X86
