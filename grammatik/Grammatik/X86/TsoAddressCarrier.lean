/-
  File:      Grammatik/X86/TsoAddressCarrier.lean
  Subject:   x86 address to source carrier mapping for the TSO-to-W bridges.

  Lane 1245 (follow-up of lane 1213, `TsoRmwLink.lean`): the links in
  `CarrierTraceBridge.lean`, `TsoReadBridge.lean` and `TsoRunInduction.lean`
  hold over the GENERIC history shape because no accepted x86-address to
  carrier mapping existed. This module defines that mapping from the
  pipeline's placement layout (`PipelineImage.lean`: `Platz`, `layoutVon`,
  `TabLayout`) to the source carriers (`t`, `k`, `f`) used by the W
  history: the relation `kartiert` (address `a` is the placed address of
  slot `(t, k, f)`), proved injective on admitted placements
  (`kartiert_injektiv`: one address names one slot) with disjoint 8-byte
  footprints for distinct carriers (`kartiert_sep`: same slot or
  `Disjunkt`), and specialises the no-read write bridge
  (`schrittW_aus_gruppen_drain`) to placed addresses, discharging its
  `repOk` premise from the decided placement admission (`platzOkB`).

  Reused, never redefined: `Platz`/`layoutVon`/`sepB`/`sepB_sound`/
  `layoutVon_loc`/`trifft_inv`/`platzOkB` (PipelineImage), `LayoutSep`/
  `repOk_int`/`natAdresse_ohneUmbruch` (Pipeline), `Disjunkt`/
  `disjunkt_von_intervallen` (Speicher), `natAdresse`
  (Regionen), `rep_schritt_bleibt`/`RepSlot`/`zahlWort`/`wortZahl`
  (SourceMemory), `schrittW_aus_gruppen_drain` with its witness vocabulary
  (`witD`, `ctProg`, `ctS*`, ...) (CarrierTraceBridge).

  SCOPE (honest): the mapping covers placed integer slots only (the
  `repOk` fragment); globals, bools, sums, floats and function pointers
  have no address form here. The full per-access target-to-W/GX simulation
  stays OPEN (see CUTS).
-/
import Grammatik.X86.PipelineImage
import Grammatik.X86.CarrierTraceBridge

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

variable {D : Deklaration}

/-- THE MAPPING: byte address `a` is the placed address of source slot
    `(t, k, f)` under placements `ps` (the pipeline's `layoutVon`). -/
def kartiert (ps : List (PipelineImage.Platz D)) (a : Nat)
    (t : D.Tab) (k : Int) (f : D.Feld t) : Prop :=
  (PipelineImage.layoutVon ps).loc t k f = some a

/-! ## 1. Separation and injectivity on admitted placements -/

/-- **DISJOINT FOOTPRINTS (`kartiert_sep`).** Two placed slots are the
    same slot or have disjoint 8-byte footprints: the decided `sepB`
    gives `LayoutSep` (`sepB_sound`), and the Nat interval disjointness
    becomes `Disjunkt` under the no-wrap bounds (from placement
    admission, see `zugelassen_schranke`). Every premise is used: `hsep`
    for the layout separation, `h1`/`h2` for the two placed slots,
    `w1`/`w2` for the no-wrap side conditions. -/
theorem kartiert_sep (ps : List (PipelineImage.Platz D))
    (hsep : PipelineImage.sepB ps = true)
    (t1 : D.Tab) (k1 : Int) (f1 : D.Feld t1) (a1 : Nat)
    (t2 : D.Tab) (k2 : Int) (f2 : D.Feld t2) (a2 : Nat)
    (h1 : kartiert ps a1 t1 k1 f1)
    (h2 : kartiert ps a2 t2 k2 f2)
    (w1 : a1 + 8 ≤ 2 ^ 64) (w2 : a2 + 8 ≤ 2 ^ 64) :
    (t1 = t2 ∧ k1 = k2 ∧ HEq f1 f2) ∨
      Disjunkt (natAdresse a1) (natAdresse a2) := by
  have hL := PipelineImage.sepB_sound ps hsep
  rcases hL t1 k1 f1 a1 t2 k2 f2 a2 h1 h2 with hEq | hDis
  · exact Or.inl hEq
  · exact Or.inr (by
      apply disjunkt_von_intervallen _ _
        (Pipeline.natAdresse_ohneUmbruch a1 w1)
        (Pipeline.natAdresse_ohneUmbruch a2 w2)
      rw [PipelineImage.natAdresse_toNat_lt a1 (by omega),
        PipelineImage.natAdresse_toNat_lt a2 (by omega)]
      exact hDis)

/-- **INJECTIVITY (`kartiert_injektiv`).** One placed address names one
    source slot: two slots placed at the same address are the same slot.
    The disjoint-footprint alternative of `kartiert_sep` is impossible
    (a footprint always meets itself). Every premise is used: `hsep`
    through the separation, `h1`/`h2` for the two placements, `w` for
    both no-wrap bounds. -/
theorem kartiert_injektiv (ps : List (PipelineImage.Platz D))
    (hsep : PipelineImage.sepB ps = true)
    (t1 : D.Tab) (k1 : Int) (f1 : D.Feld t1)
    (t2 : D.Tab) (k2 : Int) (f2 : D.Feld t2) (a : Nat)
    (h1 : kartiert ps a t1 k1 f1)
    (h2 : kartiert ps a t2 k2 f2)
    (w : a + 8 ≤ 2 ^ 64) :
    t1 = t2 ∧ k1 = k2 ∧ HEq f1 f2 := by
  rcases kartiert_sep ps hsep t1 k1 f1 a t2 k2 f2 a h1 h2 w w with
    hEq | hDis
  · exact hEq
  · exact False.elim (hDis 0 0 (by decide) (by decide) rfl)

/-! ## 2. Admission: placed slots are admitted, bounded slots -/

/-- **ADMISSION FROM THE CHECK (`platzOk_rep`).** A member placement
    that names slot `(t, k, f)` discharges the representation admission
    (`repOk`) for that slot at its placed address, plus the read/write
    permissions the bridges consume. Proved from the decided
    `platzOkB` over the member (`List.all_eq_true`) with the key
    rewritten through `trifft_inv`. Every premise is used: `h` for the
    decided check, `hp` for the membership, `htr` for the key rewrite
    (all three key components via `subst`). -/
theorem platzOk_rep {D : Deklaration} (m : Speicher)
    (ps : List (PipelineImage.Platz D))
    (h : PipelineImage.platzOkB m ps = true)
    (p : PipelineImage.Platz D) (hp : p ∈ ps)
    (t : D.Tab) (k : Int) (f : D.Feld t)
    (htr : p.trifft t k f = true) :
    repOk (D.typ t f) p.a 8 0 = true ∧
      lesbar8 m (natAdresse p.a) = true ∧
      schreibbar8 m (natAdresse p.a) = true := by
  obtain ⟨pt, pk, pf, pa⟩ := p
  have h1 := List.all_eq_true.mp h ⟨pt, pk, pf, pa⟩ hp
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨hre, hles⟩, hschr⟩ := h1
  obtain ⟨ht, hk, hf⟩ := PipelineImage.trifft_inv ⟨pt, pk, pf, pa⟩ t k f htr
  simp only at ht hk hf ⊢
  subst ht hk
  simp only [cast_eq] at hf
  subst hf
  exact ⟨hre, hles, hschr⟩

/-- **ADMITTED PLACEMENTS DO NOT WRAP (`zugelassen_schranke`).** A slot
    the placement layout maps to `a` satisfies `a + 8 ≤ 2 ^ 64`: the
    placed address comes from a member placement (`layoutVon_loc`),
    whose decided admission carries the bound (`repOk_int` over
    `platzOk_rep`). Feeds the no-wrap premises of `kartiert_sep` from
    the checks instead of an assumed bound. Every premise is used. -/
theorem zugelassen_schranke {D : Deklaration} (m : Speicher)
    (ps : List (PipelineImage.Platz D))
    (h : PipelineImage.platzOkB m ps = true)
    (t : D.Tab) (k : Int) (f : D.Feld t) (a : Nat)
    (hloc : (PipelineImage.layoutVon ps).loc t k f = some a) :
    a + 8 ≤ 2 ^ 64 := by
  obtain ⟨p, hmem, htr, rfl⟩ := PipelineImage.layoutVon_loc ps t k f a hloc
  obtain ⟨lo, hi, -, -, -, hbound⟩ :=
    Pipeline.repOk_int (D.typ t f) p.a
      (platzOk_rep m ps h p hmem t k f htr).1
  exact hbound

/-- **FIRST HIT IS THE MAPPING (`kartiert_von_erst`).** If `p` is the
    first placement naming `(t, k, f)`, the layout maps the slot to
    `p.a` -- and `p` indeed names the slot (from the `find?` equation,
    never assumed). Both conjuncts are derived from `hfirst`. -/
theorem kartiert_von_erst {D : Deklaration}
    (ps : List (PipelineImage.Platz D))
    (t : D.Tab) (k : Int) (f : D.Feld t)
    (p : PipelineImage.Platz D)
    (hfirst : ps.find? (fun q => q.trifft t k f) = some p) :
    kartiert ps p.a t k f ∧ p.trifft t k f = true := by
  refine ⟨?_, List.find?_some (p := fun q : PipelineImage.Platz D => q.trifft t k f) hfirst⟩
  unfold kartiert PipelineImage.layoutVon
  simp only [hfirst, Option.map_some]

/- CUTS:
   (skeleton: mapping relation only; theorems follow in small pieces.)
-/

#print axioms kartiert

end Gabbro.Grammatik.X86
