/-
  File:      Grammatik/X86/TsoGxChecker.lean
  Subject:   Discharge of the DRF/checker premises of the W-to-GX refinement
             for a lowered program (lane 1251, follow-up of lane 1215).

  The refinement needs `AbgK`, `FussSX` over `GeteiltV` (the checker side),
  plus `GutO` and `StartExklusiv` (NOT the checker side: see CUTS/FINDINGs).
  All checker-side premises are derived from the accepted checker facts only:
  `Pruefer.korrekt` (soundness against `AkzeptiertSpec`), the accepted
  embedding `akzeptiertSpecX_of_spec`, and `geteiltV_leer`. Nothing is
  assumed; no definition is copied.
-/
import Grammatik.Zielsatz.Akzeptiert
import Grammatik.Zielsatz.AtomarAkzeptiert
import Grammatik.Zielsatz.BeweisAtomar
import Grammatik.Zielsatz.AkzeptiertZeuge
import Grammatik.Zielsatz.SpecProben

namespace Gabbro.Grammatik.X86.TsoGxChecker

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [DecidableEq D.Fn]

/-- **Call closure from the checker Bool**: a unit the checker accepts has a
    closed call graph at every root (the `abg` field via soundness). -/
theorem abgK_von_akzeptiert (C : Pruefer) {E : Einheit D}
    {fs : Aufzaehlung D.Fn} {ls : Aufzaehlung D.Lock}
    {cs : Aufzaehlung (D.Tab ⊕ D.Glob)}
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (w : D.Fn) :
    AbgK E.P fs.1 (reachB E.P fs.1 w) :=
  (C.korrekt E fs ls cs hC).abg w

/-- **Footprint with the rely from the checker Bool**: the accepted embedding
    `akzeptiertSpecX_of_spec` turns the checker's `FussS` into `FussSX` over
    the admitted shared atomics `GeteiltV` (via `fussSX_of_fussS`). -/
theorem fussSX_von_akzeptiert (C : Pruefer) {E : Einheit D}
    {fs : Aufzaehlung D.Fn} {ls : Aufzaehlung D.Lock}
    {cs : Aufzaehlung (D.Tab ⊕ D.Glob)}
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (f : D.Fn) :
    FussSX E.P E.S (lokW E.P fs.1 E.ws) (GeteiltV E.P E.ws) f :=
  (akzeptiertSpecX_of_spec (C.korrekt E fs ls cs hC)).fuss f

/-- **No admitted shared atomic on a checker-accepted unit**: the accepted
    `geteiltV_leer` -- every footprint carrier is signature-guarded,
    lock-protected or thread-local (`FussS`), so the rely set is empty. -/
theorem kein_geteiltV_von_akzeptiert (C : Pruefer) {E : Einheit D}
    {fs : Aufzaehlung D.Fn} {ls : Aufzaehlung D.Lock}
    {cs : Aufzaehlung (D.Tab ⊕ D.Glob)}
    (hvoll : ∀ g : D.Fn, g ∈ fs.1)
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (c : D.Tab ⊕ D.Glob) :
    ¬ GeteiltV E.P E.ws c :=
  geteiltV_leer hvoll (C.korrekt E fs ls cs hC) c

/-- **Joint checker discharge for the W-to-GX refinement**: on a unit the
    checker accepts, with a complete member list, the call graphs are closed,
    the footprint property holds with the rely, and no shared atomic is
    admitted -- so the refinement's DRF/checker premises hold with an empty
    rely set. -/
theorem checker_liefert_wgx_pruefer (C : Pruefer) {E : Einheit D}
    {fs : Aufzaehlung D.Fn} {ls : Aufzaehlung D.Lock}
    {cs : Aufzaehlung (D.Tab ⊕ D.Glob)}
    (hvoll : ∀ g : D.Fn, g ∈ fs.1)
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) :
    (∀ w : D.Fn, AbgK E.P fs.1 (reachB E.P fs.1 w)) ∧
    (∀ f : D.Fn, FussSX E.P E.S (lokW E.P fs.1 E.ws) (GeteiltV E.P E.ws) f) ∧
    (∀ c : D.Tab ⊕ D.Glob, ¬ GeteiltV E.P E.ws c) :=
  ⟨fun w => abgK_von_akzeptiert C hC w,
   fun f => fussSX_von_akzeptiert C hC f,
   fun c => kein_geteiltV_von_akzeptiert C hvoll hC c⟩

/-- **Joint witness**: all premises together on the non-degenerate two-thread
    program -- the concrete checker `akzeptiert_pruefer` accepts `mE`
    (`mP_akzeptiert`), the member lists are complete, and `hauptA` writes the
    table `privA` (a memory-changing program, cf. `zweiFaeden_bewegt_gilt`). -/
theorem checker_liefert_wgx_pruefer_zeuge :
    (∀ w : mD.Fn, AbgK Zielsatz.mE.P mFs (reachB Zielsatz.mE.P mFs w)) ∧
    (∀ f : mD.Fn, FussSX Zielsatz.mE.P Zielsatz.mE.S
      (lokW Zielsatz.mE.P mFs Zielsatz.mE.ws) (GeteiltV Zielsatz.mE.P Zielsatz.mE.ws) f) ∧
    (∀ c : mD.Tab ⊕ mD.Glob, ¬ GeteiltV Zielsatz.mE.P Zielsatz.mE.ws c) ∧
    TraegerSchreibt mHauptA (.inl MTab.privA : mD.Tab ⊕ mD.Glob) = true := by
  have hC : akzeptiert_pruefer.akzeptiert Zielsatz.mE mFs [()] mCs = true :=
    mP_akzeptiert
  obtain ⟨habg, hfuss, hleer⟩ :=
    checker_liefert_wgx_pruefer (C := akzeptiert_pruefer)
      (E := Zielsatz.mE) (fs := ⟨mFs, mFs_voll⟩) (ls := ⟨[()], mLocks_voll⟩)
      (cs := ⟨mCs, mCs_voll⟩) mFs_voll hC
  exact ⟨habg, hfuss, hleer, rfl⟩

/- CUTS:
   Proved here: the checker-side premises of the W-to-GX refinement for a
   lowered (checker-accepted, atomic-free) program, from the accepted checker
   facts only -- `AbgK` via `Pruefer.korrekt`, `FussSX` over `GeteiltV` via
   the accepted embedding `akzeptiertSpecX_of_spec`, `¬ GeteiltV` via the
   accepted `geteiltV_leer` -- with the joint non-degenerate witness
   `checker_liefert_wgx_pruefer_zeuge` (concrete checker `akzeptiert_pruefer`
   on the two-thread unit, `hauptA` writes table `privA`).
   NOT proved here, and not claimed:
   - FINDING 1 (`GutO`): the oracle bound is a named hardware assumption
     (goal shape (c)), not a checker fact. No checker Bool constrains how an
     oracle answers; `GutO` holds per-oracle by construction only
     (cf. `zO_gut`, `mO_gut`). It stays an explicit premise of any refinement
     use -- assumed nowhere here.
   - FINDING 2 (`StartExklusiv`): the start fact is a property of the thread
     start assignment, not of the checked unit. The checker's `wurzeln` field
     constrains declared starts, not the `init` function the premise speaks
     about; it holds per-program by construction (cf. `zInit_exklusiv`,
     `mInit_exklusiv`) at the `Laufzeit` leg (goal shape (d)). Assumed
     nowhere here.
   - No hardware family is connected here: this lane adds no machine steps,
     so no `HwAdapter` is instantiated (the refused default stands) and no
     `HwWf`/forwarding witness is owed by this file; the MECHANISM adapter
     boilerplate does not apply to a checker-side discharge.
   - No per-access target-to-W/GX simulation and no full bridge are claimed;
     the consumer (lane 1215's `TsoGxRefine`) still owes the machine side.
   - Silicon/timing assumptions: none (no hardware facts stated).
-/

#print axioms abgK_von_akzeptiert
#print axioms fussSX_von_akzeptiert
#print axioms kein_geteiltV_von_akzeptiert
#print axioms checker_liefert_wgx_pruefer
#print axioms checker_liefert_wgx_pruefer_zeuge

end Gabbro.Grammatik.X86.TsoGxChecker
