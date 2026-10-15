/-
  File:      Grammatik/X86/CasDivergenceRec.lean
  Subject:   Per-program CAS divergence record: one source step versus an
              unbounded CAS retry loop, with cost-bound refusal.

  Lane 785. One source step that lowers to a CAS retry loop may retire
  arbitrarily many target attempts (`LockedOps.casKosten`,
  `cas_schleife_unbeschraenkt`: no constant bounds every retry count).
  This file adds the checked per-program record of that divergence --
  observed attempts plus the claimed per-site bound (`none` = honestly
  unbounded) -- and proves: (a) the connection `CasDivergenceRec_verbindung`
  from a covered record bound to the summary work bound over one source
  step; (b) the refusal `ohneDivergenz_keinKostenAnspruch`: without a
  covering record the summary admission AND the transfer admission refuse
  together. No new decoder, evaluator, encoding or fault class: canonical
  `TSOZustand`/`casSchritt`, the accepted `CostSummary` schema and the
  actual source fixture are reused untouched; fetched bytes stay with the
  `ExtendedExecution`/`LockedInstructionExecution` owners.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
  Intel SDM 325462-093US Sep 2026 -- LOCK prefix Vol. 2A 3-565/3-566,
  XADD Vol. 2D 6-27/6-28, CMPXCHG Vol. 2A 3-193/3-194 (failure still
  performs the destination write cycle). No new encoding is claimed here.
-/
import Grammatik.X86.CostSummary
import Grammatik.X86.LockedOps
import Grammatik.ZielOrtEinfadenZeuge

namespace Gabbro.Grammatik.X86

/-- Per-program CAS divergence record: for ONE source step that lowers to
    a CAS retry loop, the attempt count of this program's loop and the
    claimed per-site attempt bound. `schranke = none` is the honest
    unbounded case: one source step may take arbitrarily many target
    attempts, and no constant work bound may be claimed for it. -/
structure CasDivergenzRec where
  versuche : Nat
  schranke : Option Nat
  deriving DecidableEq, Repr

/-- Divergence amount: one source step costs `versuche + 1` target steps
    (the one `casKosten`, reused, never a second cost model). -/
def divergenzBetrag (r : CasDivergenzRec) : Nat :=
  casKosten r.versuche

/-- Transfer admission of the record against a summary: the record claims
    a bound covering its attempts AND the summary carries a retry bound
    covering the record bound. Anything else is `false`: an unbounded
    record, or a summary with no proved attempt bound, admits no
    cost-bound claim through this record. -/
def divergenzZulaessig (s : CostSummary) (r : CasDivergenzRec) : Bool :=
  match r.schranke, s.retryBound with
  | some K, some B => decide (r.versuche ≤ K) && decide (K ≤ B)
  | _, _ => false

/-! ## Connection: a covered record bound meets the work bound.

    One source step (`src = 1`) against a CAS retry loop: the record
    claims a per-site bound `K` covering its attempts, the summary
    carries a retry bound `B` covering `K`, and the uniform maximum `m`
    covers one more than `B` (the final outcome beside the attempts).
    Then the divergence amount is inside every summary work bound `k`
    over that one source step, and the record is transfer-admitted.
    All eight premises are used: `hSchranke`/`hVersuch`/`hRetry`/`hDeckt`
    admit the record, `hVersuch`/`hDeckt`/`hMaxGe` bound the attempts,
    `hMax`/`hk` expand the summary. -/

/-- TARGET: a covered divergence record is transfer-admitted and its
    amount fits the summary work bound over one source step. -/
theorem CasDivergenceRec_verbindung
    (s : CostSummary) (r : CasDivergenzRec) (K B m k : Nat)
    (hSchranke : r.schranke = some K)
    (hVersuch : r.versuche ≤ K)
    (hRetry : s.retryBound = some B)
    (hDeckt : K ≤ B)
    (hMax : alleMax s = some m)
    (hMaxGe : B + 1 ≤ m)
    (hk : expandBound s 1 = some k) :
    divergenzZulaessig s r = true ∧ divergenzBetrag r ≤ k := by
  have hExp := expandBound_keinVerlust s 1 m hMax
  have hkEq : k = 1 * m + s.spillCount + s.fenceCount :=
    Option.some_inj.mp (hk.symm.trans hExp)
  refine ⟨?_, ?_⟩
  · unfold divergenzZulaessig
    rw [hSchranke, hRetry]
    simp [hVersuch, hDeckt]
  · unfold divergenzBetrag casKosten
    omega

/-! ## Refusal: no covering record, no cost-bound claim.

    An unbounded record (`schranke = none`) against a summary with no
    proved attempt bound (`retryBound = none`) that still prices the
    retry class refuses twice: the summary admission (the accepted
    `kostenSummeOk_verweigert_unbegrenzt`) AND the record transfer
    admission. A CAS loop without its divergence record never gets a
    constant: `cas_schleife_unbeschraenkt` proves every claimed bound is
    exceeded by some retry count. All three premises are used. -/

/-- A cost-bound claim over an unbounded CAS loop without a covering
    divergence record is refused on both admissions. -/
theorem ohneDivergenz_keinKostenAnspruch
    (s : CostSummary) (r : CasDivergenzRec) (k : Nat)
    (hOffen : r.schranke = none)
    (hRetry : s.retryBound = none)
    (hExpand : s.expand .retryTry = some k) :
    kostenSummeOk s = false ∧ divergenzZulaessig s r = false := by
  refine ⟨kostenSummeOk_verweigert_unbegrenzt s k hRetry hExpand, ?_⟩
  unfold divergenzZulaessig
  rw [hOffen]

/-! ## Joint witness: covered record on a non-degenerate program.

    The source side reuses the `eP` fixture (table `konto` written by
    `eSetze`, reached run carrying slot `5` against start `0`); the
    target side reuses the reached two-core locked-add run whose word
    moved observably. Jointly with both, the covered record
    `⟨2, some 3⟩` against `blattSummary` (retry bound 4, uniform
    maximum 5, work bound 5 over one source step). -/

/-- Joint witness for `CasDivergenceRec_verbindung`: all its premises
    hold together on the admitted summary and the covered record, with
    a memory-changing source run and a memory-changing target run. -/
theorem CasDivergenceRec_verbindung_zeuge :
    ∃ (M : RufMaschineG eD) (rho : Env eD (eD.params ePruefe))
      (w0 : World eD) (s0 s2 : TSOZustand),
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
      (eSp.slots () 0 ()).n = 0 ∧
      (eD.signatur eSetze).schreibt () = true ∧
      RufEreignisF.eintritt ePruefe rho w0 ∈ (M.faeden 0).log ∧
      ReqAmEintritt eP ePruefe w0 rho ∧
      (w0.slots () 0 ()).n = 5 ∧
      s0.mem.bytes lockAddr ≠ s2.mem.bytes lockAddr ∧
      divergenzZulaessig blattSummary ⟨2, some 3⟩ = true ∧
      divergenzBetrag ⟨2, some 3⟩ ≤ 5 := by
  obtain ⟨M, hr, h0, rho, w0, hm, hreq, h5⟩ := ziel_ort_einfaden_zeuge
  obtain ⟨t0, _, t2, _, _, _, _, _, _, _, hmem⟩ := locked_add_zwei_kerne
  have hVerb := CasDivergenceRec_verbindung blattSummary ⟨2, some 3⟩ 3 4 5 5
    rfl (by decide) rfl (by decide) (by decide) (by decide)
    blattSummary_schranke
  exact ⟨M, rho, w0, t0, t2, hr, h0, rfl, hm, hreq, h5, hmem,
    hVerb.1, hVerb.2⟩

/- CUTS:
    - Proved here: per-program divergence record with its amount and its
      transfer admission; the connection from a covered record bound to
      the summary work bound over one source step; the joint refusal of
      summary admission and transfer admission without a covering record.
    - NOT proved here: which source step lowers to which CAS loop (the
      lowering/IR producer owns the correspondence; no `IR.lean` exists);
      no new byte decoding, execution, fault or timing claim (fault
      classes stay with `HardwareFaults`, fetched steps with
      `ExtendedExecution`/`LockedInstructionExecution`, per-form timing
      with `HardwareAssumptions`); no progress, fairness or retry-success
      promise (a covered bound counts attempts, it never promises one
      succeeds); no silicon correspondence.
-/

#print axioms CasDivergenceRec_verbindung
#print axioms ohneDivergenz_keinKostenAnspruch
#print axioms CasDivergenceRec_verbindung_zeuge

end Gabbro.Grammatik.X86
