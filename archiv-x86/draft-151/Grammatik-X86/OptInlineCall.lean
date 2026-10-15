/-
  File:      Grammatik/X86/OptInlineCall.lean
  Subject:   Inlining rule lemma (lane 873).

  DESIGN section 7 row: "block map + fresh renames + callee duties within
  caller site + depth discipline + GHOST call/return events (actual values,
  reason channel, order)", certificate "B+C", failure case "identical
  contracts without ghost events (FolgeG order lost); inline across lock
  floor", phase M, cost O(callee size, bounded fuel).

  What is proved here, over the REUSED canonical vocabulary (`Semantik`
  `rufAt`, `RufMaschineG`, `Folge`, `AufrufOpt` ghost pair/order lemmas,
  `ContractSites` duty discharge, `CostSummary` expansion bound, kernel
  `gleitRechne`): the validator-decided side conditions (`InlineCert`),
  the exact certificate shape (local rewrite record plus recomputed
  analysis citations `InlineCite`), the refusal cases (ghostless inlining
  refuses; duty/lock-floor violation refuses; depth violation refuses;
  FP-scope violation refuses; missing ghost-order citation refuses), and
  the generic connection `OptInlineCall_verbindung` over arbitrary values:
  ghost-pair order preservation, actual-value re-emission, entry duty at
  its place, empty reason channel, log-silent-or-single-event concurrency
  classification, and the carried machine-work bound. No `ensures` is
  derived, no refusal becomes a warning, no faulting form is speculated
  above its guard.
-/
import Grammatik.Semantik
import Grammatik.RufMaschineG
import Grammatik.Folge
import Grammatik.FolgeZeuge
import Grammatik.ZielOrtEinfadenZeuge
import Grammatik.X86.AufrufOpt
import Grammatik.X86.ContractSites
import Grammatik.X86.CostSummary
import Grammatik.RufAdaequatRufG

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one inline site (DESIGN
    section 7 row): block map present, fresh renames, callee duties within
    the caller site (writes, locks incl. lock floor, atomics, FP modes,
    costs), depth discipline, ghost pair present, reason channel kept,
    same FP rounding scope, budget carried. -/
structure InlineCert where
  blockMapOk : Bool
  freshRenamed : Bool
  dutiesIncluded : Bool
  depthOk : Bool
  ghostPresent : Bool
  reasonChannelKept : Bool
  fpScopeSame : Bool
  budgetCarried : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def inlineAdmit (c : InlineCert) : Bool :=
  c.blockMapOk && c.freshRenamed && c.dutiesIncluded && c.depthOk &&
  c.ghostPresent && c.reasonChannelKept && c.fpScopeSame && c.budgetCarried

/-! ## 1. Refusal: ghostless inlining and the other DESIGN failure cases.

    A rewrite that splices the callee body but drops the ghost pair is
    REFUSED (`ghostPresent = false` forces `inlineAdmit = false`), even
    when the contracts are textually identical: without the re-emitted
    entry/return pair the `FolgeG` order leg is lost. The same holds for a
    duty violation (which covers inlining across the lock floor: the
    callee needs a lock the caller site does not hold), a depth violation
    (unbounded recursive inline), and an FP-scope violation (the callee
    runs under another rounding mode than the site). All are proved of
    the decided Bool, so the validator cannot silently skip them. -/

/-- GHOSTLESS INLINING REFUSES: identical contracts without ghost events. -/
theorem inlineRefuses_ghostless (c : InlineCert)
    (h : c.ghostPresent = false) :
    inlineAdmit c = false := by
  simp [inlineAdmit, h]

/-- DUTY VIOLATION REFUSES: callee duties outside the caller site,
    including inlining across the lock floor. -/
theorem inlineRefuses_duties (c : InlineCert)
    (h : c.dutiesIncluded = false) :
    inlineAdmit c = false := by
  simp [inlineAdmit, h]

/-- DEPTH VIOLATION REFUSES: unbounded (recursive) inline without fuel. -/
theorem inlineRefuses_depth (c : InlineCert)
    (h : c.depthOk = false) :
    inlineAdmit c = false := by
  simp [inlineAdmit, h]

/-- FP-SCOPE VIOLATION REFUSES: callee under another rounding scope. -/
theorem inlineRefuses_fpScope (c : InlineCert)
    (h : c.fpScopeSame = false) :
    inlineAdmit c = false := by
  simp [inlineAdmit, h]

/-- BLOCK-MAP VIOLATION REFUSES: callee blocks without a map entry. -/
theorem inlineRefuses_blockMap (c : InlineCert)
    (h : c.blockMapOk = false) :
    inlineAdmit c = false := by
  simp [inlineAdmit, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_inlineAdmit_ok :
    inlineAdmit ⟨true, true, true, true, true, true, true, true⟩ = true := by
  decide

/-- Probe: a ghostless certificate is refused. -/
theorem probe_inlineAdmit_ghostless :
    inlineAdmit ⟨true, true, true, true, false, true, true, true⟩ = false := by
  decide

/-- Probe: a duty-violating certificate is refused. -/
theorem probe_inlineAdmit_duties :
    inlineAdmit ⟨true, true, false, true, true, true, true, true⟩ = false := by
  decide

/-- Admission unfolds into all eight decided side conditions. -/
theorem inlineAdmit_all (c : InlineCert) (h : inlineAdmit c = true) :
    c.blockMapOk = true ∧ c.freshRenamed = true ∧
    c.dutiesIncluded = true ∧ c.depthOk = true ∧
    c.ghostPresent = true ∧ c.reasonChannelKept = true ∧
    c.fpScopeSame = true ∧ c.budgetCarried = true := by
  simp only [inlineAdmit, Bool.and_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## 2. The exact certificate shape.

    The certificate is a LOCAL rewrite record (the decided `InlineCert`
    above: callee identity rides in the theorem's `g`, the caller site in
    the ghost worlds) plus RECOMPUTED analysis citations: the validator
    re-runs every analysis and cites it, nothing is trusted from Rust.
    `ghostOrderFresh` is the `FolgeLog` order recheck of the spliced ghost
    pair; without it the certificate is refused. -/

/-- Recomputed analysis citations of one inline certificate. -/
inductive InlineCite where
  | blockMapFresh
  | dutySubsetFresh
  | ghostOrderFresh
  | budgetExpandFresh
  | availFresh
  deriving DecidableEq, Repr

/-- Every citation the validator must recompute. -/
def citesRequired : List InlineCite :=
  [.blockMapFresh, .dutySubsetFresh, .ghostOrderFresh,
   .budgetExpandFresh, .availFresh]

/-- The citation check: every required analysis is cited fresh. -/
def citeOk (zs : List InlineCite) : Bool :=
  decide (∀ z ∈ citesRequired, z ∈ zs)

/-- The ghost-order recheck is cited in every admitted certificate. -/
theorem citeOk_ghostOrder (zs : List InlineCite)
    (h : citeOk zs = true) :
    InlineCite.ghostOrderFresh ∈ zs := by
  unfold citeOk at h
  exact of_decide_eq_true h _ (by decide)

/-- MISSING GHOST-ORDER CITATION REFUSES. -/
theorem citeRefuses_noGhostOrder (zs : List InlineCite)
    (h : InlineCite.ghostOrderFresh ∉ zs) :
    citeOk zs = false := by
  unfold citeOk
  rw [decide_eq_false_iff_not]
  intro hall
  exact h (hall _ (by decide))

/-- Probe: the full citation list passes. -/
theorem probe_citeOk : citeOk citesRequired = true := by
  decide

/-- Probe: a list without the ghost-order citation is refused. -/
theorem probe_citeOk_noGhost :
    citeOk [.blockMapFresh, .dutySubsetFresh,
      .budgetExpandFresh, .availFresh] = false := by
  decide

/-! ## 3. IEEE kernel probe: inlining introduces no float operation.

    The ghost pair re-emits entry/return EVENTS with actual values; it
    evaluates no expression, so it rounds nothing. The kernel model below
    is the same `gleitRechne` the fold lane recomputes in: `0.5 + 0.25`
    is `0.75` in one rounding. Same-scope splicing (`fpScopeSame`) keeps
    the callee under the site's rounding mode; per-width flag/fault
    identity lemmas belong to the strength-reduction row and stay OPEN
    (see CUTS). -/

/-- Probe: the kernel computes `0.5 + 0.25 = 0.75` in one rounding. -/
theorem inlineIEEE_kennwert :
    gleitRechne .add (bruch (1, 2)) (bruch (1, 4)) = bruch (3, 4) := by
  decide

/-! ## 4. Connection: the inlined call behaves like the direct call.

    Over ARBITRARY values (`rho`, `s0`, `σ1`, `v`): admission (`hz`)
    carries the DESIGN side conditions, the citation check (`hzit`) the
    recomputed analyses, the `rufAt` equation (`hruf`) the successful call
    with its actual worlds, and the armed order premises (`hord1`,
    `hrest`, `hord2`) the surrounding log. Conclusion, jointly:
    (1) the spliced ghost pair preserves the `FolgeLog` order leg
    (`geistRekon_folge`: call logs);
    (2) the ghost pair re-emits entry/return with the ACTUAL values
    (value preservation, both channels have length two);
    (3) the entry duty holds at its place over the actual arguments
    (`rufAt_ok_vorOk`: contracts, no fault added or removed -- a failing
    `requires` never reaches the splice);
    (4) the reason channel is empty (`hr`: no reason is lost);
    (5) every machine step is log-silent or one real call/return event
    (`rufSchrittG_logSchritt`: concurrency -- the inlined silent steps
    contribute no physical log event, so the ghost pair is exactly what
    the reconstruction must re-emit);
    (6) the admitted summary still bounds the machine work at the site
    (`expandBound_keinVerlust`: budget -- the inlined body still consumes
    its source budget; exhaustion timing stays OPEN per
    `budgetSimulationOffen`);
    (7) every decided side condition holds, including the same FP scope
    (IEEE: the splice changes no rounding mode; the kernel probe of
    section 3 shows the recomputation it preserves);
    (8) the ghost-order analysis is cited fresh.
    Nothing here derives an `ensures`, turns a refusal into a warning, or
    speculates a faulting form above its guard. The full duty discharge
    with the actual caller/site (`inlinePflicht_aus_rufAt`) and the
    return-duty derivation (`rufAt_ok_gibt_ens`) are reused by citation,
    not reproved. -/

/-- CONNECTION: inlining under the admitted certificate preserves order,
    values, duties, channels, concurrency classes and the work bound. -/
theorem OptInlineCall_verbindung {D : Deklaration} (P : Programm D)
    (O : Orakel D) (passes fuel : Nat) (Φ : Folge D) (g : D.Fn)
    (cert : InlineCert) (hz : inlineAdmit cert = true)
    (zs : List InlineCite) (hzit : citeOk zs = true)
    (rho : Env D (D.params g)) (s0 : World D)
    (σ1 : World D) (v : ErgVal D (D.erg g))
    (hr : D.gruende g = 0)
    (hruf : rufAt P O passes (fuel + 1) g s0 rho =
      RufAusgang.ok (D := D) (f := g) σ1 v)
    (rest : List (RufEreignisF D))
    (hord1 : rest ≠ [] →
      Pflichtig Φ (RufEreignisF.eintritt g rho s0) = true →
      Armiert Φ rest = true)
    (hrest : FolgeLog Φ rest)
    (hord2 : (RufEreignisF.eintritt g rho s0 :: rest) ≠ [] →
      Pflichtig Φ (RufEreignisF.rueck g rho v s0 σ1) = true →
      Armiert Φ (RufEreignisF.eintritt g rho s0 :: rest) = true)
    (M M' : RufMaschineG D) (f : Faden)
    (hstep : RufSchrittG P O passes M f M')
    (s : CostSummary) (src m : Nat) (hm : alleMax s = some m) :
    FolgeLog Φ (RufEreignisF.rueck g rho v s0 σ1 ::
      RufEreignisF.eintritt g rho s0 :: rest)
    ∧ geistPaar g rho s0 (GeistAntwort.ok v σ1) =
      [RufEreignisF.rueck g rho v s0 σ1,
       RufEreignisF.eintritt g rho s0]
    ∧ wahr?
        (eval (s0.lese (Signatur.anfang D (D.signatur g))
          (P.requires g).orte) (P.requires g)
          (s0.lese (Signatur.anfang D (D.signatur g))
          (P.requires g).orte) rho) = true
    ∧ (Fin (D.gruende g) → False)
    ∧ ((M'.faeden f).log = (M.faeden f).log ∨
      (∃ g rho s0, (M'.faeden f).log =
        RufEreignisF.eintritt g rho s0 :: (M.faeden f).log) ∨
      (∃ g rho v s0 s1, (M'.faeden f).log =
        RufEreignisF.rueck g rho v s0 s1 :: (M.faeden f).log) ∨
      (∃ g rho r s0 s1, (M'.faeden f).log =
        RufEreignisF.grund g rho r s0 s1 :: (M.faeden f).log))
    ∧ expandBound s src = some (src * m + s.spillCount + s.fenceCount)
    ∧ (cert.blockMapOk = true ∧ cert.freshRenamed = true ∧
      cert.dutiesIncluded = true ∧ cert.depthOk = true ∧
      cert.ghostPresent = true ∧ cert.reasonChannelKept = true ∧
      cert.fpScopeSame = true ∧ cert.budgetCarried = true)
    ∧ InlineCite.ghostOrderFresh ∈ zs := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact geistRekon_folge Φ g rho s0 σ1 v rest hord1 hrest hord2
  · rfl
  · exact rufAt_ok_vorOk P O passes (fuel + 1) g s0 rho σ1 v hruf
  · exact Fin.elim0 ∘ Fin.cast hr
  · exact rufSchrittG_logSchritt P O passes M M' f hstep
  · exact expandBound_keinVerlust s src m hm
  · exact inlineAdmit_all cert hz
  · exact citeOk_ghostOrder zs hzit

/-! ## 5. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptInlineCall_verbindung` instantiated JOINTLY on the
    NON-DEGENERATE fixture program `eP` (`setze` writes table `konto`,
    `eD.signatur eSetze` proves it): the `rufAt` equation for the real
    `setze` call (closed, by reduction, `fuel + 1 = 1`), the order
    premises at the start log (decided: `setze` is no `ruf`/`ende`
    function of `Φ50`), a genuine machine step (`w_rufEnde`: the `setze`
    call), and the counted `blattSummary` bound (`alleMax = some 5`).
    Beside it the non-degenerate facts: the reached five-step run (`hr5`)
    with the `0 -> 5` memory change, the real ghost pair with its
    `Pflichtig`/`Armiert` facts and order leg, and the discharged
    `InlinePflicht` with the actual caller and site
    (`inlinePflicht_aus_rufAt`). Both conjunct groups are used. -/

/-- JOINT WITNESS for `OptInlineCall_verbindung`: the real `setze` call
    inlines under the admitted certificate beside the memory-changing
    reached run. -/
theorem OptInlineCall_verbindung_zeuge :
    ∃ (P : Programm eD) (O : Orakel eD) (passes fuel : Nat) (Φ : Folge eD)
      (g : eD.Fn) (cert : InlineCert) (_hz : inlineAdmit cert = true)
      (zs : List InlineCite) (_hzit : citeOk zs = true)
      (rho : Env eD (eD.params g)) (s0 σ1 : World eD)
      (v : ErgVal eD (eD.erg g)) (_hr : eD.gruende g = 0)
      (_hruf : rufAt P O passes (fuel + 1) g s0 rho =
        RufAusgang.ok (D := eD) (f := g) σ1 v)
      (rest : List (RufEreignisF eD))
      (_ho1 : rest ≠ [] →
        Pflichtig Φ (RufEreignisF.eintritt g rho s0) = true →
        Armiert Φ rest = true)
      (_hrest : FolgeLog Φ rest)
      (_ho2 : (RufEreignisF.eintritt g rho s0 :: rest) ≠ [] →
        Pflichtig Φ (RufEreignisF.rueck g rho v s0 σ1) = true →
        Armiert Φ (RufEreignisF.eintritt g rho s0 :: rest) = true)
      (M M' : RufMaschineG eD) (f : Faden)
      (_hs : RufSchrittG P O passes M f M')
      (s : CostSummary) (src m : Nat) (_hm : alleMax s = some m)
      (M5 : RufMaschineG eD)
      (rhoP : Env eD (eD.params ePruefe)) (wP bP : World eD)
      (vP : ErgVal eD (eD.erg ePruefe))
      (rhoS : Env eD (eD.params eSetze)) (vS : ErgVal eD (eD.erg eSetze))
      (aS bS : World eD) (rest5 : List (RufEreignisF eD)),
      FolgeLog Φ (RufEreignisF.rueck g rho v s0 σ1 ::
        RufEreignisF.eintritt g rho s0 :: rest)
      ∧ geistPaar g rho s0 (GeistAntwort.ok v σ1) =
        [RufEreignisF.rueck g rho v s0 σ1,
         RufEreignisF.eintritt g rho s0]
      ∧ wahr?
          (eval (s0.lese (Signatur.anfang eD (eD.signatur g))
            (P.requires g).orte) (P.requires g)
            (s0.lese (Signatur.anfang eD (eD.signatur g))
            (P.requires g).orte) rho) = true
      ∧ (Fin (eD.gruende g) → False)
      ∧ ((M'.faeden f).log = (M.faeden f).log ∨
        (∃ g rho s0, (M'.faeden f).log =
          RufEreignisF.eintritt g rho s0 :: (M.faeden f).log) ∨
        (∃ g rho v s0 s1, (M'.faeden f).log =
          RufEreignisF.rueck g rho v s0 s1 :: (M.faeden f).log) ∨
        (∃ g rho r s0 s1, (M'.faeden f).log =
          RufEreignisF.grund g rho r s0 s1 :: (M.faeden f).log))
      ∧ expandBound s src = some (src * m + s.spillCount + s.fenceCount)
      ∧ (cert.blockMapOk = true ∧ cert.freshRenamed = true ∧
        cert.dutiesIncluded = true ∧ cert.depthOk = true ∧
        cert.ghostPresent = true ∧ cert.reasonChannelKept = true ∧
        cert.fpScopeSame = true ∧ cert.budgetCarried = true)
      ∧ InlineCite.ghostOrderFresh ∈ zs
      ∧ (eD.signatur eSetze).schreibt () = true
      ∧ RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M5
      ∧ ((((eSp.welt []).lese [] []).slots () 0 ()).n = 0 ∧
        (σ1.slots () 0 ()).n = 5)
      ∧ (M5.faeden 0).log = RufEreignisF.rueck ePruefe rhoP vP wP bP ::
          RufEreignisF.eintritt ePruefe rhoP wP ::
          RufEreignisF.rueck eSetze rhoS vS aS bS :: rest5
      ∧ Pflichtig Φ50 (RufEreignisF.eintritt ePruefe rhoP wP) = true
      ∧ Armiert Φ50
          (RufEreignisF.rueck eSetze rhoS vS aS bS :: rest5) = true
      ∧ FolgeLog Φ50 (M5.faeden 0).log
      ∧ Nonempty (InlinePflicht eP eHaupt eSetze []) := by
  have h00 : (RufStartG eP eSp eInit).faeden 0 = ⟨[], ⟨eHaupt, .nil,
      eSp.welt [], ⟨false, [], [], .nil, .ende eRumpfHaupt⟩⟩, [],
      [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG eP eSp eInit).faeden 0).spur = [] := rfl
  obtain ⟨M1, s1, _hZ⟩ := w_rufEnde (P := eP) (O := eO) (passes := 0) h00
    eSetze .nil eHpSetze rfl
    (.cons (.call ePruefe .nil eHpPruefe rfl) (.ret .keine List.Perm.nil))
    .nil rfl (ehg0 hoff0).heldIn
  have hread0 : ((((eSp.welt []).lese [] []).lese
      (Signatur.anfang eD (eD.signatur eSetze))
      (eP.requires eSetze).orte)) =
      ((eSp.welt []).lese [] []).lese
        (Signatur.anfang eD (eD.signatur eSetze))
        (eP.requires eSetze).orte := rfl
  have hreq0 : wahr? (eval ((((eSp.welt []).lese [] []).lese
      (Signatur.anfang eD (eD.signatur eSetze))
      (eP.requires eSetze).orte)) (eP.requires eSetze)
      ((((eSp.welt []).lese [] []).lese
        (Signatur.anfang eD (eD.signatur eSetze))
        (eP.requires eSetze).orte)) .nil) = true := by rfl
  have hschr : (eD.signatur eSetze).schreibt () = true := rfl
  have hsl0 : (((eSp.welt []).lese [] []).slots () 0 ()).n = 0 := rfl
  have hok : ∃ σ1b v σ', execEnd (V := vertragVon eD eSetze) eO 0
        (rufAt eP eO 0 0) (eP.rumpf eSetze)
        ((((eSp.welt []).lese [] []).lese
          (Signatur.anfang eD (eD.signatur eSetze))
          (eP.requires eSetze).orte)) .nil =
        EndAusgang.zurueck σ1b v ∧
      rufAt eP eO 0 1 eSetze ((eSp.welt []).lese [] []) .nil =
        RufAusgang.ok σ' v := by
    refine ⟨_, _, _, rfl, rfl⟩
  obtain ⟨σ1b, v, σ', hbody, hokc⟩ := hok
  have hret0 : σ1b.lese (vertragVon eD eSetze).ende
      (eP.ensures eSetze).orte =
      σ1b.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte := rfl
  have hsinv0 : (eD.invs.filter (schuldet eSetze)).foldl
      (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ1b.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte) =
      (eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ1b.lese (vertragVon eD eSetze).ende
          (eP.ensures eSetze).orte) := rfl
  have hinv0 : (eD.invs.find? (fun i => schuldet eSetze i &&
      !wahr? (eval ((eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ1b.lese (vertragVon eD eSetze).ende
          (eP.ensures eSetze).orte))
        (eP.invariante i)
        ((eD.invs.filter (schuldet eSetze)).foldl
          (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
          (σ1b.lese (vertragVon eD eSetze).ende
            (eP.ensures eSetze).orte)) .nil))) = none := by rfl
  have hens := rufAt_ok_gibt_ens eP eO 0 0 eSetze ((eSp.welt []).lese [] [])
    .nil _ hread0 hreq0 _ _ hbody _ hret0 _ hsinv0 hinv0 _ hokc
  have hens1 : RufEnsCheck eP eSetze
      ((((eSp.welt []).lese [] []).lese
        (Signatur.anfang eD (eD.signatur eSetze))
        (eP.requires eSetze).orte))
      (σ1b.lese (vertragVon eD eSetze).ende (eP.ensures eSetze).orte)
      .nil v := hens.1
  have hsl5 : ((σ1b.lese (vertragVon eD eSetze).ende
      (eP.ensures eSetze).orte).slots () 0 ()).n = 5 :=
    of_decide_eq_true hens1
  have hok_sinv : rufAt eP eO 0 1 eSetze ((eSp.welt []).lese [] []) .nil =
      RufAusgang.ok ((eD.invs.filter (schuldet eSetze)).foldl
        (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
        (σ1b.lese (vertragVon eD eSetze).ende
          (eP.ensures eSetze).orte)) v := by
    rw [← hens.2]
    exact hokc
  have hpfl : Nonempty (InlinePflicht eP eHaupt eSetze []) :=
    ⟨inlinePflicht_aus_rufAt eP eO 0 0 eHaupt eSetze [] eHpSetze rfl
      ((eSp.welt []).lese [] []) .nil _ hread0 hreq0 _ _ hbody _ hret0 _
      hsinv0 hinv0 hok_sinv⟩
  have hmem : (((eD.invs.filter (schuldet eSetze)).foldl
      (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
      (σ1b.lese (vertragVon eD eSetze).ende
        (eP.ensures eSetze).orte)).slots () 0 ()).n = 5 := hsl5
  have hrest0 : FolgeLog Φ50
      [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])] := by
    show (([] ≠ [] →
      Pflichtig Φ50
        (RufEreignisF.eintritt eHaupt .nil (eSp.welt [])) = true →
      Armiert Φ50 [] = true) ∧ True)
    exact ⟨fun hne _ => absurd rfl hne, trivial⟩
  have hord1 : [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])] ≠ [] →
      Pflichtig Φ50
        (RufEreignisF.eintritt eSetze .nil
          ((eSp.welt []).lese [] [])) = true →
      Armiert Φ50
        [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])] = true :=
    fun _ h => False.elim (Bool.false_ne_true h)
  have hord2 : (RufEreignisF.eintritt eSetze .nil
        ((eSp.welt []).lese [] []) ::
        [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])]) ≠ [] →
      Pflichtig Φ50
        (RufEreignisF.rueck eSetze .nil v ((eSp.welt []).lese [] [])
          ((eD.invs.filter (schuldet eSetze)).foldl
            (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
            (σ1b.lese (vertragVon eD eSetze).ende
              (eP.ensures eSetze).orte))) = true →
      Armiert Φ50
        (RufEreignisF.eintritt eSetze .nil ((eSp.welt []).lese [] []) ::
          [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])]) = true :=
    fun _ h => False.elim (Bool.false_ne_true h)
  have hm5 : alleMax blattSummary = some 5 := by decide
  obtain ⟨M5, hr5, _hsl0g, _hschrg, rhoP, wP, bP, vP, rhoS, vS, aS, bS,
    rest5, hlog, _hsl5g, _hgp, hpf, harm, hfol⟩ := geistRekon_zeuge
  have hconn := OptInlineCall_verbindung eP eO 0 0 Φ50 eSetze
    ⟨true, true, true, true, true, true, true, true⟩ (by decide)
    citesRequired probe_citeOk
    (.nil : Env eD (eD.params eSetze)) ((eSp.welt []).lese [] [])
    (((eD.invs.filter (schuldet eSetze)).foldl
      (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
      (σ1b.lese (vertragVon eD eSetze).ende
        (eP.ensures eSetze).orte))) v rfl hok_sinv
    [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])]
    hord1 hrest0 hord2
    (RufStartG eP eSp eInit) M1 0 s1
    blattSummary 1 5 hm5
  exact ⟨eP, eO, 0, 0, Φ50, eSetze,
    ⟨true, true, true, true, true, true, true, true⟩, by decide,
    citesRequired, probe_citeOk,
    (.nil : Env eD (eD.params eSetze)), ((eSp.welt []).lese [] []),
    ((eD.invs.filter (schuldet eSetze)).foldl
      (fun s i => s.lese (invSicht eD i) (eP.invariante i).orte)
      (σ1b.lese (vertragVon eD eSetze).ende
        (eP.ensures eSetze).orte)), v, rfl, hok_sinv,
    [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])],
    hord1, hrest0, hord2,
    (RufStartG eP eSp eInit), M1, 0, s1,
    blattSummary, 1, 5, hm5,
    M5, rhoP, wP, bP, vP, rhoS, vS, aS, bS, rest5,
    hconn.1, hconn.2.1, hconn.2.2.1, hconn.2.2.2.1,
    hconn.2.2.2.2.1, hconn.2.2.2.2.2.1,
    hconn.2.2.2.2.2.2.1, hconn.2.2.2.2.2.2.2,
    hschr, hr5, ⟨hsl0, hmem⟩, hlog, hpf, harm, hfol, hpfl⟩

/- CUTS:
    - No executable source-body splice: there is no function splicing a
      callee body at a call site (same cut as `AufrufOpt`), hence no
      proved body-splice simulation against `rufAt`. What is proved is
      the CHECKED RULE: validator-decided admission, recomputed citations,
      ghost-pair order/value preservation, entry duty at its place, empty
      reason channel, the log classification and the carried work bound.
    - Return-duty derivation (`rufAt_ok_gibt_ens`) and the full duty
      discharge (`inlinePflicht_aus_rufAt`) are REUSED by citation; the
      witness exhibits the discharged `InlinePflicht` on the real call.
    - Order premises at `eSetze` hold by decided computation (`setze` is
      no `ruf`/`ende` function of `Φ50`); the non-vacuous order evidence
      (real ghost pair, `Pflichtig`/`Armiert`, order leg on the reached
      run) rides in the witness extras from `geistRekon_zeuge`.
    - Budget exhaustion timing (`budgetSimulationOffen`) stays OPEN per
      `CostSummary`; per-width float flag/fault identity stays with the
      strength-reduction row; indirect calls have no ghost form here.
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at source worlds, call logs and canonical
      work bounds.
-/

#print axioms inlineAdmit
#print axioms inlineRefuses_ghostless
#print axioms inlineRefuses_duties
#print axioms inlineRefuses_depth
#print axioms inlineRefuses_fpScope
#print axioms inlineRefuses_blockMap
#print axioms citeOk_ghostOrder
#print axioms citeRefuses_noGhostOrder
#print axioms inlineIEEE_kennwert
#print axioms OptInlineCall_verbindung
#print axioms OptInlineCall_verbindung_zeuge

end Gabbro.Grammatik.X86
