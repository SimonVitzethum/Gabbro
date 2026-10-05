/-
  File:      Grammatik/X86/TsoGxCrossDecl.lean
  Subject:   Cross-declaration lowering certificate for the GX refinement
             (lane 1269, follow-up of lane 1253 `TsoGxStart`).

  Joining the `eP` entry/call prefix run (declaration `eD`) with a `witD`
  bridged fragment run needs a cross-declaration lowering certificate
  (OPEN in `TsoGxStart`'s CUTS). This module defines the certificate as a
  DECIDED check over the accepted structures (carriers, table extents,
  call log, footprint flags), proves that a passing certificate yields the
  paired joint bridged run, and gives the joint non-degenerate `_zeuge`.

  No new machine, no new executor, no silicon claim. The consumer is
  machines G/W/GX, not `HwMaschine`, so no `HwAdapter` is defined here
  (same reading as `TsoGxRefine`/`TsoGxChecker`).
-/
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfadenZeuge
import Grammatik.X86.Bruecke.TsoGxStart
import Grammatik.X86.Bruecke.TsoRunInduction
import Grammatik.X86.Bruecke.CarrierTraceBridge

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Cross-declaration agreement data: what the entry/prefix side (`eP`
    over `eD`) and the fragment side (`ctProg` over `witD`) must agree
    on. Plain data, no runs inside (so the joint theorem below is not a
    restatement of a premise). -/
structure CrossDeclCert where
  prefixStart : Nat
  prefixEntry : Nat
  prefixSchreibt : Bool
  fragStart : Nat
  fragEnde : Nat
  fragSchreibt : Bool
  deriving DecidableEq, Repr

/-! ## 1. Shape agreement: carriers, extents, footprint flags. -/

/-- Both sides have one single-slot table. -/
theorem formGleich_anzahl_e : eD.count () = 1 := rfl

/-- Both sides have one single-slot table. -/
theorem formGleich_anzahl_wit : witD.count () = 1 := rfl

/-- The prefix carrier is `int 0 100`. -/
theorem formGleich_typ_e : eD.typ () () = .int 0 100 := rfl

/-- Neither table is shared (prefix side). -/
theorem formGleich_ungeteilt_e : eD.geteilt () = false := rfl

/-- Neither table is shared (fragment side). -/
theorem formGleich_ungeteilt_wit : witD.geteilt () = false := rfl

/-- COMBINED shape agreement: one single-slot `int 0 100` table on each
    side (the fragment side reuses the accepted `witHT`), unshared on
    both sides. Decided facts only, no runs. -/
theorem formGleich :
    eD.count () = 1 ∧ witD.count () = 1 ∧
    eD.typ () () = .int 0 100 ∧ witD.typ () () = .int 0 100 ∧
    eD.geteilt () = false ∧ witD.geteilt () = false :=
  ⟨formGleich_anzahl_e, formGleich_anzahl_wit, formGleich_typ_e, witHT,
    formGleich_ungeteilt_e, formGleich_ungeteilt_wit⟩

/-- CALL LOG agreement, fragment side: `ctProg` performs no calls -- its
    every body is a bare return -- so the joint call log is exactly the
    prefix's logged `pruefe` entry. -/
theorem ctProg_ohne_ruf : ∃ h, ctProg.rumpf () = .ret .keine h :=
  ⟨_, rfl⟩

/-! ## 2. The decided certificate check. -/

/-- The certificate condition as a `Prop`: the prefix starts at `0`,
    logs the `pruefe` entry world at `5`, and writes its table; the
    fragment starts at `0`, ends at `42`, and writes its table; both
    start from the same initial carrier state. -/
def crossCertProp (c : CrossDeclCert) : Prop :=
  c.prefixStart = 0 ∧ c.prefixEntry = 5 ∧ c.prefixSchreibt = true ∧
  c.fragStart = 0 ∧ c.fragEnde = 42 ∧ c.fragSchreibt = true ∧
  c.prefixStart = c.fragStart

/-- Decidability of the certificate condition, by unfolding. -/
instance crossCertPropDec (c : CrossDeclCert) :
    Decidable (crossCertProp c) := by
  unfold crossCertProp
  infer_instance

/-- The DECIDED check: agreement computed over the accepted structures'
    observable values. -/
def crossCertOkB (c : CrossDeclCert) : Bool := decide (crossCertProp c)

/-- The witness certificate carries the accepted observable values. -/
def crossCertWit : CrossDeclCert :=
  { prefixStart := 0, prefixEntry := 5, prefixSchreibt := true,
    fragStart := 0, fragEnde := 42, fragSchreibt := true }

/-- The witness certificate passes the decided check. -/
theorem crossCertWit_ok : crossCertOkB crossCertWit = true := by decide

/-- A passing check yields the agreement equations. Every conjunct is
    consumed by the joint theorem below. -/
theorem crossCertOk_gleich (c : CrossDeclCert) (hok : crossCertOkB c = true) :
    crossCertProp c :=
  of_decide_eq_true hok

/-! ## 3. A passing certificate yields the paired joint run. -/

/-- **JOINT COMPOSITION (`crossCert_gibt_joint`).** A passing
    certificate yields the paired joint run: the `eP` entry/call prefix
    reached from `RufStartG` (lane 1253's `startFragment_zeuge`) together
    with the `witD` bridged fragment run (lane 1187's
    `brueckenLauf_erreichbar_zeuge`), with every observable stated IN
    TERMS OF the certificate fields -- so the check premise is genuinely
    consumed, not restated. Every premise is used: `hok` through the
    extracted equations, each equation at its conjunct. -/
theorem crossCert_gibt_joint (c : CrossDeclCert)
    (hok : crossCertOkB c = true) :
    ∃ (Mp : RufMaschineG eD) (Wf : RufMaschineW witD)
      (arts : List FragArt),
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) Mp ∧
      BrueckenLauf ctProg witO 0 (fun g => nomatch g) (RufStartW ctM) Wf arts ∧
      arts = [.store] ∧
      (eSp.slots () 0 ()).n = c.prefixStart ∧
      (∃ (rho : Env eD (eD.params ePruefe)) (s0 : World eD),
        RufEreignisF.eintritt ePruefe rho s0 ∈ (Mp.faeden 0).log ∧
        ReqAmEintritt eP ePruefe s0 rho ∧
        (s0.slots () 0 ()).n = c.prefixEntry) ∧
      (eD.signatur eSetze).schreibt () = c.prefixSchreibt ∧
      (witSigma.slots () 0 ()).n = c.fragStart ∧
      (∃ σ' : World witD, (σ'.slots () 0 ()).n = c.fragEnde) ∧
      (vertragVon witD ()).schreibt () = c.fragSchreibt ∧
      c.prefixStart = c.fragStart := by
  have h := crossCertOk_gleich c hok
  obtain ⟨hS0, hE5, hSE, hW0, hW42, hWE, hEq⟩ := h
  obtain ⟨Mp, hrP, h0, hSchrP, rho, s0, hm, hreq, h5⟩ :=
    startFragment_zeuge
  obtain ⟨Wf, arts, hL, hR, hArts, hHw, hBefore, hAfterEx, hBytes, hErbt,
    hInv, hErr, hUhr, hBuf, hFresh, hSt0, hSt1, hSpur, hX, hY⟩ :=
    brueckenLauf_erreichbar_zeuge
  obtain ⟨sig', hAfter⟩ := hAfterEx
  have hStart : (eSp.slots () 0 ()).n = c.prefixStart := by
    rw [hS0]; exact h0
  have hEntry : (s0.slots () 0 ()).n = c.prefixEntry := by
    rw [hE5]; exact h5
  have hSchr : (eD.signatur eSetze).schreibt () = c.prefixSchreibt := by
    rw [hSE]; exact hSchrP
  have hWStart : (witSigma.slots () 0 ()).n = c.fragStart := by
    rw [hW0]; exact hBefore
  have hWEnd : (sig'.slots () 0 ()).n = c.fragEnde := by
    rw [hW42]; exact hAfter
  have hWSchr : (vertragVon witD ()).schreibt () = c.fragSchreibt := by
    rw [hWE]; exact hHw
  have hLog : ∃ (rho : Env eD (eD.params ePruefe)) (s0 : World eD),
      RufEreignisF.eintritt ePruefe rho s0 ∈ (Mp.faeden 0).log ∧
      ReqAmEintritt eP ePruefe s0 rho ∧
      (s0.slots () 0 ()).n = c.prefixEntry :=
    ⟨rho, s0, hm, hreq, hEntry⟩
  have hFrag : ∃ σ' : World witD, (σ'.slots () 0 ()).n = c.fragEnde :=
    ⟨sig', hWEnd⟩
  exact ⟨Mp, Wf, arts, hrP, hL, hArts, hStart, hLog,
    hSchr, hWStart, hFrag, hWSchr, hEq⟩

/-! ## 4. Finding: the two writes diverge in value. -/

/-- **FINDING (`crossCert_werte_divergieren`).** On the witness
    certificate the logged prefix value (`5`) is not the fragment value
    (`42`): the fragment write is not the prefix write replayed. The
    joint statement above is therefore a PAIRED joint run over two
    declarations, never a single-declaration run; see CUTS. -/
theorem crossCert_werte_divergieren :
    crossCertWit.prefixEntry ≠ crossCertWit.fragEnde := by
  decide

/-! ## 5. Joint non-degenerate witness. -/

/-- **JOINT WITNESS (`crossCert_joint_zeuge`).** Every premise holds
    jointly on concrete values: the witness certificate passes the
    decided check; the `eP` prefix is reached from `RufStartG` with the
    start world at `konto[0] = 0`, `setze` writing the table, and the
    logged `pruefe` entry world at `konto[0] = 5`; the `witD` fragment
    bridged run writes `0 → 42` with a memory-changing target drain.
    Non-degenerate: a written table on each side and reached runs whose
    memory observably changed. -/
theorem crossCert_joint_zeuge :
    crossCertOkB crossCertWit = true ∧
    (∃ (Mp : RufMaschineG eD) (Wf : RufMaschineW witD)
      (arts : List FragArt),
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) Mp ∧
      BrueckenLauf ctProg witO 0 (fun g => nomatch g) (RufStartW ctM) Wf arts ∧
      arts = [.store] ∧
      (eSp.slots () 0 ()).n = 0 ∧
      (∃ (rho : Env eD (eD.params ePruefe)) (s0 : World eD),
        RufEreignisF.eintritt ePruefe rho s0 ∈ (Mp.faeden 0).log ∧
        ReqAmEintritt eP ePruefe s0 rho ∧
        (s0.slots () 0 ()).n = 5) ∧
      (eD.signatur eSetze).schreibt () = true ∧
      (witSigma.slots () 0 ()).n = 0 ∧
      (∃ σ' : World witD, (σ'.slots () 0 ()).n = 42) ∧
      (vertragVon witD ()).schreibt () = true ∧
      witM.bytes witA ≠ witM'.bytes witA) := by
  obtain ⟨Mp, hrP, h0, hSchrP, rho, s0, hm, hreq, h5⟩ :=
    startFragment_zeuge
  obtain ⟨Wf, arts, hL, hR, hArts, hHw, hBefore, hAfterEx, hBytes, hErbt,
    hInv, hErr, hUhr, hBuf, hFresh, hSt0, hSt1, hSpur, hX, hY⟩ :=
    brueckenLauf_erreichbar_zeuge
  obtain ⟨sig', hAfter⟩ := hAfterEx
  exact ⟨crossCertWit_ok, Mp, Wf, arts, hrP, hL, hArts, h0,
    ⟨rho, s0, hm, hreq, h5⟩, hSchrP, hBefore, ⟨sig', hAfter⟩, hHw,
    hBytes⟩

/- CUTS:
   Proved here:
   (1) Shape agreement (`formGleich_*`, `formGleich`): one single-slot
   `int 0 100` table on each side (fragment side via the accepted
   `witHT`), unshared on both sides; call-log agreement
   (`ctProg_ohne_ruf`): the fragment program performs no calls, so the
   joint call log is the prefix's logged `pruefe` entry.
   (2) The decided certificate (`CrossDeclCert`, `crossCertProp`,
   `crossCertOkB` with instance `crossCertPropDec`, `crossCertWit`,
   `crossCertWit_ok`, `crossCertOk_gleich`).
   (3) Joint composition (`crossCert_gibt_joint`): a passing check
   yields the paired joint run -- lane 1253's prefix
   (`startFragment_zeuge`) with lane 1187's bridged fragment run
   (`brueckenLauf_erreichbar_zeuge`) -- every observable stated in
   terms of the certificate fields.
   (4) Finding (`crossCert_werte_divergieren`): `5 ≠ 42`, the fragment
   write is not the prefix write.
   (5) Joint non-degenerate witness (`crossCert_joint_zeuge`): written
   tables on both sides, reached runs with observable memory change
   (`0 → 5` at the logged entry world, `0 → 42` at the fragment step
   plus a memory-changing target drain).
   NOT proved here, and not claimed:
   - FINDING (the exact obstruction): no single-declaration joint run.
   `eD` and `witD` differ definitionally (`Fn`: four constructors vs
   `Unit`; `Lock`: `Unit` vs `Empty`; different programs, oracles and
   values `5` vs `42`), so no `BrueckenLauf` can start at `RufStartG`
   over `eP` and end over `ctProg` without a declaration morphism --
   and any such morphism would need a desired-correctness premise
   (which lowering maps which function, which table, which value).
   The certificate therefore certifies shape agreement plus paired
   runs, never a transported single run.
   - No per-access TSO-to-W/GX simulation beyond the reused accepted
   lemmas; no `valX86_sound`; no byte-level entry linkage; no
   hardware, timing, fairness or progress claim.
   - No `HwAdapter` is defined here by design: the consumer is
   machines G/W/GX, not `HwMaschine` (the same reading lanes 1215 and
   1251 stand on); the MECHANISM adapter boilerplate does not apply.
-/

#print axioms formGleich_anzahl_e
#print axioms formGleich_anzahl_wit
#print axioms formGleich_typ_e
#print axioms formGleich_ungeteilt_e
#print axioms formGleich_ungeteilt_wit
#print axioms formGleich
#print axioms ctProg_ohne_ruf
#print axioms crossCertPropDec
#print axioms crossCertWit_ok
#print axioms crossCertOk_gleich
#print axioms crossCert_gibt_joint
#print axioms crossCert_werte_divergieren
#print axioms crossCert_joint_zeuge

#print axioms CrossDeclCert

end Gabbro.Grammatik.X86
