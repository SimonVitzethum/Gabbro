/-
  File:      Grammatik/X86/OptRetPathSel.lean
  Subject:   Return-path selection with callee-saved restores (lane 895).

  DESIGN section 7 row "Layout / allocation": local premise "spills fresh
  private frame slots, token-threaded, save/restore on all paths",
  certificate "B+C map", failure cases "fused 16-byte spill over two live
  carriers; spill slot overlapping neighbour frame; address-taken spill
  via call arg", phase L. Plus DESIGN section 3A: "callee-saved restores
  on all paths, checked per call/return".

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Speicher`, `Ausfuehrung`, `StackUnwind`, and the `eD`/`eP` fixture for
  the joint witness): the optimiser may select return paths (route
  several returns through one shared epilogue) only where the validator
  re-decides, per call and per return, that the entry saves the
  callee-saved register and every selected return path restores it; a
  path with a missing restore refuses loudly, never silently. The
  connection is generic over arbitrary registers and values: save
  (`push64 r`) plus selected-path restore (`pop64 r`) plus `ret` keeps
  the callee-saved value, the stack top, the return address, the flags
  and every permission map. No `ensures` is derived, no refusal becomes
  a warning, no faulting form is speculated above its guard.

  No accepted shared IR is present in the tree, so the rule is stated
  over the canonical machine steps plus the certificate record the
  future validator re-decides (IR-VALIDIERUNG layer A local rewrite plus
  layer B/C recomputed citations, carried here as checked data).
-/
import Grammatik.X86.StackUnwind
import Grammatik.ZielOrtEinfadenZeuge

namespace Gabbro.Grammatik.X86

/-- Per-path restore check (validator-decided): the selected return path
    ends in the restore `pop64 r` and `ret`. -/
def retPaarOk (dq dr : Decodiert) (r : Register) : Bool :=
  decide (dq.befehl = .pop64 r ∧ dr.befehl = .ret)

/-! ## 1. Certificate shape and admission.

    EXACT certificate shape (IR-VALIDIERUNG layer A + B/C):
    - layer A (local rewrite record): `pfade` (the selected return paths
      that share the epilogue) and `epilog` (the shared epilogue itself)
      plus `gesichert` (the entry save form);
    - layers B+C (validator-RECOMPUTED analysis citations, carried as
      checked data, never trusted from Rust): `alleOk` (every selected
      path restores, from recomputed path enumeration), `epilogOk` (the
      shared epilogue restores), `fremdOk` (no address-taken slot and no
      overlapping spill -- the DESIGN section 7 failure cases), `farbeOk`
      (colouring agrees with recomputed liveness). -/
structure RetPfadCert where
  pfade : List (List Befehl)
  epilog : List Befehl
  gesichert : Befehl
  alleOk : Bool
  epilogOk : Bool
  fremdOk : Bool
  farbeOk : Bool
  deriving DecidableEq, Repr

/-- Admission: every recomputed citation holds, the taken path restores
    `r`, the entry saves `r`, and the shared epilogue is exactly the
    restore pair. A refused OPTIONAL selection falls back to another
    certified translation, never to a warning. -/
def retPfadZulassen (c : RetPfadCert) (dq dr : Decodiert)
    (r : Register) : Bool :=
  c.alleOk && c.epilogOk && c.fremdOk && c.farbeOk &&
    retPaarOk dq dr r && decide (c.gesichert = .push64 r) &&
    decide (c.epilog = [.pop64 r, .ret])

/-- Admission pins the taken path's restore pair. Every conjunct of the
    admission is used: the four citations, the pair check, and both
    shape equations. -/
theorem retPaar_aus_zulassung (c : RetPfadCert) (dq dr : Decodiert)
    (r : Register) (hz : retPfadZulassen c dq dr r = true) :
    dq.befehl = .pop64 r ∧ dr.befehl = .ret ∧
      c.gesichert = .push64 r ∧ c.epilog = [.pop64 r, .ret] := by
  unfold retPfadZulassen at hz
  rw [Bool.and_eq_true] at hz
  obtain ⟨hz1, hepi⟩ := hz
  rw [Bool.and_eq_true] at hz1
  obtain ⟨hz2, hges⟩ := hz1
  rw [Bool.and_eq_true] at hz2
  have hzpaar : retPaarOk dq dr r = true := hz2.2
  unfold retPaarOk at hzpaar
  have hpaar := of_decide_eq_true hzpaar
  have hges' := of_decide_eq_true hges
  have hepi' := of_decide_eq_true hepi
  exact ⟨hpaar.1, hpaar.2, hges', hepi'⟩

/-! ## 2. Refusals: a missing restore never selects silently.

    A selected path whose tail is not `pop64 r` refuses; a selected
    path not ending in `ret` refuses; an address-taken or overlapping
    spill slot (DESIGN section 7 failure cases, recomputed `fremdOk`)
    refuses; a colouring/liveness mismatch (recomputed `farbeOk`)
    refuses. All refusals are loud `false`, never a warning. -/

/-- MISSING RESTORE REFUSES: a path ending in anything but `pop64 r`
    admits no return-path selection. -/
theorem retPfadVerweigert_fehlend (c : RetPfadCert) (dq dr : Decodiert)
    (r : Register) (h : dq.befehl ≠ .pop64 r) :
    retPfadZulassen c dq dr r = false := by
  have hneg : ¬(dq.befehl = .pop64 r ∧ dr.befehl = .ret) :=
    fun hh => h hh.1
  have hpaar : retPaarOk dq dr r = false := by
    unfold retPaarOk
    cases hdec : decide (dq.befehl = .pop64 r ∧ dr.befehl = .ret) with
    | true => exact absurd (of_decide_eq_true hdec) hneg
    | false => rfl
  unfold retPfadZulassen
  rw [hpaar]
  simp

/-- MISSING RETURN REFUSES: a path not ending in `ret` admits nothing. -/
theorem retPfadVerweigert_keinRet (c : RetPfadCert) (dq dr : Decodiert)
    (r : Register) (h : dr.befehl ≠ .ret) :
    retPfadZulassen c dq dr r = false := by
  have hneg : ¬(dq.befehl = .pop64 r ∧ dr.befehl = .ret) :=
    fun hh => h hh.2
  have hpaar : retPaarOk dq dr r = false := by
    unfold retPaarOk
    cases hdec : decide (dq.befehl = .pop64 r ∧ dr.befehl = .ret) with
    | true => exact absurd (of_decide_eq_true hdec) hneg
    | false => rfl
  unfold retPfadZulassen
  rw [hpaar]
  simp

/-- ADDRESS-TAKEN OR OVERLAPPING SPILL REFUSES (DESIGN section 7
    failure cases): a false `fremdOk` citation admits nothing. -/
theorem retPfadVerweigert_fremd (c : RetPfadCert) (dq dr : Decodiert)
    (r : Register) (h : c.fremdOk = false) :
    retPfadZulassen c dq dr r = false := by
  simp [retPfadZulassen, h]

/-- COLOURING/LIVENESS MISMATCH REFUSES: a false `farbeOk` citation
    admits nothing. -/
theorem retPfadVerweigert_farbe (c : RetPfadCert) (dq dr : Decodiert)
    (r : Register) (h : c.farbeOk = false) :
    retPfadZulassen c dq dr r = false := by
  simp [retPfadZulassen, h]

/-- Witness certificate: two selected paths sharing the `rbx` epilogue,
    every recomputed citation true. -/
def retPfadCertW : RetPfadCert :=
  { pfade := [[.movReg64 .rax .rbx, .pop64 .rbx, .ret],
      [.xorReg64 .rax .rax, .pop64 .rbx, .ret]]
    epilog := [.pop64 .rbx, .ret]
    gesichert := .push64 .rbx
    alleOk := true
    epilogOk := true
    fremdOk := true
    farbeOk := true }

/-- Probe: the fully admitted selection passes. -/
theorem probe_retPfadZulassen_ok :
    retPfadZulassen retPfadCertW ⟨.pop64 .rbx, 1⟩ ⟨.ret, 1⟩ .rbx = true := by
  decide

/-- Probe: a path with a missing restore is refused. -/
theorem probe_retPfadZulassen_fehlend :
    retPfadZulassen retPfadCertW ⟨.push64 .rax, 1⟩ ⟨.ret, 1⟩ .rbx
      = false := by
  decide

/-- Probe: a false spill citation is refused. -/
theorem probe_retPfadZulassen_fremd :
    retPfadZulassen { retPfadCertW with fremdOk := false }
      ⟨.pop64 .rbx, 1⟩ ⟨.ret, 1⟩ .rbx = false := by
  decide

/-! ## 3. Value and observation preservation.

    The save plus the selected-path restore of the SAME register is the
    accepted push/pop restoration: over arbitrary values the
    callee-saved value and the stack top survive. Call, save, selected
    restore and return move only the stack pointer, one register,
    memory bytes and control -- flags survive all four steps, so no
    downstream conditional observes the selection. -/

/-- VALUE PRESERVATION: entry save plus selected-path restore of the
    same register keeps the callee-saved value and the stack top, over
    arbitrary values. Every premise pins one guard of the two steps or
    of the read-back, via the accepted push/pop restoration. -/
theorem retPfad_wert_erhalten (s s1 s2 : Zustand) (r : Register)
    (d1 d2 : Decodiert) (m : Speicher) (v : Wort)
    (hok1 : laengeOk d1.laenge = true)
    (hb1 : d1.befehl = .push64 r)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register r) = some m)
    (hles : lesbar8 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      = true)
    (hstep1 : schritt d1 s = some s1)
    (hrd : read64 s1.speicher (s1.register Register.rsp) = some v)
    (hstep2 : schritt d2 s1 = some s2)
    (hok2 : laengeOk d2.laenge = true)
    (hb2 : d2.befehl = .pop64 r)
    (hdst : r ≠ Register.rsp) :
    s2.register r = s.register r ∧
      s2.register Register.rsp = s.register Register.rsp := by
  have h := push_pop_wiederhergestellt s s1 s2 r r d1 d2 m v
    hok1 hb1 hwr hles hstep1 hrd hstep2 hok2 hb2 hdst
  exact ⟨h.2, h.1⟩

/-- FLAG PRESERVATION: flags survive call, save, selected restore and
    return. Every premise pins one guard of the four steps. -/
theorem OptRetPathSel_flags (s s1 s2 s3 s4 : Zustand) (disp : BitVec 32)
    (r dst : Register) (dc dp dq dr : Decodiert) (mc mp : Speicher)
    (vp vr : Wort)
    (hokc : laengeOk dc.laenge = true)
    (hbc : dc.befehl = .call32 disp)
    (hwrc : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip dc.laenge) = some mc)
    (hstepc : schritt dc s = some s1)
    (hwrp : write64 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
      (s1.register r) = some mp)
    (hstepp : schritt dp s1 = some s2)
    (hokp : laengeOk dp.laenge = true)
    (hbp : dp.befehl = .push64 r)
    (hrdp : read64 s2.speicher (s2.register Register.rsp) = some vp)
    (hstepq : schritt dq s2 = some s3)
    (hokq : laengeOk dq.laenge = true)
    (hbq : dq.befehl = .pop64 dst)
    (hdst : dst ≠ Register.rsp)
    (hrdr : read64 s3.speicher (s3.register Register.rsp) = some vr)
    (hstepr : schritt dr s3 = some s4)
    (hokr : laengeOk dr.laenge = true)
    (hbr : dr.befehl = .ret) :
    s4.flags = s.flags := by
  rw [schritt_call32_erfolg dc s disp mc hokc hbc hwrc] at hstepc
  rw [schritt_push64_erfolg dp s1 r mp hokp hbp hwrp] at hstepp
  rw [schritt_pop64_reg dq s2 dst vp hokq hbq hdst hrdp] at hstepq
  rw [schritt_ret_erfolg dr s3 vr hokr hbr hrdr] at hstepr
  have e1 : s1 = schrittCall s Register.rsp mc
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip dc.laenge + dispWort disp) :=
    (Option.some_inj.mp hstepc).symm
  have e2 : s2 = schrittPush s1 Register.rsp (ripNach s1.rip dp.laenge)
      (s1.register Register.rsp - BitVec.ofNat 64 8) mp :=
    (Option.some_inj.mp hstepp).symm
  have e3 : s3 = schrittPopReg s2 Register.rsp dst
      (ripNach s2.rip dq.laenge)
      (s2.register Register.rsp + BitVec.ofNat 64 8) vp :=
    (Option.some_inj.mp hstepq).symm
  have e4 : s4 = schrittRet s3 Register.rsp
      (s3.register Register.rsp + BitVec.ofNat 64 8) vr :=
    (Option.some_inj.mp hstepr).symm
  have f1 : s1.flags = s.flags := by simp [e1, schrittCall]
  have f2 : s2.flags = s1.flags := by simp [e2, schrittPush]
  have f3 : s3.flags = s2.flags := by simp [e3, schrittPopReg]
  have f4 : s4.flags = s3.flags := by simp [e4, schrittRet]
  rw [f4, f3, f2, f1]

/-! ## 4. Connection: the selected return path keeps the callee-saved contract.

    The optimisation (DESIGN section 3A + section 7 row): return paths
    are selected -- several returns share one epilogue -- with the entry
    save and every selected-path restore CHECKED per call/return by the
    validator (`hz`). The rule is generic over arbitrary registers and
    values: the taken restore register `dst` is arbitrary in the steps
    and pinned to `r` by the admission -- the proof uses `hz` for
    exactly that. Conclusion, jointly: the stack top is restored, the
    return address is correct, the callee-saved value survives from
    entry to return, and every permission map survives (fault
    behaviour: no new faulting form -- save/restore/return refuse only
    through their accepted guards, section 2 refuses loudly).
    Observation behaviour beyond registers/flags/permissions --
    contracts at their place, call-log order, shared-atomic
    concurrency, IEEE rounding, budget exhaustion timing -- stays with
    its owner lane (see CUTS), since no source bridge is invented here. -/

/-- CONNECTION: an admitted return-path selection keeps the
    callee-saved value, the stack top, the return address and every
    permission map. -/
theorem OptRetPathSel_verbindung (s s1 s2 s3 s4 : Zustand)
    (disp : BitVec 32) (r dst : Register)
    (dc dp dq dr : Decodiert)
    (mc mp : Speicher) (vp vr : Wort)
    (cert : RetPfadCert)
    (hokc : laengeOk dc.laenge = true)
    (hbc : dc.befehl = .call32 disp)
    (hwrc : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip dc.laenge) = some mc)
    (hlesc : lesbar8 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      = true)
    (hstepc : schritt dc s = some s1)
    (hwrp : write64 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
      (s1.register r) = some mp)
    (hlesp : lesbar8 s1.speicher
      (s1.register Register.rsp - BitVec.ofNat 64 8) = true)
    (hstepp : schritt dp s1 = some s2)
    (hokp : laengeOk dp.laenge = true)
    (hbp : dp.befehl = .push64 r)
    (hrdp : read64 s2.speicher (s2.register Register.rsp) = some vp)
    (hstepq : schritt dq s2 = some s3)
    (hokq : laengeOk dq.laenge = true)
    (hbq : dq.befehl = .pop64 dst)
    (hdst : dst ≠ Register.rsp)
    (hrdr : read64 s3.speicher (s3.register Register.rsp) = some vr)
    (hstepr : schritt dr s3 = some s4)
    (hokr : laengeOk dr.laenge = true)
    (hbr : dr.befehl = .ret)
    (hdis : Disjunkt (s.register Register.rsp - BitVec.ofNat 64 8)
      (s1.register Register.rsp - BitVec.ofNat 64 8))
    (hz : retPfadZulassen cert dq dr r = true) :
    s4.register Register.rsp = s.register Register.rsp ∧
      s4.rip = ripNach s.rip dc.laenge ∧
      s4.register r = s1.register r ∧
      s4.speicher.ausfuehrbar = s.speicher.ausfuehrbar ∧
      s4.speicher.lesbar = s.speicher.lesbar ∧
      s4.speicher.schreibbar = s.speicher.schreibbar := by
  have hpair := retPaar_aus_zulassung cert dq dr r hz
  have hdst_eq : dst = r := by
    simpa using hbq.symm.trans hpair.1
  rw [hdst_eq] at hbq hdst
  exact verschachtelt_wiederhergestellt s s1 s2 s3 s4 disp r r dc dp dq dr
    mc mp vp vr hokc hbc hwrc hlesc hstepc hwrp hlesp hstepp hokp hbp
    hrdp hstepq hokq hbq hdst hrdr hstepr hokr hbr hdis

/-! ## 5. Joint witness: every premise jointly on a memory-changing run.

    The machine half reuses the accepted call frame (`zeugS`, `zeugSc1`,
    `zeugMc`, `zeugNobenP`, `zeug_call_schreibt`, `zeugOben_lesbar`) and
    runs a SAME-register callee-saved chain through it: entry saves
    `rbx`, the selected return path restores `rbx`, then `ret`. The
    source half is the non-degenerate fixture program `eP`: `setze`
    writes table `konto`, and the reached run moves slot 0 from `0` to
    `5`. -/

/-- Witness memory after the inner save of `rbx` below the post-call top. -/
def zeugRmp : Speicher := { zeugMc with
  bytes := writeBytes zeugMc zeugNobenP (zeugSc1.register Register.rbx) }

/-- Witness state after the inner `push rbx` (length 1). -/
def zeugRS2 : Zustand := schrittPush zeugSc1 Register.rsp
  (ripNach zeugSc1.rip 1) zeugNobenP zeugRmp

/-- Witness state after the selected `pop rbx` (length 1). -/
def zeugRS3 : Zustand := schrittPopReg zeugRS2 Register.rsp Register.rbx
  (ripNach zeugRS2.rip 1)
  (zeugRS2.register Register.rsp + BitVec.ofNat 64 8)
  (zeugSc1.register Register.rbx)

/-- Witness state after the matching `ret` (length 1). -/
def zeugRS4 : Zustand := schrittRet zeugRS3 Register.rsp
  (zeugRS3.register Register.rsp + BitVec.ofNat 64 8)
  (ripNach zeugS.rip 5)

/-- JOINT WITNESS for `OptRetPathSel_verbindung`: every premise holds
    jointly -- the admitted `rbx` save/restore/return chain over actual
    `schritt` executions whose call observably changes memory (zero
    becomes the return address below the old top), the restored stack
    top and callee-saved value by the connection -- beside the
    non-degenerate source fixture (`setze` writes `konto`) with a
    reached run moving slot 0 from `0` to `5`. -/
theorem OptRetPathSel_verbindung_zeuge :
    ∃ (s s1 s2 s3 s4 : Zustand) (disp : BitVec 32) (r dst : Register)
      (dc dp dq dr : Decodiert) (mc mp : Speicher) (vp vr : Wort)
      (cert : RetPfadCert),
      (laengeOk dc.laenge = true) ∧ (dc.befehl = .call32 disp) ∧
      (write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip dc.laenge) = some mc) ∧
      (lesbar8 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        = true) ∧
      (schritt dc s = some s1) ∧
      (write64 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
        (s1.register r) = some mp) ∧
      (lesbar8 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
        = true) ∧
      (schritt dp s1 = some s2) ∧
      (laengeOk dp.laenge = true) ∧ (dp.befehl = .push64 r) ∧
      (read64 s2.speicher (s2.register Register.rsp) = some vp) ∧
      (schritt dq s2 = some s3) ∧
      (laengeOk dq.laenge = true) ∧ (dq.befehl = .pop64 dst) ∧
      (dst ≠ Register.rsp) ∧
      (read64 s3.speicher (s3.register Register.rsp) = some vr) ∧
      (schritt dr s3 = some s4) ∧
      (laengeOk dr.laenge = true) ∧ (dr.befehl = .ret) ∧
      (Disjunkt (s.register Register.rsp - BitVec.ofNat 64 8)
        (s1.register Register.rsp - BitVec.ofNat 64 8)) ∧
      (retPfadZulassen cert dq dr r = true) ∧
      (s.speicher.bytes (s.register Register.rsp - BitVec.ofNat 64 8) ≠
        mc.bytes (s.register Register.rsp - BitVec.ofNat 64 8)) ∧
      (s4.register Register.rsp = s.register Register.rsp) ∧
      (s4.register r = s1.register r) ∧
      (eD.signatur eSetze).schreibt () = true ∧
      (∃ (M : RufMaschineG eD) (rho : Env eD (eD.params ePruefe))
        (w0 : World eD),
        RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
        (eSp.slots () 0 ()).n = 0 ∧ (w0.slots () 0 ()).n = 5 ∧
        (eSp.slots () 0 ()).n ≠ (w0.slots () 0 ()).n ∧
        RufEreignisF.eintritt ePruefe rho w0 ∈ (M.faeden 0).log) := by
  have hokc : laengeOk
      (⟨Befehl.call32 (BitVec.ofNat 32 0), 5⟩ : Decodiert).laenge =
      true := by
    decide
  have hokp : laengeOk
      (⟨Befehl.push64 Register.rbx, 1⟩ : Decodiert).laenge = true := by
    decide
  have hokq : laengeOk
      (⟨Befehl.pop64 Register.rbx, 1⟩ : Decodiert).laenge = true := by
    decide
  have hokr : laengeOk (⟨Befehl.ret, 1⟩ : Decodiert).laenge = true := by
    decide
  have hdst : Register.rbx ≠ Register.rsp := by decide
  have hstepc : schritt
      (⟨Befehl.call32 (BitVec.ofNat 32 0), 5⟩ : Decodiert)
      zeugS = some zeugSc1 :=
    schritt_call32_erfolg _ _ _ _ hokc rfl zeug_call_schreibt
  have hpermp : schreibbar8 zeugMc zeugNobenP = true := by decide
  have hlesp : lesbar8 zeugMc zeugNobenP = true := by decide
  have hwrp : write64 zeugMc zeugNobenP (zeugSc1.register Register.rbx) =
      some zeugRmp := by
    unfold write64 zeugRmp
    rw [if_pos hpermp]
  have hstepp : schritt
      (⟨Befehl.push64 Register.rbx, 1⟩ : Decodiert)
      zeugSc1 = some zeugRS2 :=
    schritt_push64_erfolg _ _ _ _ hokp rfl hwrp
  have hrdp : read64 zeugRS2.speicher (zeugRS2.register Register.rsp) =
      some (zeugSc1.register Register.rbx) := by
    simp only [zeugRS2, schrittPush, regSet_gleich]
    exact read64_nach_write64 zeugMc zeugRmp _ _ hwrp hlesp
  have hstepq : schritt
      (⟨Befehl.pop64 Register.rbx, 1⟩ : Decodiert)
      zeugRS2 = some zeugRS3 :=
    schritt_pop64_reg _ _ _ _ hokq rfl hdst hrdp
  have hrdr : read64 zeugRS3.speicher (zeugRS3.register Register.rsp) =
      some (ripNach zeugS.rip 5) := by
    decide
  have hstepr : schritt (⟨Befehl.ret, 1⟩ : Decodiert)
      zeugRS3 = some zeugRS4 :=
    schritt_ret_erfolg _ _ _ hokr rfl hrdr
  have hdis : Disjunkt (zeugS.register Register.rsp - BitVec.ofNat 64 8)
      (zeugSc1.register Register.rsp - BitVec.ofNat 64 8) := by
    show Disjunkt (BitVec.ofNat 64 8184) (BitVec.ofNat 64 8176)
    exact disjunkt_von_intervallen _ _
      (by unfold OhneUmbruch; decide) (by unfold OhneUmbruch; decide)
      (Or.inr (by decide))
  have hmem : zeugSpeicherRW.bytes zeugOben ≠
      zeugMc.bytes zeugOben := by
    have hhit := writeBytesN_hit zeugSpeicherRW zeugOben
      (ripNach zeugS.rip 5) 8 0 (by decide) (by decide)
    rw [addrOff_null] at hhit
    show BitVec.ofNat 8 0 ≠
      writeBytes zeugSpeicherRW zeugOben (ripNach zeugS.rip 5) zeugOben
    unfold writeBytes
    rw [hhit]
    decide
  have hconn := OptRetPathSel_verbindung zeugS zeugSc1 zeugRS2 zeugRS3
    zeugRS4 (BitVec.ofNat 32 0) .rbx .rbx
    ⟨.call32 (BitVec.ofNat 32 0), 5⟩ ⟨.push64 .rbx, 1⟩
    ⟨.pop64 .rbx, 1⟩ ⟨.ret, 1⟩ zeugMc zeugRmp
    (zeugSc1.register Register.rbx) (ripNach zeugS.rip 5) retPfadCertW
    hokc rfl zeug_call_schreibt zeugOben_lesbar hstepc
    hwrp hlesp hstepp hokp rfl hrdp hstepq hokq rfl
    hdst hrdr hstepr hokr rfl hdis probe_retPfadZulassen_ok
  obtain ⟨M, hr, h0, rho, w0, hm, hreq, h5⟩ := ziel_ort_einfaden_zeuge
  have hchg : (eSp.slots () 0 ()).n ≠ (w0.slots () 0 ()).n := by
    rw [h0, h5]
    decide
  exact ⟨zeugS, zeugSc1, zeugRS2, zeugRS3, zeugRS4,
    BitVec.ofNat 32 0, .rbx, .rbx,
    ⟨.call32 (BitVec.ofNat 32 0), 5⟩, ⟨.push64 .rbx, 1⟩,
    ⟨.pop64 .rbx, 1⟩, ⟨.ret, 1⟩, zeugMc, zeugRmp,
    (zeugSc1.register Register.rbx), (ripNach zeugS.rip 5),
    retPfadCertW,
    hokc, rfl, zeug_call_schreibt, zeugOben_lesbar, hstepc,
    hwrp, hlesp, hstepp, hokp, rfl, hrdp, hstepq, hokq, rfl,
    hdst, hrdr, hstepr, hokr, rfl, hdis, probe_retPfadZulassen_ok,
    hmem, hconn.1, hconn.2.2.1, rfl,
    M, rho, w0, hr, h0, h5, hchg, hm⟩

/- CUTS:
    Proved here (all over the REUSED canonical `Typen`/`Speicher`/
    `Ausfuehrung`/`StackUnwind` vocabulary plus the `eD`/`eP` fixture --
    no new machine, no new decoder row, no new instruction, no source
    change):
    - per-path restore check `retPaarOk` and admission `retPfadZulassen`
      with the EXACT certificate shape (`RetPfadCert`: layer-A rewrite
      record `pfade`/`epilog`/`gesichert` plus layer-B/C recomputed
      citations `alleOk`/`epilogOk`/`fremdOk`/`farbeOk`), and the
      extraction `retPaar_aus_zulassung` the connection uses;
    - four loud refusals (missing restore, missing return,
      address-taken/overlap citation, colouring/liveness citation) and
      three probes (admitted, missing-restore, false citation);
    - value preservation `retPfad_wert_erhalten` (same-register
      save/restore over arbitrary values) and flag preservation
      `OptRetPathSel_flags` (flags survive call/save/restore/return);
    - connection `OptRetPathSel_verbindung` (admitted selection keeps
      the callee-saved value, the stack top, the return address and
      every permission map) with joint witness
      `OptRetPathSel_verbindung_zeuge` (same-register `rbx` chain over
      actual steps with a memory-changing call beside the
      table-writing source fixture and its `0 -> 5` reached run).
    NOT proved here, and not claimed:
    - No tail rewrite: the jump from each selected path to the shared
      epilogue (`pop/ret` tail replaced by a `jump32`) is recorded in
      the certificate but its step correspondence is not proved --
      only the taken path's restore pair is pinned and connected.
      Short-branch selection stays with `BranchLayout`/`Rel8Reach`.
    - No source correspondence: contracts at their place, call-log
      order (`FolgeG`, `AufrufOpt` ghost obligation), entry duties and
      budget exhaustion timing are source-side and stay with their
      lanes; this rule removes no call and no check.
    - No TSO/concurrency bridge: all facts are sequential over one
      `Speicher`; store buffers, forwarding and GX refinement stay with
      the TSO-bridge work.
    - No IEEE claim: the pilot `Befehl` vocabulary has no FP form, so
      the rule cannot alter FP state; scalar-FP correspondence
      (DESIGN section 4) stays with its lane.
    - No cost/work bound: step counts are unchanged in shape; the
      machine-work bound stays with the `CostSummary` schema and the
      lowering lane.
    - No silicon correspondence and no ABI entry claim: the
      callee-saved discipline is the stated checked obligation, proved
      of the canonical steps, not of hardware.
-/

#print axioms retPaarOk
#print axioms retPfadZulassen
#print axioms retPaar_aus_zulassung
#print axioms retPfadVerweigert_fehlend
#print axioms retPfadVerweigert_keinRet
#print axioms retPfadVerweigert_fremd
#print axioms retPfadVerweigert_farbe
#print axioms probe_retPfadZulassen_ok
#print axioms probe_retPfadZulassen_fehlend
#print axioms probe_retPfadZulassen_fremd
#print axioms retPfad_wert_erhalten
#print axioms OptRetPathSel_flags
#print axioms OptRetPathSel_verbindung
#print axioms OptRetPathSel_verbindung_zeuge

end Gabbro.Grammatik.X86
