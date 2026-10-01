/-
   File:      Grammatik/X86/StackUnwind.lean
   Subject:   Frame-chain well-formedness and guard facts over actual pilot
              push/pop/call/ret steps (no new executor).

   Lane 542 (N9 proof wave): thin consumer layer over the ACCEPTED
   `Typen` / `Speicher` / `Ausfuehrung` / `Stapel` / `Regionen` /
   `Byteschritt` vocabulary. No new transition, no second decoder, no
   source claim, no OS content. Generic nested-call/frame-chain
   preservation and return-stack restoration over actual
   memory-changing `schritt` executions; refusal of returns into
   non-executable or guard memory via actual fetch.
-/
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Stapel
import Grammatik.X86.Regionen
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- Frame-chain well-formedness: both frames are checked and the inner
    (callee) frame sits at or below the outer (caller) frame base.
    The stack grows down; adjacency (`=` allowed) shares no byte since
    slot extents stay strictly below their own tops. -/
def KetteOk (aussen innen : Rahmen) : Bool :=
  rahmenOk aussen && rahmenOk innen && decide (innen.spitzeNat ≤ aussen.basis)

/-- The stack pointer sits inside a frame extent (inclusive top, so a
    frame-top `rsp` after full unwind still counts as inside). -/
def rspImRahmen (s : Zustand) (r : Rahmen) : Bool :=
  decide (r.basis ≤ (s.register Register.rsp).toNat ∧
    (s.register Register.rsp).toNat ≤ r.spitzeNat)

/-- Stack-pointer round-trip: moving down one word and back up restores
    the pointer. Arithmetic only; frame/guard validity is separate. -/
theorem rsp8_runter_rauf (R : Wort) :
    (R - BitVec.ofNat 64 8) + BitVec.ofNat 64 8 = R :=
  BitVec.sub_add_cancel R (BitVec.ofNat 64 8)

/-! ## 1. Single-level restoration over actual steps. -/

/-- PUSH-POP RESTORATION: over actual `schritt` executions, a push
    followed by a pop into a different register restores the stack
    pointer and delivers the pushed value. Every premise pins one
    guard of the two steps or of the read-back. -/
theorem push_pop_wiederhergestellt (s s1 s2 : Zustand) (src dst : Register)
    (d1 d2 : Decodiert) (m : Speicher) (v : Wort)
    (hok1 : laengeOk d1.laenge = true)
    (hb1 : d1.befehl = .push64 src)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = some m)
    (hles : lesbar8 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      = true)
    (hstep1 : schritt d1 s = some s1)
    (hrd : read64 s1.speicher (s1.register Register.rsp) = some v)
    (hstep2 : schritt d2 s1 = some s2)
    (hok2 : laengeOk d2.laenge = true)
    (hb2 : d2.befehl = .pop64 dst)
    (hdst : dst ≠ Register.rsp) :
    s2.register Register.rsp = s.register Register.rsp ∧
      s2.register dst = s.register src := by
  rw [schritt_push64_erfolg d1 s src m hok1 hb1 hwr] at hstep1
  rw [schritt_pop64_reg d2 s1 dst v hok2 hb2 hdst hrd] at hstep2
  have hback : read64 m (s.register Register.rsp - BitVec.ofNat 64 8) =
      some (s.register src) :=
    read64_nach_write64 s.speicher m _ _ hwr hles
  cases hstep1
  cases hstep2
  unfold schrittPopReg schrittPush at *
  dsimp only at hrd ⊢
  rw [regSet_gleich] at hrd
  have hv : v = s.register src :=
    Option.some_inj.mp (hrd.symm.trans hback)
  constructor
  · rw [regSet_fremd _ _ _ _ (Ne.symm hdst), regSet_gleich]
    exact rsp8_runter_rauf _
  · rw [regSet_gleich]
    exact hv

/-- CALL-RET RESTORATION: over actual `schritt` executions, a call
    followed by a return restores the stack pointer and lands on the
    stored post-decode address. Every premise pins one guard of the
    two steps or of the read-back. -/
theorem call_ret_wiederhergestellt (s s1 s2 : Zustand) (disp : BitVec 32)
    (d1 d2 : Decodiert) (m : Speicher) (ziel : Wort)
    (hok1 : laengeOk d1.laenge = true)
    (hb1 : d1.befehl = .call32 disp)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip d1.laenge) = some m)
    (hles : lesbar8 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      = true)
    (hstep1 : schritt d1 s = some s1)
    (hrd : read64 s1.speicher (s1.register Register.rsp) = some ziel)
    (hstep2 : schritt d2 s1 = some s2)
    (hok2 : laengeOk d2.laenge = true)
    (hb2 : d2.befehl = .ret) :
    s2.register Register.rsp = s.register Register.rsp ∧
      s2.rip = ripNach s.rip d1.laenge := by
  rw [schritt_call32_erfolg d1 s disp m hok1 hb1 hwr] at hstep1
  rw [schritt_ret_erfolg d2 s1 ziel hok2 hb2 hrd] at hstep2
  have hback : read64 m (s.register Register.rsp - BitVec.ofNat 64 8) =
      some (ripNach s.rip d1.laenge) :=
    read64_nach_write64 s.speicher m _ _ hwr hles
  cases hstep1
  cases hstep2
  unfold schrittRet schrittCall at *
  dsimp only at hrd ⊢
  rw [regSet_gleich] at hrd
  have hz : ziel = ripNach s.rip d1.laenge :=
    Option.some_inj.mp (hrd.symm.trans hback)
  constructor
  · show ((s.register Register.rsp - BitVec.ofNat 64 8) +
      BitVec.ofNat 64 8) = _
    exact rsp8_runter_rauf _
  · show ziel = _
    exact hz

/-! ## 2. Nested call/frame-chain preservation. -/

/-- NESTED RESTORATION: over actual `schritt` executions, a call with
    an inner push/pop pair followed by a return restores the stack
    pointer and the return address, delivers the inner value, and
    preserves every permission map (frame/guard validity survives the
    two word stores, which change bytes only). The disjointness premise
    keeps the inner store off the saved return address; every other
    premise pins one guard of the four steps or of a read-back. -/
theorem verschachtelt_wiederhergestellt
    (s s1 s2 s3 s4 : Zustand)
    (disp : BitVec 32) (src dst : Register)
    (dc dp dq dr : Decodiert)
    (mc mp : Speicher) (vp vr : Wort)
    (hokc : laengeOk dc.laenge = true)
    (hbc : dc.befehl = .call32 disp)
    (hwrc : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip dc.laenge) = some mc)
    (hlesc : lesbar8 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      = true)
    (hstepc : schritt dc s = some s1)
    (hwrp : write64 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
      (s1.register src) = some mp)
    (hlesp : lesbar8 s1.speicher
      (s1.register Register.rsp - BitVec.ofNat 64 8) = true)
    (hstepp : schritt dp s1 = some s2)
    (hokp : laengeOk dp.laenge = true)
    (hbp : dp.befehl = .push64 src)
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
      (s1.register Register.rsp - BitVec.ofNat 64 8)) :
    s4.register Register.rsp = s.register Register.rsp ∧
      s4.rip = ripNach s.rip dc.laenge ∧
      s4.register dst = s1.register src ∧
      s4.speicher.ausfuehrbar = s.speicher.ausfuehrbar ∧
      s4.speicher.lesbar = s.speicher.lesbar ∧
      s4.speicher.schreibbar = s.speicher.schreibbar := by
  rw [schritt_call32_erfolg dc s disp mc hokc hbc hwrc] at hstepc
  rw [schritt_push64_erfolg dp s1 src mp hokp hbp hwrp] at hstepp
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
  have hrsp_ne : Register.rsp ≠ dst := Ne.symm hdst
  have e1rsp : s1.register Register.rsp =
      s.register Register.rsp - BitVec.ofNat 64 8 := by
    rw [e1]
    show regSet s.register Register.rsp
      (s.register Register.rsp - BitVec.ofNat 64 8)
      Register.rsp = _
    exact regSet_gleich _ _ _
  have e2rsp : s2.register Register.rsp =
      s1.register Register.rsp - BitVec.ofNat 64 8 := by
    rw [e2]
    show regSet s1.register Register.rsp
      (s1.register Register.rsp - BitVec.ofNat 64 8)
      Register.rsp = _
    exact regSet_gleich _ _ _
  have e3rsp : s3.register Register.rsp =
      s2.register Register.rsp + BitVec.ofNat 64 8 := by
    rw [e3]
    show regSet (regSet s2.register Register.rsp
      (s2.register Register.rsp + BitVec.ofNat 64 8)) dst vp
      Register.rsp = _
    rw [regSet_fremd _ _ _ _ hrsp_ne, regSet_gleich]
  have e4rsp : s4.register Register.rsp =
      s3.register Register.rsp + BitVec.ofNat 64 8 := by
    rw [e4]
    show regSet s3.register Register.rsp
      (s3.register Register.rsp + BitVec.ofNat 64 8)
      Register.rsp = _
    exact regSet_gleich _ _ _
  have e1mem : s1.speicher = mc := congrArg Zustand.speicher e1
  have e2mem : s2.speicher = mp := congrArg Zustand.speicher e2
  have e3mem : s3.speicher = s2.speicher := by simp only [e3, schrittPopReg]
  have e4mem : s4.speicher = s3.speicher := by simp only [e4, schrittRet]
  have e3dst : s3.register dst = vp := by
    rw [e3]
    show regSet (regSet s2.register Register.rsp
      (s2.register Register.rsp + BitVec.ofNat 64 8)) dst vp dst = _
    exact regSet_gleich _ _ _
  have e4dst : s4.register dst = s3.register dst := by
    rw [e4]
    show regSet s3.register Register.rsp
      (s3.register Register.rsp + BitVec.ofNat 64 8) dst = _
    exact regSet_fremd _ _ _ _ hdst
  have e4rip : s4.rip = vr := congrArg Zustand.rip e4
  have hbackc : read64 mc (s.register Register.rsp - BitVec.ofNat 64 8) =
      some (ripNach s.rip dc.laenge) :=
    read64_nach_write64 s.speicher mc _ _ hwrc hlesc
  have hbackp := read64_nach_write64 _ _ _ _ hwrp hlesp
  rw [e2mem, e2rsp] at hrdp
  have hv : vp = s1.register src :=
    Option.some_inj.mp (hrdp.symm.trans hbackp)
  have hdis' : Disjunkt (s1.register Register.rsp - BitVec.ofNat 64 8)
      (s.register Register.rsp - BitVec.ofNat 64 8) :=
    fun i j hi hj h => hdis j i hj hi h.symm
  have hcarry : read64 mp (s.register Register.rsp - BitVec.ofNat 64 8) =
      read64 s1.speicher (s.register Register.rsp - BitVec.ofNat 64 8) :=
    read64_rahmen _ _ _ _ _ hwrp hdis'
  rw [e1mem] at hcarry
  rw [e3mem, e2mem, e3rsp, e2rsp, e1rsp, rsp8_runter_rauf] at hrdr
  have hz : vr = ripNach s.rip dc.laenge :=
    Option.some_inj.mp (hrdr.symm.trans (hcarry.trans hbackc))
  have pc := write64_erhaelt_berechtigungen s.speicher _ _ mc hwrc
  have pp := write64_erhaelt_berechtigungen _ _ _ mp hwrp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e4rsp, e3rsp, e2rsp, e1rsp]
    repeat rw [rsp8_runter_rauf]
  · rw [e4rip]
    exact hz
  · rw [e4dst, e3dst]
    exact hv
  · rw [e4mem, e3mem, e2mem, pp.2.2, e1mem, pc.2.2]
  · rw [e4mem, e3mem, e2mem, pp.1, e1mem, pc.1]
  · rw [e4mem, e3mem, e2mem, pp.2.1, e1mem, pc.2.1]

/-! ## 3. Refusal: returns into non-executable memory. -/

/-- FETCH REFUSAL WITHOUT EXECUTE: a state whose rip has no execute
    permission fetches nothing, so the byte step loudly refuses. Fetch
    consults execute permission only; data readability is irrelevant. -/
theorem nicht_ausfuehrbar_verweigert (s : Zustand)
    (h : s.speicher.ausfuehrbar s.rip = false) :
    byteschritt s = .verweigert := by
  have hg : geholt s = [] := by
    have hlen : (geholt s).length = 0 := by
      by_cases hc : (geholt s).length = 0
      · exact hc
      · have hpos : 0 < (geholt s).length := Nat.pos_of_ne_zero hc
        have hx := geholt_nur_ausfuehrbar s 0 hpos
        rw [addrOff_null] at hx
        rw [hx] at h
        exact Bool.noConfusion h
    exact List.length_eq_zero_iff.mp hlen
  have hf : fetchDekodiert s = none := by
    simp only [fetchDekodiert, hg, decode_nichts_leer]
  exact byteschritt_verweigert_ohne_fetch s hf

/-- RETURN INTO NON-EXECUTABLE REFUSED: a successful `ret` whose popped
    target has no execute permission admits no byte step: the machine
    loudly refuses instead of fetching bytes as code there. Guard
    regions carry `ausfuehrbar = false`, so returns into a guard refuse
    here too. Every premise pins one guard of the return step or of the
    refusal. -/
theorem ret_ins_nicht_ausfuehrbar_verweigert (s s' : Zustand) (ziel : Wort)
    (d : Decodiert)
    (hok : laengeOk d.laenge = true)
    (hb : d.befehl = .ret)
    (hrd : read64 s.speicher (s.register Register.rsp) = some ziel)
    (hstep : schritt d s = some s')
    (hexe : s.speicher.ausfuehrbar ziel = false) :
    byteschritt s' = .verweigert := by
  rw [schritt_ret_erfolg d s ziel hok hb hrd] at hstep
  have e : s' = schrittRet s Register.rsp
      (s.register Register.rsp + BitVec.ofNat 64 8) ziel :=
    (Option.some_inj.mp hstep).symm
  have erip : s'.rip = ziel := by simp only [e, schrittRet]
  have emem : s'.speicher = s.speicher := by simp only [e, schrittRet]
  have hrip : s'.speicher.ausfuehrbar s'.rip = false := by
    rw [emem, erip]
    exact hexe
  exact nicht_ausfuehrbar_verweigert s' hrip

/-! ## 4. Guard pages: no-access regions refuse stack stores. -/

/-- A guard region: declared extent with no access rights. Stack guards
    refuse the push/call word store below the top; return guards carry
    `ausfuehrbar = false` and refuse fetch via §3. -/
def Wache (w : Region) : Bool :=
  decide (0 < w.len ∧ w.lesbar = false ∧ w.schreibbar = false ∧
    w.ausfuehrbar = false)

/-- A write-denied initialised region answers no full write permission
    at its base: the guard footprint is closed to word stores. Uses the
    denial, the nonempty extent and the no-wrap bound. -/
theorem wache_schreibschutz (m : Speicher) (r : Region)
    (hw : r.schreibbar = false)
    (hlen : 0 < r.len)
    (hwrap : r.basis + 8 ≤ 2 ^ 64) :
    schreibbar8 (initialisiere m r) (natAdresse r.basis) = false := by
  have hbyte : (initialisiere m r).schreibbar
      (addrOff (natAdresse r.basis) 0) = false := by
    rw [addrOff_null]
    have hto : (natAdresse r.basis).toNat = r.basis := by
      unfold natAdresse
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hin : inRegion r (natAdresse r.basis).toNat = true := by
      unfold inRegion
      simp only [decide_eq_true_eq]
      rw [hto]
      omega
    have hx := initialisiere_ausmass_rechte m r (natAdresse r.basis) hin
    rw [hx.2.1, hw]
  unfold schreibbar8
  simp only [hbyte, Bool.false_and]

/-- PUSH ONTO A GUARD REFUSED: if the eight bytes below the top are not
    writable, the push step loudly refuses. Every premise pins one guard
    of the step. -/
theorem wache_push_verweigert (s : Zustand) (src : Register)
    (d : Decodiert)
    (hok : laengeOk d.laenge = true)
    (hb : d.befehl = .push64 src)
    (hguard : schreibbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = false) :
    schritt d s = none :=
  schritt_push64_verweigert d s src hok hb
    (write64_verweigert s.speicher _ _ hguard)

/-- CALL ONTO A GUARD REFUSED: if the eight bytes below the top are not
    writable, the call step loudly refuses instead of spilling the
    return address into the guard. Every premise pins one guard. -/
theorem wache_call_verweigert (s : Zustand) (disp : BitVec 32)
    (d : Decodiert)
    (hok : laengeOk d.laenge = true)
    (hb : d.befehl = .call32 disp)
    (hguard : schreibbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = false) :
    schritt d s = none :=
  schritt_call32_verweigert d s disp hok hb
    (write64_verweigert s.speicher _ _ hguard)

/-! ## 5. Alignment is not validity; layout slots stay in frame. -/

/-- Shared witness flags: nothing set. -/
def zeugFlags : Flags :=
  { cf := false, pf := true, af := some false, zf := false, sf := false,
    of := false }

/-- Shared witness memory: zeroed bytes, fully readable and writable,
    never executable. -/
def zeugSpeicherRW : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun _ => false }

/-- Shared witness registers: stack top at 8192, `rax` holding 42. -/
def zeugReg42 : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 8192
  else if q = Register.rax then BitVec.ofNat 64 42
  else BitVec.ofNat 64 0

/-- Shared witness start state: code at 4096, stack top at 8192. -/
def zeugS : Zustand :=
  { register := zeugReg42, flags := zeugFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugSpeicherRW }

/-- ALIGNMENT IS NOT VALIDITY: a 16-aligned stack pointer far outside
    the frame is aligned and still not in the frame. Arithmetic
    alignment never substitutes for frame/guard validity. -/
theorem ausrichtung_ohne_rahmen :
    ausgerichtet16 (zeugS.register Register.rsp) = true ∧
      rspImRahmen zeugS { basis := 0, tiefe := 16 } = false := by
  decide

/-- CHAIN WITNESS SHAPE: adjacent checked frames with the stack top at
    their boundary satisfy the chain predicate, and the top counts as
    inside the outer frame. -/
theorem kette_ok_sonde :
    KetteOk { basis := 8192, tiefe := 32 }
      { basis := 8160, tiefe := 32 } = true ∧
      rspImRahmen zeugS { basis := 8192, tiefe := 32 } = true := by
  decide

/-- CALLEE-SAVE SLOTS STAY IN FRAME: under a fitting layout, every
    callee-save word index names a frame slot. Uses the layout fit and
    the position; the conclusion is a slot bound, not a restatement. -/
theorem belegung_gerettet_schranke (b : Belegung) (r : Rahmen) (i : Nat)
    (hi : i < b.gerettet)
    (hpasst : Belegung.passt b r = true) :
    b.gerettetIdx i < r.schlitzZahl := by
  unfold Belegung.passt Belegung.braucht Belegung.gerettetIdx
    Rahmen.schlitzZahl at *
  simp only [decide_eq_true_eq] at hpasst
  omega

/-! ## 6. Joint witnesses: memory-changing runs and loud refusals. -/

/-- Witness stack slot address: one word below the top. -/
def zeugOben : Adresse := zeugS.register Register.rsp - BitVec.ofNat 64 8

/-- Witness memory after pushing 42 below the top. -/
def zeugM1 : Speicher := { zeugSpeicherRW with
  bytes := writeBytes zeugSpeicherRW zeugOben 42 }

/-- Witness state after `push rax` (length 1). -/
def zeugS1 : Zustand := schrittPush zeugS Register.rsp
  (ripNach zeugS.rip 1) zeugOben zeugM1

/-- Witness state after `pop rbx` (length 1) past the push. -/
def zeugS2 : Zustand := schrittPopReg zeugS1 Register.rsp Register.rbx
  (ripNach zeugS1.rip 1)
  (zeugS1.register Register.rsp + BitVec.ofNat 64 8) 42

/-- The witness slot is writable for eight bytes. -/
theorem zeugOben_schreibbar :
    schreibbar8 zeugSpeicherRW zeugOben = true := by
  decide

/-- The witness slot is readable for eight bytes. -/
theorem zeugOben_lesbar :
    lesbar8 zeugSpeicherRW zeugOben = true := by
  decide

/-- The witness push installs its word below the old top. -/
theorem zeug_push_schreibt : write64 zeugSpeicherRW zeugOben 42 =
    some zeugM1 := by
  unfold write64 zeugM1
  rw [if_pos zeugOben_schreibbar]

/-- The pushed word reads back at the witness slot. -/
theorem zeug_push_liest : read64 zeugS1.speicher
    (zeugS1.register Register.rsp) = some 42 := by
  decide

/-- JOINT WITNESS (push/pop): every premise of single-level restoration
    holds jointly on a non-degenerate run, and the push observably
    changes memory (zero becomes 42 below the old top). -/
theorem push_pop_wiederhergestellt_zeuge :
    ∃ (s s1 s2 : Zustand) (src dst : Register) (d1 d2 : Decodiert)
      (m : Speicher) (v : Wort),
      (laengeOk d1.laenge = true) ∧ (d1.befehl = .push64 src) ∧
      (write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (s.register src) = some m) ∧
      (lesbar8 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        = true) ∧
      (schritt d1 s = some s1) ∧
      (read64 s1.speicher (s1.register Register.rsp) = some v) ∧
      (schritt d2 s1 = some s2) ∧
      (laengeOk d2.laenge = true) ∧ (d2.befehl = .pop64 dst) ∧
      (dst ≠ Register.rsp) ∧
      (s.speicher.bytes (s.register Register.rsp - BitVec.ofNat 64 8) ≠
        m.bytes (s.register Register.rsp - BitVec.ofNat 64 8)) := by
  have hok1 : laengeOk (⟨Befehl.push64 Register.rax, 1⟩ : Decodiert).laenge =
      true := by
    decide
  have hok2 : laengeOk (⟨Befehl.pop64 Register.rbx, 1⟩ : Decodiert).laenge =
      true := by
    decide
  have hdst : Register.rbx ≠ Register.rsp := by decide
  have hstep1 : schritt (⟨Befehl.push64 Register.rax, 1⟩ : Decodiert)
      zeugS = some zeugS1 :=
    schritt_push64_erfolg _ _ _ _ hok1 rfl zeug_push_schreibt
  have hstep2 : schritt (⟨Befehl.pop64 Register.rbx, 1⟩ : Decodiert)
      zeugS1 = some zeugS2 :=
    schritt_pop64_reg _ _ _ _ hok2 rfl hdst zeug_push_liest
  have hmem : zeugSpeicherRW.bytes zeugOben ≠
      zeugM1.bytes zeugOben := by
    have hhit := writeBytesN_hit zeugSpeicherRW zeugOben 42 8 0
      (by decide) (by decide)
    rw [addrOff_null] at hhit
    show BitVec.ofNat 8 0 ≠
      writeBytes zeugSpeicherRW zeugOben 42 zeugOben
    unfold writeBytes
    rw [hhit]
    decide
  exact ⟨zeugS, zeugS1, zeugS2, .rax, .rbx,
    ⟨.push64 .rax, 1⟩, ⟨.pop64 .rbx, 1⟩, zeugM1, 42,
    hok1, rfl, zeug_push_schreibt, zeugOben_lesbar, hstep1,
    zeug_push_liest, hstep2, hok2, rfl, hdst, hmem⟩

/-- Witness memory after a call storing the return address 4101. -/
def zeugMc : Speicher := { zeugSpeicherRW with
  bytes := writeBytes zeugSpeicherRW zeugOben (ripNach zeugS.rip 5) }

/-- Witness state after `call +0` (length 5). -/
def zeugSc1 : Zustand := schrittCall zeugS Register.rsp zeugMc zeugOben
  (ripNach zeugS.rip 5 + dispWort (BitVec.ofNat 32 0))

/-- Witness state after the matching `ret` (length 1). -/
def zeugSc2 : Zustand := schrittRet zeugSc1 Register.rsp
  (zeugSc1.register Register.rsp + BitVec.ofNat 64 8)
  (ripNach zeugS.rip 5)

/-- The witness call installs the post-decode address below the top. -/
theorem zeug_call_schreibt :
    write64 zeugSpeicherRW zeugOben (ripNach zeugS.rip 5) =
      some zeugMc := by
  unfold write64 zeugMc
  rw [if_pos zeugOben_schreibbar]

/-- The stored return address reads back at the witness slot. -/
theorem zeug_call_liest : read64 zeugSc1.speicher
    (zeugSc1.register Register.rsp) = some (ripNach zeugS.rip 5) := by
  decide

/-- JOINT WITNESS (call/ret): every premise of call/return restoration
    holds jointly on a non-degenerate run, and the call observably
    changes memory (zero becomes the return address below the top). -/
theorem call_ret_wiederhergestellt_zeuge :
    ∃ (s s1 s2 : Zustand) (disp : BitVec 32) (d1 d2 : Decodiert)
      (m : Speicher) (ziel : Wort),
      (laengeOk d1.laenge = true) ∧ (d1.befehl = .call32 disp) ∧
      (write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip d1.laenge) = some m) ∧
      (lesbar8 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        = true) ∧
      (schritt d1 s = some s1) ∧
      (read64 s1.speicher (s1.register Register.rsp) = some ziel) ∧
      (schritt d2 s1 = some s2) ∧
      (laengeOk d2.laenge = true) ∧ (d2.befehl = .ret) ∧
      (s.speicher.bytes (s.register Register.rsp - BitVec.ofNat 64 8) ≠
        m.bytes (s.register Register.rsp - BitVec.ofNat 64 8)) := by
  have hok1 : laengeOk
      (⟨Befehl.call32 (BitVec.ofNat 32 0), 5⟩ : Decodiert).laenge =
      true := by
    decide
  have hok2 : laengeOk (⟨Befehl.ret, 1⟩ : Decodiert).laenge = true := by
    decide
  have hstep1 : schritt
      (⟨Befehl.call32 (BitVec.ofNat 32 0), 5⟩ : Decodiert)
      zeugS = some zeugSc1 :=
    schritt_call32_erfolg _ _ _ _ hok1 rfl zeug_call_schreibt
  have hstep2 : schritt (⟨Befehl.ret, 1⟩ : Decodiert)
      zeugSc1 = some zeugSc2 :=
    schritt_ret_erfolg _ _ _ hok2 rfl zeug_call_liest
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
  exact ⟨zeugS, zeugSc1, zeugSc2, BitVec.ofNat 32 0,
    ⟨.call32 (BitVec.ofNat 32 0), 5⟩, ⟨.ret, 1⟩, zeugMc,
    ripNach zeugS.rip 5,
    hok1, rfl, zeug_call_schreibt, zeugOben_lesbar, hstep1,
    zeug_call_liest, hstep2, hok2, rfl, hmem⟩

/-! ## 7. Nested witness, refusal witnesses, layout witness. -/

/-- Nested inner slot: one word below the post-call top. -/
def zeugNobenP : Adresse :=
  zeugSc1.register Register.rsp - BitVec.ofNat 64 8

/-- Nested memory after the inner push of the caller's `rax` word. -/
def zeugNmp : Speicher := { zeugMc with
  bytes := writeBytes zeugMc zeugNobenP (zeugSc1.register Register.rax) }

/-- Nested state after the inner `push rax` (length 1). -/
def zeugNS2 : Zustand := schrittPush zeugSc1 Register.rsp
  (ripNach zeugSc1.rip 1) zeugNobenP zeugNmp

/-- Nested state after the inner `pop rbx` (length 1). -/
def zeugNS3 : Zustand := schrittPopReg zeugNS2 Register.rsp Register.rbx
  (ripNach zeugNS2.rip 1)
  (zeugNS2.register Register.rsp + BitVec.ofNat 64 8)
  (zeugSc1.register Register.rax)

/-- Nested state after the outer `ret` (length 1). -/
def zeugNS4 : Zustand := schrittRet zeugNS3 Register.rsp
  (zeugNS3.register Register.rsp + BitVec.ofNat 64 8)
  (ripNach zeugS.rip 5)

/-- JOINT WITNESS (nested): every premise of nested restoration holds
    jointly on a non-degenerate run: the outer call and the inner push
    both store into disjoint slots, both reads come back, and the outer
    store observably changes memory. -/
theorem verschachtelt_wiederhergestellt_zeuge :
    ∃ (s s1 s2 s3 s4 : Zustand) (disp : BitVec 32) (src dst : Register)
      (dc dp dq dr : Decodiert) (mc mp : Speicher) (vp vr : Wort),
      (laengeOk dc.laenge = true) ∧ (dc.befehl = .call32 disp) ∧
      (write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip dc.laenge) = some mc) ∧
      (lesbar8 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        = true) ∧
      (schritt dc s = some s1) ∧
      (write64 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
        (s1.register src) = some mp) ∧
      (lesbar8 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
        = true) ∧
      (schritt dp s1 = some s2) ∧
      (laengeOk dp.laenge = true) ∧ (dp.befehl = .push64 src) ∧
      (read64 s2.speicher (s2.register Register.rsp) = some vp) ∧
      (schritt dq s2 = some s3) ∧
      (laengeOk dq.laenge = true) ∧ (dq.befehl = .pop64 dst) ∧
      (dst ≠ Register.rsp) ∧
      (read64 s3.speicher (s3.register Register.rsp) = some vr) ∧
      (schritt dr s3 = some s4) ∧
      (laengeOk dr.laenge = true) ∧ (dr.befehl = .ret) ∧
      (Disjunkt (s.register Register.rsp - BitVec.ofNat 64 8)
        (s1.register Register.rsp - BitVec.ofNat 64 8)) ∧
      (s.speicher.bytes (s.register Register.rsp - BitVec.ofNat 64 8) ≠
        mc.bytes (s.register Register.rsp - BitVec.ofNat 64 8)) := by
  have hokc : laengeOk
      (⟨Befehl.call32 (BitVec.ofNat 32 0), 5⟩ : Decodiert).laenge =
      true := by
    decide
  have hokp : laengeOk
      (⟨Befehl.push64 Register.rax, 1⟩ : Decodiert).laenge = true := by
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
  have hwrp : write64 zeugMc zeugNobenP (zeugSc1.register Register.rax) =
      some zeugNmp := by
    unfold write64 zeugNmp
    rw [if_pos hpermp]
  have hstepp : schritt
      (⟨Befehl.push64 Register.rax, 1⟩ : Decodiert)
      zeugSc1 = some zeugNS2 :=
    schritt_push64_erfolg _ _ _ _ hokp rfl hwrp
  have hrdp : read64 zeugNS2.speicher (zeugNS2.register Register.rsp) =
      some (zeugSc1.register Register.rax) := by
    simp only [zeugNS2, schrittPush, regSet_gleich]
    exact read64_nach_write64 zeugMc zeugNmp _ _ hwrp hlesp
  have hstepq : schritt
      (⟨Befehl.pop64 Register.rbx, 1⟩ : Decodiert)
      zeugNS2 = some zeugNS3 :=
    schritt_pop64_reg _ _ _ _ hokq rfl hdst hrdp
  have hrdr : read64 zeugNS3.speicher (zeugNS3.register Register.rsp) =
      some (ripNach zeugS.rip 5) := by
    decide
  have hstepr : schritt (⟨Befehl.ret, 1⟩ : Decodiert)
      zeugNS3 = some zeugNS4 :=
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
  exact ⟨zeugS, zeugSc1, zeugNS2, zeugNS3, zeugNS4,
    BitVec.ofNat 32 0, .rax, .rbx,
    ⟨.call32 (BitVec.ofNat 32 0), 5⟩, ⟨.push64 .rax, 1⟩,
    ⟨.pop64 .rbx, 1⟩, ⟨.ret, 1⟩, zeugMc, zeugNmp,
    (zeugSc1.register Register.rax), (ripNach zeugS.rip 5),
    hokc, rfl, zeug_call_schreibt, zeugOben_lesbar, hstepc,
    hwrp, hlesp, hstepp, hokp, rfl, hrdp, hstepq, hokq, rfl,
    hdst, hrdr, hstepr, hokr, rfl, hdis, hmem⟩

/-- Return-refusal witness memory: a `ret` byte at 4096 (executable),
    the stack word 12288 at 8192, and no execute permission at 12288. -/
def zeugRetSpeicher : Speicher :=
  { bytes := fun a =>
      if a.toNat = 4096 then BitVec.ofNat 8 195
      else if a.toNat = 8192 then BitVec.ofNat 8 0
      else if a.toNat = 8193 then BitVec.ofNat 8 48
      else BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun a => decide (a.toNat = 4096) }

/-- Return-refusal witness start: `ret` at 4096, stack top at 8192. -/
def zeugRet : Zustand :=
  { register := fun q =>
      if q = Register.rsp then BitVec.ofNat 64 8192 else BitVec.ofNat 64 0
    flags := zeugFlags
    rip := BitVec.ofNat 64 4096
    speicher := zeugRetSpeicher }

/-- Return-refusal witness successor: control at 12288, top at 8200. -/
def zeugRetS : Zustand := schrittRet zeugRet Register.rsp
  (zeugRet.register Register.rsp + BitVec.ofNat 64 8)
  (BitVec.ofNat 64 12288)

/-- NEGATIVE WITNESS (non-executable return): a `ret` popping 12288
    succeeds as a step, but the target is not executable, so the byte
    step loudly refuses. -/
theorem ret_ins_nicht_ausfuehrbar_verweigert_zeuge :
    ∃ (s s' : Zustand) (ziel : Wort) (d : Decodiert),
      (laengeOk d.laenge = true) ∧ (d.befehl = .ret) ∧
      (read64 s.speicher (s.register Register.rsp) = some ziel) ∧
      (schritt d s = some s') ∧
      (s.speicher.ausfuehrbar ziel = false) ∧
      (byteschritt s' = .verweigert) := by
  have hok : laengeOk (⟨Befehl.ret, 1⟩ : Decodiert).laenge = true := by
    decide
  have hrd : read64 zeugRet.speicher (zeugRet.register Register.rsp) =
      some (BitVec.ofNat 64 12288) := by
    decide
  have hstep : schritt (⟨Befehl.ret, 1⟩ : Decodiert)
      zeugRet = some zeugRetS :=
    schritt_ret_erfolg _ _ _ hok rfl hrd
  have hexe : zeugRet.speicher.ausfuehrbar (BitVec.ofNat 64 12288) =
      false := by
    decide
  exact ⟨zeugRet, zeugRetS, BitVec.ofNat 64 12288, ⟨.ret, 1⟩,
    hok, rfl, hrd, hstep, hexe,
    ret_ins_nicht_ausfuehrbar_verweigert _ _ _ _ hok rfl hrd hstep
      hexe⟩

/-- Guard-refusal witness memory: everything below 8192 is a
    no-write guard; the stack top sits right above it. -/
def zeugWacheSpeicher : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun a => decide (8192 ≤ a.toNat)
    ausfuehrbar := fun _ => false }

/-- Guard-refusal witness start: top at 8192, `rax` holding 7. -/
def zeugWache : Zustand :=
  { register := fun q =>
      if q = Register.rsp then BitVec.ofNat 64 8192
      else if q = Register.rax then BitVec.ofNat 64 7
      else BitVec.ofNat 64 0
    flags := zeugFlags
    rip := BitVec.ofNat 64 4096
    speicher := zeugWacheSpeicher }

/-- NEGATIVE WITNESS (guard store): pushing below a write-protected
    guard loudly refuses the step. -/
theorem wache_push_verweigert_zeuge :
    ∃ (s : Zustand) (src : Register) (d : Decodiert),
      (laengeOk d.laenge = true) ∧ (d.befehl = .push64 src) ∧
      (schreibbar8 s.speicher
        (s.register Register.rsp - BitVec.ofNat 64 8) = false) ∧
      (schritt d s = none) := by
  have hok : laengeOk
      (⟨Befehl.push64 Register.rax, 1⟩ : Decodiert).laenge = true := by
    decide
  have hguard : schreibbar8 zeugWacheSpeicher
      (zeugWache.register Register.rsp - BitVec.ofNat 64 8) =
      false := by
    decide
  exact ⟨zeugWache, .rax, ⟨.push64 .rax, 1⟩, hok, rfl, hguard,
    wache_push_verweigert _ _ _ hok rfl hguard⟩

/-- LAYOUT WITNESS: a concrete fitting layout puts its callee-save
    slots inside the frame. -/
theorem belegung_gerettet_schranke_zeuge :
    ∃ (b : Belegung) (r : Rahmen) (i : Nat),
      (i < b.gerettet) ∧ (Belegung.passt b r = true) ∧
        b.gerettetIdx i < r.schlitzZahl := by
  refine ⟨{ spill := 1, gerettet := 2, stapelArgs := 1 },
    { basis := 8192, tiefe := 32 }, 1, by decide, by decide, ?_⟩
  exact belegung_gerettet_schranke _ _ _ (by decide) (by decide)

/- CUTS:
   - No decoder, TSO bridge, source correspondence, ABI/loader, cost
     transfer or final-image acceptance is proved here: this module
     reuses the accepted pilot `schritt`, `Stapel` frame obligations,
     `Regionen` permissions and `Byteschritt` fetch for frame-chain
     preservation and guard refusal only. Alignment (`ausgerichtet16`,
     `rsp8_runter_rauf`) never implies frame or guard validity
     (`ausrichtung_ohne_rahmen`). Full source-to-final-bytes validation
     remains OPEN. Interrupts, concurrency, callee-save/entry contracts
     and external ABI byte correspondence stay OPEN (see `Stapel` CUTS).
-/

#print axioms rsp8_runter_rauf
#print axioms KetteOk
#print axioms rspImRahmen
#print axioms push_pop_wiederhergestellt
#print axioms call_ret_wiederhergestellt
#print axioms verschachtelt_wiederhergestellt
#print axioms nicht_ausfuehrbar_verweigert
#print axioms ret_ins_nicht_ausfuehrbar_verweigert
#print axioms Wache
#print axioms wache_schreibschutz
#print axioms wache_push_verweigert
#print axioms wache_call_verweigert
#print axioms ausrichtung_ohne_rahmen
#print axioms kette_ok_sonde
#print axioms belegung_gerettet_schranke
#print axioms push_pop_wiederhergestellt_zeuge
#print axioms call_ret_wiederhergestellt_zeuge
#print axioms verschachtelt_wiederhergestellt_zeuge
#print axioms ret_ins_nicht_ausfuehrbar_verweigert_zeuge
#print axioms wache_push_verweigert_zeuge
#print axioms belegung_gerettet_schranke_zeuge

end Gabbro.Grammatik.X86
