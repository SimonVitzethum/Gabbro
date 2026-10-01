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

/- CUTS:
   - Joint non-degenerate witnesses follow in the next commit.
   - No new executor, decoder, source or OS claim (see header).
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

end Gabbro.Grammatik.X86
