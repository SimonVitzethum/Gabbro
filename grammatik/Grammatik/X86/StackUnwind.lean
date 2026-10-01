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

/- CUTS:
   - Skeleton only: chain/refusal theorems follow in later commits.
   - No new executor, decoder, source or OS claim (see header).
-/

#print axioms rsp8_runter_rauf
#print axioms KetteOk
#print axioms rspImRahmen
#print axioms push_pop_wiederhergestellt
#print axioms call_ret_wiederhergestellt

end Gabbro.Grammatik.X86
