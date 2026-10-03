/-
  Composition closing: thread-stack guard pages to fault delivery (lane 848).

  Producer/consumer interface closed here: the producers are the accepted
  fetched stack steps (`StackExecution.byteschritt_geholt_call/push` and
  the guard refusals `byteschritt_geholt_call_wache/push_wache`), the
  accepted step-level guard facts (`StackUnwind.wache_push/call_verweigert`),
  the accepted frame-save facts (`Stapel.sichereWort_rahmen`) and the
  accepted store facts (`Speicher.write64_rahmen`,
  `write64_verweigert_kein_effekt`); the consumer is fault delivery (a
  stack overflow into the guard loudly refuses as `byteschritt .verweigert`
  with no store outcome, so no neighbour byte can change). This file only
  composes already-accepted theorems; it re-proves no step, fetch, frame
  or store internals and defines no second interpreter or executor.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.Stapel
import Grammatik.X86.StackUnwind
import Grammatik.X86.StackExecution

namespace Gabbro.Grammatik.X86

/-- FETCHED CALL SUCCESS (composition leg): from actual call bytes, the
    composed byte step stores the correct next-RIP return word below the
    pre-state top and transfers control. Reuses the accepted
    `byteschritt_geholt_call` by name; generic over arbitrary admitted
    inputs. -/
theorem wachenCallWeiter (s : Zustand) (disp : BitVec 32)
    (suffix : List Byte) (m : Speicher)
    (hwin : StapelGeholt s (.call32 disp) suffix)
    (hexe : ausfuehrbarN s.speicher s.rip
      (encode (.call32 disp)).length = true)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length) = some m) :
    byteschritt s = .weiter (schrittCall s Register.rsp m
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length + dispWort disp)) :=
  byteschritt_geholt_call s disp suffix m hwin hexe hwr

/-- FETCHED PUSH SUCCESS (composition leg): from actual push bytes, the
    composed byte step stores the pre-state source value below the
    pre-state top. Reuses the accepted `byteschritt_geholt_push` by name;
    generic over arbitrary admitted inputs. -/
theorem wachenPushWeiter (s : Zustand) (src : Register)
    (suffix : List Byte) (m : Speicher)
    (hwin : StapelGeholt s (.push64 src) suffix)
    (hexe : ausfuehrbarN s.speicher s.rip
      (encode (.push64 src)).length = true)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = some m) :
    byteschritt s = .weiter (schrittPush s Register.rsp
      (ripNach s.rip (encode (.push64 src)).length)
      (s.register Register.rsp - BitVec.ofNat 64 8) m) :=
  byteschritt_geholt_push s src suffix m hwin hexe hwr

/-- FETCHED CALL ONTO A GUARD REFUSED (composition leg: fault delivery):
    actual call bytes decode, but the return-address store below the top
    hits the write-protected guard, so the composed byte step loudly
    refuses. Reuses the accepted `byteschritt_geholt_call_wache` by name;
    generic over arbitrary admitted inputs. -/
theorem wachenCallVerweigert (s : Zustand) (disp : BitVec 32)
    (suffix : List Byte)
    (hwin : StapelGeholt s (.call32 disp) suffix)
    (hexe : ausfuehrbarN s.speicher s.rip
      (encode (.call32 disp)).length = true)
    (hguard : schreibbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = false) :
    byteschritt s = .verweigert :=
  byteschritt_geholt_call_wache s disp suffix hwin hexe hguard

/-- FETCHED PUSH ONTO A GUARD REFUSED (composition leg: fault delivery):
    actual push bytes decode, but the word store below the top hits the
    write-protected guard, so the composed byte step loudly refuses.
    Reuses the accepted `byteschritt_geholt_push_wache` by name; generic
    over arbitrary admitted inputs. -/
theorem wachenPushVerweigert (s : Zustand) (src : Register)
    (suffix : List Byte)
    (hwin : StapelGeholt s (.push64 src) suffix)
    (hexe : ausfuehrbarN s.speicher s.rip
      (encode (.push64 src)).length = true)
    (hguard : schreibbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = false) :
    byteschritt s = .verweigert :=
  byteschritt_geholt_push_wache s src suffix hwin hexe hguard

/-- STEP-LEVEL PUSH ONTO A GUARD REFUSED (composition leg): below a
    write-protected guard the push step has no outcome at all, so the
    byte step built over it cannot reach a successor either. Reuses the
    accepted `wache_push_verweigert` by name; every premise pins one
    guard of the step. -/
theorem wachenSchrittPushVerweigert (s : Zustand) (src : Register)
    (d : Decodiert)
    (hok : laengeOk d.laenge = true)
    (hb : d.befehl = .push64 src)
    (hguard : schreibbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = false) :
    schritt d s = none :=
  wache_push_verweigert s src d hok hb hguard

/-- STEP-LEVEL CALL ONTO A GUARD REFUSED (composition leg): below a
    write-protected guard the call step has no outcome at all instead of
    spilling the return address into the guard. Reuses the accepted
    `wache_call_verweigert` by name; every premise pins one guard. -/
theorem wachenSchrittCallVerweigert (s : Zustand) (disp : BitVec 32)
    (d : Decodiert)
    (hok : laengeOk d.laenge = true)
    (hb : d.befehl = .call32 disp)
    (hguard : schreibbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = false) :
    schritt d s = none :=
  wache_call_verweigert s disp d hok hb hguard

/-- FRAME-SAVE NEIGHBOUR PRESERVATION (composition leg): a checked frame
    save changes nothing outside its eight slot bytes, so an in-frame
    stack store never corrupts a neighbour slot. Reuses the accepted
    `sichereWort_rahmen` by name; every premise is used. -/
theorem wachenNachbarBleibt (m m' : Speicher) (r : Rahmen)
    (idx : Nat) (x : Adresse) (v : Wort)
    (hb : idx < r.schlitzZahl)
    (hwr : sichereWort m r idx v = some m')
    (haussen : ∀ k : Nat, k < 8 → x ≠ addrOff (r.schlitzAddr idx) k) :
    m'.bytes x = m.bytes x :=
  sichereWort_rahmen m m' r idx x v hb hwr haussen

/-- GUARD STORE HAS NO OUTCOME (composition leg: instead of corrupting
    neighbours): a store into the write-protected guard answers no
    successor memory at all. Reuses the accepted
    `write64_verweigert_kein_effekt` by name; every premise is used. -/
theorem wachenVerweigertOhneEffekt (m m' : Speicher) (a : Adresse)
    (v : Wort) (h : schreibbar8 m a = false) :
    write64 m a v ≠ some m' :=
  write64_verweigert_kein_effekt m m' a v h

/-- FETCHED RETURN INTO A GUARD REFUSED (composition leg: fault
    delivery): an actual return byte steps to the popped target, but the
    target carries no execute permission -- guard regions carry
    `ausfuehrbar = false` -- so the following byte step loudly refuses
    instead of fetching bytes as code there. Reuses the accepted
    `byteschritt_geholt_ret_nicht_ausfuehrbar` by name; every premise pins
    one guard of the return step or of the refusal. -/
theorem wachenRetVerweigert (s s' : Zustand)
    (suffix : List Byte) (ziel : Wort)
    (hwin : StapelGeholt s .ret suffix)
    (hexe : ausfuehrbarN s.speicher s.rip (encode .ret).length = true)
    (hrd : read64 s.speicher (s.register Register.rsp) = some ziel)
    (hstep : byteschritt s = .weiter s')
    (hxe : s.speicher.ausfuehrbar ziel = false) :
    byteschritt s' = .verweigert :=
  byteschritt_geholt_ret_nicht_ausfuehrbar s s' suffix ziel hwin hexe hrd
    hstep hxe

/-- GUARD-PAGE CLOSING through the composed byte step, generic over
    arbitrary admitted inputs: fetched call/push stores below a writable
    top reach their stack rule with the correct word; the same fetched
    stores below a write-protected guard loudly refuse with no store
    outcome at all (so no neighbour byte can change); a fetched return
    into a non-executable guard address refuses the following byte step;
    and every checked in-frame save preserves all neighbour bytes.
    Composes `wachenCallWeiter`, `wachenPushWeiter`,
    `wachenCallVerweigert`, `wachenPushVerweigert`, `wachenRetVerweigert`,
    `wachenNachbarBleibt` and `wachenVerweigertOhneEffekt`; no step,
    fetch, frame or store fact is re-proved here. -/
theorem ComposeGuardPages_verbindung :
    (∀ (s : Zustand) (disp : BitVec 32) (suffix : List Byte) (m : Speicher),
      StapelGeholt s (.call32 disp) suffix →
      ausfuehrbarN s.speicher s.rip (encode (.call32 disp)).length = true →
      write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip (encode (.call32 disp)).length) = some m →
      byteschritt s = .weiter (schrittCall s Register.rsp m
        (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip (encode (.call32 disp)).length + dispWort disp))) ∧
    (∀ (s : Zustand) (src : Register) (suffix : List Byte) (m : Speicher),
      StapelGeholt s (.push64 src) suffix →
      ausfuehrbarN s.speicher s.rip (encode (.push64 src)).length = true →
      write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (s.register src) = some m →
      byteschritt s = .weiter (schrittPush s Register.rsp
        (ripNach s.rip (encode (.push64 src)).length)
        (s.register Register.rsp - BitVec.ofNat 64 8) m)) ∧
    (∀ (s : Zustand) (disp : BitVec 32) (suffix : List Byte),
      StapelGeholt s (.call32 disp) suffix →
      ausfuehrbarN s.speicher s.rip (encode (.call32 disp)).length = true →
      schreibbar8 s.speicher
        (s.register Register.rsp - BitVec.ofNat 64 8) = false →
      byteschritt s = .verweigert ∧
      ∀ (m' : Speicher), write64 s.speicher
        (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip (encode (.call32 disp)).length) ≠ some m') ∧
    (∀ (s : Zustand) (src : Register) (suffix : List Byte),
      StapelGeholt s (.push64 src) suffix →
      ausfuehrbarN s.speicher s.rip (encode (.push64 src)).length = true →
      schreibbar8 s.speicher
        (s.register Register.rsp - BitVec.ofNat 64 8) = false →
      byteschritt s = .verweigert ∧
      ∀ (m' : Speicher), write64 s.speicher
        (s.register Register.rsp - BitVec.ofNat 64 8)
        (s.register src) ≠ some m') ∧
    (∀ (s s' : Zustand) (suffix : List Byte) (ziel : Wort),
      StapelGeholt s .ret suffix →
      ausfuehrbarN s.speicher s.rip (encode .ret).length = true →
      read64 s.speicher (s.register Register.rsp) = some ziel →
      byteschritt s = .weiter s' →
      s.speicher.ausfuehrbar ziel = false →
      byteschritt s' = .verweigert) ∧
    (∀ (m m' : Speicher) (r : Rahmen) (idx : Nat) (x : Adresse) (v : Wort),
      idx < r.schlitzZahl →
      sichereWort m r idx v = some m' →
      (∀ k : Nat, k < 8 → x ≠ addrOff (r.schlitzAddr idx) k) →
      m'.bytes x = m.bytes x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s disp suffix m hwin hexe hwr
    exact wachenCallWeiter s disp suffix m hwin hexe hwr
  · intro s src suffix m hwin hexe hwr
    exact wachenPushWeiter s src suffix m hwin hexe hwr
  · intro s disp suffix hwin hexe hguard
    exact ⟨wachenCallVerweigert s disp suffix hwin hexe hguard,
      fun m' => wachenVerweigertOhneEffekt s.speicher m' _ _ hguard⟩
  · intro s src suffix hwin hexe hguard
    exact ⟨wachenPushVerweigert s src suffix hwin hexe hguard,
      fun m' => wachenVerweigertOhneEffekt s.speicher m' _ _ hguard⟩
  · intro s s' suffix ziel hwin hexe hrd hstep hxe
    exact wachenRetVerweigert s s' suffix ziel hwin hexe hrd hstep hxe
  · intro m m' r idx x v hb hwr haussen
    exact wachenNachbarBleibt m m' r idx x v hb hwr haussen

/-- Push-guard witness memory: a canonical `push rax` byte at 4096 with
    an executable 15-byte window, but every stack byte write-protected.
    Same code shape as the accepted nested run, guard shape as the
    accepted call-guard witness. -/
def wachePushSpeicher : Speicher :=
  { bytes := fun a =>
      if a.toNat = 4096 then natByte 80 else BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => false
    ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4111) }

/-- Push-guard witness start: `push` at 4096, stack top at 8192. -/
def wachePushS : Zustand :=
  { nestS0 with speicher := wachePushSpeicher }

/-- PUSH-GUARD FETCH: the actual bytes at 4096 are the canonical
    `push rax` byte followed by fourteen zero bytes. -/
theorem wachePush_geholt : StapelGeholt wachePushS (.push64 .rax)
    (List.replicate 14 (BitVec.ofNat 8 0)) := by
  unfold StapelGeholt
  decide

/-- The consumed push prefix stays executable under the guard. -/
theorem wachePush_exe : ausfuehrbarN wachePushS.speicher wachePushS.rip
    (encode (.push64 .rax)).length = true := by
  decide

/-- The stack slot below the top is guard-protected. -/
theorem wachePush_guard : schreibbar8 wachePushS.speicher
    (wachePushS.register Register.rsp - BitVec.ofNat 64 8) = false := by
  decide

/-- JOINT WITNESS for `ComposeGuardPages_verbindung`: every leg
    instantiated jointly on non-degenerate states (executable code plus a
    writable stack cell, the analogue of a written table): a reached
    memory-changing run through the composed call step (zero becomes the
    return address below the old top), the fetched push step, planted
    call/push guard refusals with no store outcome, a fetched return into
    a guard address refusing the next byte step, and a checked frame save
    preserving its neighbour slot. -/
theorem ComposeGuardPages_verbindung_zeuge :
    ∃ (s : Zustand) (disp : BitVec 32) (sc : List Byte) (mc : Speicher),
      StapelGeholt s (.call32 disp) sc ∧
      (ausfuehrbarN s.speicher s.rip (encode (.call32 disp)).length
        = true) ∧
      (write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip (encode (.call32 disp)).length) = some mc) ∧
      (byteschritt s = .weiter (schrittCall s Register.rsp mc
        (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip (encode (.call32 disp)).length + dispWort disp))) ∧
      (s.speicher.bytes (s.register Register.rsp - BitVec.ofNat 64 8) ≠
        mc.bytes (s.register Register.rsp - BitVec.ofNat 64 8)) ∧
      (∃ (p : Zustand) (sp : List Byte) (mp : Speicher),
        StapelGeholt p (.push64 .rax) sp ∧
        (ausfuehrbarN p.speicher p.rip (encode (.push64 .rax)).length
          = true) ∧
        (write64 p.speicher (p.register Register.rsp - BitVec.ofNat 64 8)
          (p.register Register.rax) = some mp) ∧
        (byteschritt p = .weiter (schrittPush p Register.rsp
          (ripNach p.rip (encode (.push64 .rax)).length)
          (p.register Register.rsp - BitVec.ofNat 64 8) mp))) ∧
      (∃ (w : Zustand) (sw : List Byte),
        StapelGeholt w (.call32 disp) sw ∧
        (ausfuehrbarN w.speicher w.rip (encode (.call32 disp)).length
          = true) ∧
        (schreibbar8 w.speicher
          (w.register Register.rsp - BitVec.ofNat 64 8) = false) ∧
        (byteschritt w = .verweigert) ∧
        (∀ m' : Speicher, write64 w.speicher
          (w.register Register.rsp - BitVec.ofNat 64 8)
          (ripNach w.rip (encode (.call32 disp)).length) ≠ some m')) ∧
      (∃ (u : Zustand) (su : List Byte),
        StapelGeholt u (.push64 .rax) su ∧
        (ausfuehrbarN u.speicher u.rip (encode (.push64 .rax)).length
          = true) ∧
        (schreibbar8 u.speicher
          (u.register Register.rsp - BitVec.ofNat 64 8) = false) ∧
        (byteschritt u = .verweigert) ∧
        (∀ m' : Speicher, write64 u.speicher
          (u.register Register.rsp - BitVec.ofNat 64 8)
          (u.register Register.rax) ≠ some m')) ∧
      (∃ (t t' : Zustand) (st : List Byte) (z : Wort),
        StapelGeholt t .ret st ∧
        (ausfuehrbarN t.speicher t.rip (encode .ret).length = true) ∧
        (read64 t.speicher (t.register Register.rsp) = some z) ∧
        (byteschritt t = .weiter t') ∧
        (t.speicher.ausfuehrbar z = false) ∧
        (byteschritt t' = .verweigert)) ∧
      (∃ m' : Speicher,
        sichereWort speicherZeuge rahmenZeuge 1 42 = some m' ∧
        m'.bytes (rahmenZeuge.schlitzAddr 0) =
          speicherZeuge.bytes (rahmenZeuge.schlitzAddr 0)) := by
  have hwrc : write64 nestS0.speicher
      (nestS0.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach nestS0.rip (encode (.call32 nestDisp)).length) =
      some nestM1 := by
    rw [nest_rsp0]
    exact nest_call_schreibt
  have hmem : nestS0.speicher.bytes
      (nestS0.register Register.rsp - BitVec.ofNat 64 8) ≠
      nestM1.bytes
        (nestS0.register Register.rsp - BitVec.ofNat 64 8) := by
    rw [nest_rsp0]
    have hhit := writeBytesN_hit nestSpeicher nestOben0
      (ripNach nestS0.rip 5) 8 0 (by decide) (by decide)
    rw [addrOff_null] at hhit
    show BitVec.ofNat 8 0 ≠
      writeBytes nestSpeicher nestOben0 (ripNach nestS0.rip 5) nestOben0
    unfold writeBytes
    rw [hhit]
    decide
  have hwrp : write64 nestS1.speicher
      (nestS1.register Register.rsp - BitVec.ofNat 64 8)
      (nestS1.register Register.rax) = some nestMp := by
    rw [nest_rsp1]
    exact nest_push_schreibt
  have hretStep : byteschritt retNestS =
      .weiter (schrittRet retNestS Register.rsp
        (retNestS.register Register.rsp + BitVec.ofNat 64 8)
        (BitVec.ofNat 64 12288)) :=
    byteschritt_geholt_ret _ _ _ retNest_geholt retNest_exe retNest_liest
  have hnwr : sichereWort speicherZeuge rahmenZeuge 1 42 =
      some { speicherZeuge with
        bytes := writeBytes speicherZeuge (rahmenZeuge.schlitzAddr 1)
          42 } := by
    unfold sichereWort
    rw [if_pos (by decide : 1 < rahmenZeuge.schlitzZahl)]
    unfold write64
    rw [if_pos zeuge_schreibbar8]
  have haussen : ∀ k : Nat, k < 8 →
      rahmenZeuge.schlitzAddr 0 ≠
        addrOff (rahmenZeuge.schlitzAddr 1) k := by
    intro k hk
    have e0 : (rahmenZeuge.schlitzAddr 0).toNat = 0x2000 := by decide
    have e1 : (rahmenZeuge.schlitzAddr 1).toNat = 0x2008 := by decide
    have o1 : OhneUmbruch (rahmenZeuge.schlitzAddr 1) := by
      unfold OhneUmbruch
      rw [e1]
      decide
    have e2 := ohneUmbruch_addrs _ o1 k hk
    intro hcontra
    have hc := congrArg BitVec.toNat hcontra
    rw [e0, e2, e1] at hc
    omega
  refine ⟨nestS0, nestDisp, _, nestM1, nest_call_geholt, nest_call_exe,
    hwrc, wachenCallWeiter _ _ _ _ nest_call_geholt nest_call_exe hwrc,
    hmem, ⟨nestS1, _, nestMp, nest_push_geholt, nest_push_exe, hwrp,
      wachenPushWeiter _ _ _ _ nest_push_geholt nest_push_exe hwrp⟩,
    ⟨wacheNestS, _, wacheNest_geholt, wacheNest_exe, wacheNest_guard,
      wachenCallVerweigert _ _ _ wacheNest_geholt wacheNest_exe
        wacheNest_guard,
      fun m' => wachenVerweigertOhneEffekt _ m' _ _ wacheNest_guard⟩,
    ⟨wachePushS, _, wachePush_geholt, wachePush_exe, wachePush_guard,
      wachenPushVerweigert _ _ _ wachePush_geholt wachePush_exe
        wachePush_guard,
      fun m' => wachenVerweigertOhneEffekt _ m' _ _ wachePush_guard⟩,
    ⟨retNestS, _, [], _, retNest_geholt, retNest_exe, retNest_liest,
      hretStep, retNest_kein_exec,
      wachenRetVerweigert _ _ _ _ retNest_geholt retNest_exe retNest_liest
        hretStep retNest_kein_exec⟩,
    ⟨_, hnwr, wachenNachbarBleibt _ _ _ _ _ _ (by decide) hnwr haussen⟩⟩

/- CUTS:
    Proved here, by composing the accepted producer modules (no producer
    fact re-proved, no second interpreter or executor): the fetched
    call/push success legs (`wachenCallWeiter`, `wachenPushWeiter`); the
    fetched call/push guard refusals (`wachenCallVerweigert`,
    `wachenPushVerweigert`); the decoder-independent step-level guard
    refusals (`wachenSchrittPushVerweigert`,
    `wachenSchrittCallVerweigert`); the guard store with no outcome
    (`wachenVerweigertOhneEffekt`); the frame-save neighbour preservation
    (`wachenNachbarBleibt`); the fetched return into a guard address
    refusing the next byte step (`wachenRetVerweigert`); the six-leg
    generic guard-page closing (`ComposeGuardPages_verbindung`); and one
    joint non-degenerate witness with reached memory-changing runs and
    planted refusals (`ComposeGuardPages_verbindung_zeuge`, with the
    push-guard witness `wachePushSpeicher`/`wachePushS` and its fetch
    facts `wachePush_geholt`/`wachePush_exe`/`wachePush_guard`).
    NOT proved here, and not claimed:
    - No source correspondence: nothing here claims the stack carries any
      source value, contract or duty; no int-to-pointer conversion enters.
    - No hardware correspondence: refusal runs over the model `Speicher`
      permissions, not silicon; Guarded stacks, faults beyond the refused
      transition, interrupts and timing are OPEN.
    - No TSO/GX bridge: every fact is sequential over one canonical
      `Speicher`; store buffers, forwarding and coherence stay with the
      TSO-bridge work (owner: TSO bridge lanes).
    - No ABI/loader/entry/relocation/cost/final-image claim; no
      callee-save/entry contracts.
    - `verweigert` is the absence of a transition, never a termination
      claim; the divide trap and other architectural faults keep their
      own channel (`DecodeFault`), distinct from guard refusal.
-/

#print axioms wachenCallWeiter
#print axioms wachenPushWeiter
#print axioms wachenCallVerweigert
#print axioms wachenPushVerweigert
#print axioms wachenSchrittPushVerweigert
#print axioms wachenSchrittCallVerweigert
#print axioms wachenNachbarBleibt
#print axioms wachenVerweigertOhneEffekt
#print axioms wachenRetVerweigert
#print axioms ComposeGuardPages_verbindung
#print axioms ComposeGuardPages_verbindung_zeuge

end Gabbro.Grammatik.X86
