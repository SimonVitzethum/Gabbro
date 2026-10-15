/-
  File:      Grammatik/X86/CallAlign16.lean
  Subject:   16-byte call-site alignment obligation with checked rsp.

  Lane 771: the call alignment obligation for every loaded image -- rsp is
  16-byte aligned at each call site, the post-call top carries the 8-byte
  return-word offset, a matching return restores the aligned top, and a
  misaligned call site refuses loudly. Reuses the canonical `Zustand` /
  `Speicher` vocabulary, the accepted `Stapel.ausgerichtet16` predicate,
  the accepted `Ausfuehrung.schritt` call/return steps, the accepted
  `Byteschritt.fetchDekodiert` fetch and the accepted
  `StackUnwind.call_ret_wiederhergestellt` restoration. No new machine,
  no new decoder row, no source claim.

  Provenance: Intel SDM combined volumes 1-4, edition 325462-093US
  (`.tmp/HARDWARE-REFERENCES/REFERENCES.json`, sha256
  `a4a62e6a7ba11a76c7753a195b825087306812aac39b930973f9168ee599f321`);
  procedure-call stack alignment is the 16-byte before-call rule whose
  call/return offset relation is proved here from `BitVec.sub_add_cancel`
  over the canonical steps, not from prose. Exact SDM section transfer
  for faulting misaligned SSE accesses stays OPEN (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Stapel
import Grammatik.X86.Codec
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt
import Grammatik.X86.StackUnwind

namespace Gabbro.Grammatik.X86

/-- Call-site instruction class: only `call32` pushes a return word. -/
def istRuf : Befehl → Bool
  | .call32 _ => true
  | _ => false

/-- Call-site alignment: rsp is 16-byte aligned before the call. -/
def rufAlignOk (s : Zustand) : Bool :=
  ausgerichtet16 (s.register Register.rsp)

/-- Post-call stack offset: one pushed return word below an aligned top. -/
def nachRufVersatz (oben : Adresse) : Bool :=
  decide (oben.toNat % 16 = 8)

/-- Checked call step: a call site with misaligned rsp refuses loudly
    (`none`); every other step is the accepted `schritt`. -/
def callGeprueft (d : Decodiert) (s : Zustand) : Option Zustand :=
  match istRuf d.befehl && !rufAlignOk s with
  | true => none
  | false => schritt d s

/-- Checked byte step from actual memory: fetch through the accepted
    `fetchDekodiert`, then the checked call gate. -/
def rufByteschritt (s : Zustand) : ByteAusgang :=
  match fetchDekodiert s with
  | none => .verweigert
  | some (d, _) =>
    match callGeprueft d s with
    | none => .verweigert
    | some s' => .weiter s'

/-! ## Call-site gate: classification and checked steps. -/

/-- The call form classifies as a call site. -/
theorem istRuf_call (disp : BitVec 32) : istRuf (.call32 disp) = true := rfl

/-- OFFSET: one pushed word below an aligned top carries offset 8.
    From `BitVec.sub_add_cancel` through `BitVec.toNat_add`: the
    cancelled sum pins the wrapped difference, and `omega` reads the
    offset off the modulus. Uses the alignment hypothesis. -/
theorem rsp8_versatz8 (x : Wort) (h : x.toNat % 16 = 0) :
    (x - BitVec.ofNat 64 8).toNat % 16 = 8 := by
  have hlt := x.isLt
  have hy := (x - BitVec.ofNat 64 8).isLt
  have h8 : (BitVec.ofNat 64 8).toNat = 8 := by decide
  have hcancel :
      ((x - BitVec.ofNat 64 8) + BitVec.ofNat 64 8).toNat = x.toNat := by
    rw [BitVec.sub_add_cancel]
  rw [BitVec.toNat_add, h8] at hcancel
  have hN : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  rw [hN] at hcancel hlt hy
  omega

/-- ALIGNED CALL PASSES: at an aligned call site the checked step IS the
    accepted step. Uses the call shape, the alignment and the step. -/
theorem callGeprueft_call_erfolg (d : Decodiert) (s s' : Zustand)
    (disp : BitVec 32)
    (hbef : d.befehl = .call32 disp) (hali : rufAlignOk s = true)
    (hstep : schritt d s = some s') :
    callGeprueft d s = some s' := by
  have hc : (istRuf d.befehl && !rufAlignOk s) = false := by
    simp [hbef, hali, istRuf]
  unfold callGeprueft
  simp only [hc, hstep]

/-- MISALIGNED CALL REFUSES: at a misaligned call site the checked step
    is an explicit refusal, never a silent skip. Uses the call shape and
    the misalignment. -/
theorem callGeprueft_fehlalign (d : Decodiert) (s : Zustand)
    (disp : BitVec 32)
    (hbef : d.befehl = .call32 disp) (hmis : rufAlignOk s = false) :
    callGeprueft d s = none := by
  have hc : (istRuf d.befehl && !rufAlignOk s) = true := by
    simp [hbef, hmis, istRuf]
  unfold callGeprueft
  simp only [hc]

/-- NON-CALL PASSES THROUGH: outside call sites the checked step IS the
    accepted step. Uses the non-call classification. -/
theorem callGeprueft_durchlass (d : Decodiert) (s : Zustand)
    (hruf : istRuf d.befehl = false) :
    callGeprueft d s = schritt d s := by
  unfold callGeprueft
  simp only [hruf, Bool.false_and]

/-! ## Call/return connection: checked rsp at both ends. -/

/-- CONNECTION: over actual `schritt` executions, an aligned call site
    takes the checked step, the post-call top carries offset 8, and the
    matching return restores the aligned top. Every premise pins one
    guard of the two steps, of the read-back, or of the alignment. -/
theorem CallAlign16_verbindung (s s1 s2 : Zustand) (d1 d2 : Decodiert)
    (disp : BitVec 32) (m : Speicher) (ziel : Wort)
    (hok1 : laengeOk d1.laenge = true)
    (hbef1 : d1.befehl = .call32 disp)
    (hali : rufAlignOk s = true)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip d1.laenge) = some m)
    (hles : lesbar8 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      = true)
    (hstep1 : schritt d1 s = some s1)
    (hrd : read64 s1.speicher (s1.register Register.rsp) = some ziel)
    (hstep2 : schritt d2 s1 = some s2)
    (hok2 : laengeOk d2.laenge = true)
    (hbef2 : d2.befehl = .ret) :
    callGeprueft d1 s = some s1 ∧
    nachRufVersatz (s1.register Register.rsp) = true ∧
    s2.register Register.rsp = s.register Register.rsp ∧
    rufAlignOk s2 = true := by
  have hcall := schritt_call32_erfolg d1 s disp m hok1 hbef1 hwr
  have hs1 : s1 = schrittCall s Register.rsp m
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip d1.laenge + dispWort disp) :=
    (Option.some_inj.mp (hcall.symm.trans hstep1)).symm
  rw [hs1] at hrd hstep2 ⊢
  have hrsp : (schrittCall s Register.rsp m
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip d1.laenge + dispWort disp)).register
      Register.rsp =
      s.register Register.rsp - BitVec.ofNat 64 8 := by
    unfold schrittCall
    show (regSet s.register Register.rsp
      (s.register Register.rsp - BitVec.ofNat 64 8)) Register.rsp = _
    exact regSet_gleich _ _ _
  have haliN : (s.register Register.rsp).toNat % 16 = 0 := by
    unfold rufAlignOk ausgerichtet16 at hali
    exact of_decide_eq_true hali
  have hvers : nachRufVersatz ((schrittCall s Register.rsp m
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip d1.laenge + dispWort disp)).register
      Register.rsp) = true := by
    unfold nachRufVersatz
    rw [hrsp, decide_eq_true_eq]
    exact rsp8_versatz8 _ haliN
  have hrest := call_ret_wiederhergestellt s (schrittCall s Register.rsp m
    (s.register Register.rsp - BitVec.ofNat 64 8)
    (ripNach s.rip d1.laenge + dispWort disp)) s2 disp d1 d2 m ziel
    hok1 hbef1 hwr hles hcall hrd hstep2 hok2 hbef2
  have hali2 : rufAlignOk s2 = true := by
    unfold rufAlignOk ausgerichtet16
    rw [decide_eq_true_eq, hrest.1]
    exact haliN
  exact ⟨callGeprueft_call_erfolg d1 s _ disp hbef1 hali hcall,
    hvers, hrest.1, hali2⟩

/-! ## Byte-level gate: fetched call sites through actual memory. -/

/-- FETCHED MISALIGNED CALL REFUSES: actual fetched bytes decoding to a
    call at a misaligned site admit no byte transition. Uses the fetch,
    the call shape and the misalignment. -/
theorem rufByteschritt_verweigert_fehlalign (s : Zustand) (d : Decodiert)
    (rest : List Byte) (disp : BitVec 32)
    (hf : fetchDekodiert s = some (d, rest))
    (hbef : d.befehl = .call32 disp)
    (hmis : rufAlignOk s = false) :
    rufByteschritt s = .verweigert := by
  have hg : callGeprueft d s = none :=
    callGeprueft_fehlalign d s disp hbef hmis
  unfold rufByteschritt
  simp only [hf, hg]

/-- FETCHED ALIGNED CALL STEPS: actual fetched bytes decoding to a call
    at an aligned site step through the checked gate. Uses the fetch,
    the call shape, the alignment and the step. -/
theorem rufByteschritt_weiter_ausgerichtet (s s' : Zustand) (d : Decodiert)
    (rest : List Byte) (disp : BitVec 32)
    (hf : fetchDekodiert s = some (d, rest))
    (hbef : d.befehl = .call32 disp)
    (hali : rufAlignOk s = true)
    (hstep : schritt d s = some s') :
    rufByteschritt s = .weiter s' := by
  have hg : callGeprueft d s = some s' :=
    callGeprueft_call_erfolg d s s' disp hbef hali hstep
  unfold rufByteschritt
  simp only [hf, hg]

/-! ## Per-image witness: an accepted image carrying a call. -/

/-- Witness call displacement: straight ahead, target inside code. -/
def alignDisp : BitVec 32 := BitVec.ofNat 32 0

/-- Witness file bytes: the canonical call plus a return byte. -/
def alignDatei : List Byte :=
  encode (.call32 alignDisp) ++ encode .ret

/-- Witness code section: the six file bytes, executable only. -/
def alignCode : Abschnitt :=
  { dateiOff := 0, dateiLen := 6, vaddr := 0x1000, memLen := 6,
    lesbar := false, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Witness data section: sixteen zero-defined stack bytes. -/
def alignDaten : Abschnitt :=
  { dateiOff := 6, dateiLen := 0, vaddr := 0x2000, memLen := 16,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- The witness image: fixed bias, entry inside code. -/
def alignBild : Bild :=
  { datei := alignDatei
    abschnitte := [alignCode, alignDaten]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- The witness image is accepted under profile 48. -/
theorem alignBild_wohlgeformt : wohlgeformt .p48 alignBild = true := by
  decide

/-- Witness registers: stack top at `0x2010`, everything else zero. -/
def alignReg : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 0x2010 else BitVec.ofNat 64 0

/-- Witness start state: call site at `0x1000` over loaded image memory. -/
def alignS0 : Zustand :=
  { register := alignReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 0x1000, speicher := geladen alignBild 0 }

/-- The witness call site is 16-byte aligned. -/
theorem alignS0_ausgerichtet : rufAlignOk alignS0 = true := by
  decide

/-- The witness stack slot is writable for eight bytes. -/
theorem alignS0_slot_schreibbar :
    schreibbar8 alignS0.speicher
      (alignS0.register Register.rsp - BitVec.ofNat 64 8) = true := by
  decide

/-- The witness stack slot is readable for eight bytes. -/
theorem alignS0_slot_lesbar :
    lesbar8 alignS0.speicher
      (alignS0.register Register.rsp - BitVec.ofNat 64 8) = true := by
  decide

/-- FETCH FROM IMAGE BYTES: the loaded six bytes decode to the call
    with the return byte as suffix. -/
theorem alignS0_fetch : fetchDekodiert alignS0 =
    some (⟨.call32 alignDisp, 5⟩, encode .ret) := by
  decide

/-! ## Joint witness: reached call/return over image bytes. -/

/-- Witness stack slot: one word below the aligned top. -/
def alignOben : Adresse := BitVec.ofNat 64 0x2008

/-- Memory after the witness call stores the return word `0x1005`. -/
def alignM1 : Speicher := { alignS0.speicher with
  bytes := writeBytes alignS0.speicher alignOben (ripNach alignS0.rip 5) }

/-- State after the witness call: control at `0x1005`, top at `0x2008`. -/
def alignS1 : Zustand := schrittCall alignS0 Register.rsp alignM1
  (alignS0.register Register.rsp - BitVec.ofNat 64 8)
  (ripNach alignS0.rip 5 + dispWort alignDisp)

/-- State after the witness return: control back at `0x1005`. -/
def alignS2 : Zustand := schrittRet alignS1 Register.rsp
  (alignS1.register Register.rsp + BitVec.ofNat 64 8)
  (ripNach alignS0.rip 5)

/-- Misaligned twin: same code, stack top at `0x2008` (offset 8). -/
def alignSmis : Zustand :=
  { alignS0 with register := (fun q =>
    if q = Register.rsp then BitVec.ofNat 64 0x2008
    else BitVec.ofNat 64 0) }

/-- The twin site is misaligned. -/
theorem alignSmis_fehlalign : rufAlignOk alignSmis = false := by
  decide

/-- JOINT WITNESS for `CallAlign16_verbindung`: every premise holds
    jointly on a non-degenerate reached run over loaded image bytes --
    the call observably changes memory (zero becomes the return word
    below the old top), `lauf` chains call and return, the top is
    restored -- plus a misaligned twin that the gate loudly refuses. -/
theorem CallAlign16_verbindung_zeuge :
    ∃ (s s1 s2 : Zustand) (d1 d2 : Decodiert) (disp : BitVec 32)
      (m : Speicher) (ziel : Wort),
      laengeOk d1.laenge = true ∧
      d1.befehl = .call32 disp ∧
      rufAlignOk s = true ∧
      (write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip d1.laenge) = some m) ∧
      (lesbar8 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        = true) ∧
      (schritt d1 s = some s1) ∧
      (read64 s1.speicher (s1.register Register.rsp) = some ziel) ∧
      (schritt d2 s1 = some s2) ∧
      laengeOk d2.laenge = true ∧
      d2.befehl = .ret ∧
      (lauf [d1, d2] s = some s2) ∧
      (s.speicher.bytes alignOben ≠ s1.speicher.bytes alignOben) ∧
      (s2.register Register.rsp = s.register Register.rsp) ∧
      (∃ smis : Zustand, rufAlignOk smis = false ∧
        callGeprueft d1 smis = none) := by
  have hslot : alignS0.register Register.rsp - BitVec.ofNat 64 8 =
      alignOben := by
    decide
  have hok1 : laengeOk (⟨.call32 alignDisp, 5⟩ : Decodiert).laenge =
      true := by
    decide
  have hok2 : laengeOk (⟨.ret, 1⟩ : Decodiert).laenge = true := by
    decide
  have hlesOben : lesbar8 alignS0.speicher alignOben = true := by
    decide
  have hschOben : schreibbar8 alignS0.speicher alignOben = true := by
    decide
  have hwrOben : write64 alignS0.speicher alignOben
      (ripNach alignS0.rip 5) = some alignM1 := by
    unfold write64 alignM1
    rw [if_pos hschOben]
  have hwr : write64 alignS0.speicher
      (alignS0.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach alignS0.rip 5) = some alignM1 := by
    rw [hslot]
    exact hwrOben
  have hles : lesbar8 alignS0.speicher
      (alignS0.register Register.rsp - BitVec.ofNat 64 8) = true := by
    rw [hslot]
    exact hlesOben
  have hstep1 : schritt (⟨.call32 alignDisp, 5⟩ : Decodiert) alignS0 =
      some alignS1 :=
    schritt_call32_erfolg _ _ _ _ hok1 rfl hwr
  have e1 : alignS1.speicher = alignM1 := rfl
  have e2 : alignS1.register Register.rsp = alignOben := by
    have hrr : alignS1.register Register.rsp =
        alignS0.register Register.rsp - BitVec.ofNat 64 8 := by
      unfold alignS1 schrittCall
      show (regSet alignS0.register Register.rsp
        (alignS0.register Register.rsp - BitVec.ofNat 64 8))
        Register.rsp = _
      exact regSet_gleich _ _ _
    rw [hrr, hslot]
  have hrd : read64 alignS1.speicher (alignS1.register Register.rsp) =
      some (ripNach alignS0.rip 5) := by
    have hrr := read64_nach_write64 alignS0.speicher alignM1 alignOben
      (ripNach alignS0.rip 5) hwrOben hlesOben
    rw [e1, e2]
    exact hrr
  have hstep2 : schritt (⟨.ret, 1⟩ : Decodiert) alignS1 = some alignS2 :=
    schritt_ret_erfolg _ _ _ hok2 rfl hrd
  have hlauf : lauf [⟨.call32 alignDisp, 5⟩, ⟨.ret, 1⟩] alignS0 =
      some alignS2 := by
    simp only [lauf, hstep1, hstep2]
  have hrip5 : ripNach alignS0.rip 5 = BitVec.ofNat 64 0x1005 := by
    decide
  have hchg : alignS0.speicher.bytes alignOben ≠
      alignS1.speicher.bytes alignOben := by
    have hzero : alignS0.speicher.bytes alignOben = BitVec.ofNat 8 0 := by
      have hfind : abteilFinden alignBild.abschnitte 0 0x2008 =
          some alignDaten := by
        decide
      have hbss := geladenByte_bss alignBild 0 0x2008 alignDaten hfind
        (by decide : 0 + alignDaten.vaddr + alignDaten.dateiLen ≤ 0x2008)
      have hto : alignOben.toNat = 0x2008 := by decide
      show ladenByte alignBild 0 alignOben.toNat = _
      rw [hto]
      exact hbss
    have hbyte : alignS1.speicher.bytes alignOben =
        wortByte (ripNach alignS0.rip 5) 0 := by
      show writeBytes alignS0.speicher alignOben
        (ripNach alignS0.rip 5) alignOben = _
      unfold writeBytes
      have hhit := writeBytesN_hit alignS0.speicher alignOben
        (ripNach alignS0.rip 5) 8 0 (by decide) (by decide)
      rw [addrOff_null] at hhit
      exact hhit
    rw [hzero, hbyte, hrip5]
    decide
  have hconn := CallAlign16_verbindung alignS0 alignS1 alignS2
    ⟨.call32 alignDisp, 5⟩ ⟨.ret, 1⟩ alignDisp alignM1
    (ripNach alignS0.rip 5) hok1 rfl alignS0_ausgerichtet hwr hles
    hstep1 hrd hstep2 hok2 rfl
  have hmisWit : ∃ smis : Zustand, rufAlignOk smis = false ∧
      callGeprueft (⟨.call32 alignDisp, 5⟩ : Decodiert) smis = none :=
    ⟨alignSmis, alignSmis_fehlalign,
      callGeprueft_fehlalign _ _ _ rfl alignSmis_fehlalign⟩
  exact ⟨alignS0, alignS1, alignS2, ⟨.call32 alignDisp, 5⟩, ⟨.ret, 1⟩,
    alignDisp, alignM1, ripNach alignS0.rip 5,
    hok1, rfl, alignS0_ausgerichtet, hwr, hles, hstep1, hrd, hstep2,
    hok2, rfl, hlauf, hchg, hconn.2.2.1, hmisWit⟩

/- CUTS:
    Proved here (all over the REUSED canonical `Zustand`/`Speicher`
    vocabulary, the accepted `Stapel.ausgerichtet16` predicate, the
    accepted `Ausfuehrung.schritt` call/return steps, the accepted
    `Byteschritt.fetchDekodiert` fetch and the accepted
    `StackUnwind.call_ret_wiederhergestellt` restoration -- no new
    machine, no new decoder row, no new instruction, no source claim):
    - call-site gate `istRuf`/`rufAlignOk`/`callGeprueft`: an aligned call
      site takes the accepted step, a misaligned call site refuses loudly,
      non-call steps pass through;
    - offset arithmetic `rsp8_versatz8`: one pushed word below an aligned
      top carries offset 8, from `BitVec.sub_add_cancel`;
    - connection `CallAlign16_verbindung`: checked call step, post-call
      offset 8, rsp restoration and realignment at return;
    - byte-level gate `rufByteschritt`: fetched misaligned calls refuse,
      fetched aligned calls step, through actual memory bytes;
    - per-image joint witness `CallAlign16_verbindung_zeuge`: an accepted
      image (`alignBild_wohlgeformt`) carrying canonical call bytes whose
      fetch decodes from loaded memory, with a memory-changing reached
      `lauf` call/return run plus a misaligned refusal twin.
    NOT proved here, and not claimed:
    - No silicon correspondence: the 16-byte rule is the stated checked
      obligation (Intel SDM snapshot in REFERENCES.json, edition
      325462-093US); exact SDM section transfer for faulting misaligned
      SSE accesses, and any vendor/silicon difference, stay OPEN.
    - No ABI entry claim: process-entry rsp alignment is not stated.
    - No TSO/concurrency bridge: all facts are sequential over one
      `Speicher`; store buffers, forwarding and GX refinement stay with
      the TSO-bridge work.
    - No source correspondence, no cost or time transfer, no handler or
      fault-delivery claim.
-/

#print axioms istRuf
#print axioms rufAlignOk
#print axioms nachRufVersatz
#print axioms callGeprueft
#print axioms rufByteschritt
#print axioms istRuf_call
#print axioms rsp8_versatz8
#print axioms callGeprueft_call_erfolg
#print axioms callGeprueft_fehlalign
#print axioms callGeprueft_durchlass
#print axioms CallAlign16_verbindung
#print axioms rufByteschritt_verweigert_fehlalign
#print axioms rufByteschritt_weiter_ausgerichtet
#print axioms alignBild_wohlgeformt
#print axioms alignS0_ausgerichtet
#print axioms alignS0_slot_schreibbar
#print axioms alignS0_slot_lesbar
#print axioms alignS0_fetch
#print axioms alignSmis_fehlalign
#print axioms CallAlign16_verbindung_zeuge

end Gabbro.Grammatik.X86
