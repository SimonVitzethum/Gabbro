/-
  Stack-to-ABI composition closing (lane 828).

  Producer/consumer interface closed here: the accepted `Stapel` frame-slot
  vocabulary (`Rahmen`, `Belegung`, `sichereWort`/`ladeWort`) meets the
  accepted `StackUnwind` push/pop restoration (`push_pop_wiederhergestellt`)
  at the shared stack slot `r.schlitzAddr (b.gerettetIdx i) =
  s.register rsp - 8`, under the accepted `CallAlign16` call-site alignment
  (`rufAlignOk`) and the per-frame red-zone rule below. No transition,
  decoder, memory model or source claim is created here; every execution
  fact reuses the accepted producer theorems by name.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Stapel
import Grammatik.X86.StackUnwind
import Grammatik.X86.CallAlign16

namespace Gabbro.Grammatik.X86

/-- Red-zone rule per frame: the 128 bytes below `rsp` lie inside the frame
    extent, so a leaf routine's red zone never leaves the checked frame. -/
def rotZoneImRahmen (s : Zustand) (r : Rahmen) : Bool :=
  decide (r.basis + 128 ≤ (s.register Register.rsp).toNat ∧
    (s.register Register.rsp).toNat ≤ r.spitzeNat)

/-! ## Witness frame: the shared slot below the witness stack top. -/

/-- Witness frame: base 8032, depth 160, top 8192 (the witness stack top). -/
def abiRahmen : Rahmen := { basis := 8032, tiefe := 160 }

/-- Witness layout: ten spill slots, ten callee-save slots, no stack args. -/
def abiBelegung : Belegung := { spill := 10, gerettet := 10, stapelArgs := 0 }

/-- The witness layout fits the witness frame. -/
theorem abi_passt : Belegung.passt abiBelegung abiRahmen = true := by
  decide

/-- Callee-save index 9 names frame slot 19. -/
theorem abi_idx19 : abiBelegung.gerettetIdx 9 = 19 := by
  decide

/-- Frame slot 19 is the word below the witness stack top. -/
theorem abi_slot_unten :
    abiRahmen.schlitzAddr (abiBelegung.gerettetIdx 9) =
      zeugS.register Register.rsp - BitVec.ofNat 64 8 := by
  decide

/-- The witness red zone sits inside the witness frame. -/
theorem abi_rotzone : rotZoneImRahmen zeugS abiRahmen = true := by
  decide

/-- The witness call site is aligned. -/
theorem abi_ausgerichtet : rufAlignOk zeugS = true := by
  decide

/-! ## Closing step: frame slots meet unwind restoration under the ABI. -/

/-- STACK-TO-ABI CLOSING: a callee-save slot that names the word below the
    top (`hslot`) carries the saved register through an actual push/pop pair:
    the unwind restores the pointer and delivers the value, the frame slot
    reads the same value back on both paths, and alignment, frame membership
    and the red zone hold after the composed step. Every premise is consumed:
    `hpasst`/`hi` bound the slot, `hslot` bridges the frame address to the
    machine store, `hsave`/`hles` feed both round-trips, `hok1`--`hdst` feed
    the unwind, `hali` transfers alignment, `hrot` transfers membership and
    the red zone. -/
theorem ComposeStackAbi_verbindung
    (s s1 s2 : Zustand) (r : Rahmen) (b : Belegung)
    (src dst : Register) (d1 d2 : Decodiert) (m : Speicher) (v : Wort)
    (i : Nat)
    (hpasst : Belegung.passt b r = true)
    (hi : i < b.gerettet)
    (hslot : r.schlitzAddr (b.gerettetIdx i) =
      s.register Register.rsp - BitVec.ofNat 64 8)
    (hsave : sichereWort s.speicher r (b.gerettetIdx i) (s.register src) =
      some m)
    (hles : lesbar8 s.speicher (r.schlitzAddr (b.gerettetIdx i)) = true)
    (hok1 : laengeOk d1.laenge = true)
    (hbef1 : d1.befehl = .push64 src)
    (hstep1 : schritt d1 s = some s1)
    (hrd : read64 s1.speicher (s1.register Register.rsp) = some v)
    (hstep2 : schritt d2 s1 = some s2)
    (hok2 : laengeOk d2.laenge = true)
    (hbef2 : d2.befehl = .pop64 dst)
    (hdst : dst ≠ Register.rsp)
    (hali : rufAlignOk s = true)
    (hrot : rotZoneImRahmen s r = true) :
    s2.register Register.rsp = s.register Register.rsp ∧
      s2.register dst = s.register src ∧
      ladeWort m r (b.gerettetIdx i) = some (s.register src) ∧
      ladeWort m r (b.gerettetIdx i) = some (s2.register dst) ∧
      rufAlignOk s2 = true ∧
      rspImRahmen s2 r = true ∧
      rotZoneImRahmen s2 r = true := by
  have hslotb : b.gerettetIdx i < r.schlitzZahl :=
    belegung_gerettet_schranke b r i hi hpasst
  have hwr64 : write64 s.speicher (r.schlitzAddr (b.gerettetIdx i))
      (s.register src) = some m := by
    unfold sichereWort at hsave
    rw [if_pos hslotb] at hsave
    exact hsave
  have hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = some m := by
    rw [← hslot]
    exact hwr64
  have hles64 : lesbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = true := by
    rw [← hslot]
    exact hles
  have hwind := push_pop_wiederhergestellt s s1 s2 src dst d1 d2 m v
    hok1 hbef1 hwr hles64 hstep1 hrd hstep2 hok2 hbef2 hdst
  obtain ⟨hrsp, hval⟩ := hwind
  have hframe : ladeWort m r (b.gerettetIdx i) = some (s.register src) :=
    sichere_lade_rundreise s.speicher m r (b.gerettetIdx i) (s.register src)
      hslotb hsave hles
  have hagree : ladeWort m r (b.gerettetIdx i) = some (s2.register dst) := by
    rw [hval]
    exact hframe
  have hali2 : rufAlignOk s2 = true := by
    unfold rufAlignOk
    rw [hrsp]
    exact hali
  have hrot2 : rotZoneImRahmen s2 r = true := by
    unfold rotZoneImRahmen
    rw [hrsp]
    exact hrot
  have hconj := of_decide_eq_true hrot
  obtain ⟨hlo, hhi⟩ := hconj
  have hrahmen : rspImRahmen s2 r = true := by
    unfold rspImRahmen
    rw [hrsp, decide_eq_true_eq]
    exact ⟨by omega, hhi⟩
  exact ⟨hrsp, hval, hframe, hagree, hali2, hrahmen, hrot2⟩

/-! ## Joint witness: every premise holds on a memory-changing run. -/

/-- JOINT WITNESS for `ComposeStackAbi_verbindung`: every premise holds
    jointly on the shared push/pop witness -- the frame save observably
    changes memory (zero becomes 42 below the old top), the reached `lauf`
    run chains push and pop, and the misaligned twin is refused. -/
theorem ComposeStackAbi_verbindung_zeuge :
    ∃ (s s1 s2 : Zustand) (r : Rahmen) (b : Belegung)
      (src dst : Register) (d1 d2 : Decodiert) (m : Speicher) (v : Wort)
      (i : Nat),
      Belegung.passt b r = true ∧
      i < b.gerettet ∧
      r.schlitzAddr (b.gerettetIdx i) =
        s.register Register.rsp - BitVec.ofNat 64 8 ∧
      sichereWort s.speicher r (b.gerettetIdx i) (s.register src) =
        some m ∧
      lesbar8 s.speicher (r.schlitzAddr (b.gerettetIdx i)) = true ∧
      laengeOk d1.laenge = true ∧
      d1.befehl = .push64 src ∧
      schritt d1 s = some s1 ∧
      read64 s1.speicher (s1.register Register.rsp) = some v ∧
      schritt d2 s1 = some s2 ∧
      laengeOk d2.laenge = true ∧
      d2.befehl = .pop64 dst ∧
      dst ≠ Register.rsp ∧
      rufAlignOk s = true ∧
      rotZoneImRahmen s r = true ∧
      s.speicher.bytes (r.schlitzAddr (b.gerettetIdx i)) ≠
        m.bytes (r.schlitzAddr (b.gerettetIdx i)) ∧
      lauf [d1, d2] s = some s2 := by
  have hb19 : abiBelegung.gerettetIdx 9 < abiRahmen.schlitzZahl := by
    decide
  have emem : zeugS.speicher = zeugSpeicherRW := rfl
  have eob : zeugS.register Register.rsp - BitVec.ofNat 64 8 = zeugOben :=
    rfl
  have ereg : zeugS.register Register.rax = 42 := by
    decide
  have hsave9 :
      sichereWort zeugS.speicher abiRahmen (abiBelegung.gerettetIdx 9)
        (zeugS.register Register.rax) = some zeugM1 := by
    unfold sichereWort
    rw [if_pos hb19, abi_slot_unten, ereg, emem]
    exact zeug_push_schreibt
  have hles9 :
      lesbar8 zeugS.speicher
        (abiRahmen.schlitzAddr (abiBelegung.gerettetIdx 9)) = true := by
    rw [abi_slot_unten, emem]
    exact zeugOben_lesbar
  have hok1w :
      laengeOk (⟨Befehl.push64 Register.rax, 1⟩ : Decodiert).laenge =
        true := by
    decide
  have hwr0 :
      write64 zeugS.speicher
        (zeugS.register Register.rsp - BitVec.ofNat 64 8)
        (zeugS.register Register.rax) = some zeugM1 := by
    rw [emem, eob, ereg]
    exact zeug_push_schreibt
  have hstep1w :
      schritt (⟨Befehl.push64 Register.rax, 1⟩ : Decodiert) zeugS =
        some zeugS1 :=
    schritt_push64_erfolg _ _ _ _ hok1w rfl hwr0
  have hok2w :
      laengeOk (⟨Befehl.pop64 Register.rbx, 1⟩ : Decodiert).laenge =
        true := by
    decide
  have hdstw : Register.rbx ≠ Register.rsp := by
    decide
  have hstep2w :
      schritt (⟨Befehl.pop64 Register.rbx, 1⟩ : Decodiert) zeugS1 =
        some zeugS2 :=
    schritt_pop64_reg _ _ _ _ hok2w rfl hdstw zeug_push_liest
  have hi9 : 9 < abiBelegung.gerettet := by
    decide
  have hhit :=
    writeBytesN_hit zeugSpeicherRW zeugOben 42 8 0 (by decide) (by decide)
  rw [addrOff_null] at hhit
  have hmem :
      zeugS.speicher.bytes
        (abiRahmen.schlitzAddr (abiBelegung.gerettetIdx 9)) ≠
        zeugM1.bytes
          (abiRahmen.schlitzAddr (abiBelegung.gerettetIdx 9)) := by
    rw [abi_slot_unten, emem]
    show BitVec.ofNat 8 0 ≠ writeBytes zeugSpeicherRW zeugOben 42 zeugOben
    unfold writeBytes
    rw [hhit]
    decide
  have hlauf :
      lauf [⟨Befehl.push64 Register.rax, 1⟩,
        ⟨Befehl.pop64 Register.rbx, 1⟩] zeugS = some zeugS2 := by
    simp only [lauf, hstep1w, hstep2w]
  exact ⟨zeugS, zeugS1, zeugS2, abiRahmen, abiBelegung, Register.rax,
    Register.rbx, ⟨Befehl.push64 Register.rax, 1⟩,
    ⟨Befehl.pop64 Register.rbx, 1⟩, zeugM1, 42, 9,
    abi_passt, hi9, abi_slot_unten, hsave9, hles9, hok1w, rfl, hstep1w,
    zeug_push_liest, hstep2w, hok2w, rfl, hdstw, abi_ausgerichtet,
    abi_rotzone, hmem, hlauf⟩

/-! ## Planted refusals: loud frame and alignment gates. -/

/-- Planted refusal: a slot past the witness frame saves nothing. -/
theorem abi_slot_verweigert (v : Wort) :
    sichereWort zeugS.speicher abiRahmen 20 v = none :=
  sichereWort_ausserhalb _ _ _ _ (by decide)

/-- Planted refusal: a misaligned call site is refused loudly. -/
theorem abi_fehlalign_verweigert :
    callGeprueft ⟨.call32 alignDisp, 5⟩ alignSmis = none :=
  callGeprueft_fehlalign _ _ _ rfl alignSmis_fehlalign

/- CUTS:
    Proved here (all over the REUSED canonical `Zustand`/`Speicher`
    vocabulary and the accepted `Stapel`, `StackUnwind` and `CallAlign16`
    theorems -- no new machine, no new decoder row, no source claim):
    - red-zone rule `rotZoneImRahmen`: the 128 bytes below `rsp` lie
      inside the frame extent;
    - closing step `ComposeStackAbi_verbindung`: the callee-save slot that
      names the word below the top carries the saved register through an
      actual push/pop pair (pointer restoration and value delivery from
      `push_pop_wiederhergestellt`, slot read-back from
      `sichere_lade_rundreise` over `belegung_gerettet_schranke`), with
      unwind/frame agreement on both paths and alignment, membership and
      red-zone transfer;
    - joint witness `ComposeStackAbi_verbindung_zeuge`: every premise
      holds jointly on a non-degenerate reached `lauf` run whose frame
      save observably changes memory (zero becomes 42);
    - planted refusals `abi_slot_verweigert` (bounds) and
      `abi_fehlalign_verweigert` (misaligned call gate).
    NOT proved here, and not claimed:
    - The call/ret plus alignment leg stays with its producer
      `CallAlign16_verbindung`; the fetched nested leg stays with
      `geholt_verschachtelt_wiederhergestellt` (lane 569). Neither is
      re-proved or duplicated here.
    - No TSO/store-buffer/forwarding/GX bridge: every fact is sequential
      over one canonical `Speicher`; per-access granularity and the GX
      refinement stay with the TSO-bridge lanes.
    - No source correspondence: nothing here claims the slots carry any
      source value, contract or duty.
    - System V leaf/async-signal red-zone clobber semantics beyond the
      checked 128-byte in-frame rule stays OPEN.
    - No loader, entry, relocation, cost/time transfer or final-image
      acceptance claim.
    - No new hardware or software assumptions: the only gates are the
      accepted execute/read/write permissions of the consumed slots.
-/

#print axioms rotZoneImRahmen
#print axioms abi_passt
#print axioms abi_idx19
#print axioms abi_slot_unten
#print axioms abi_rotzone
#print axioms abi_ausgerichtet
#print axioms ComposeStackAbi_verbindung
#print axioms ComposeStackAbi_verbindung_zeuge
#print axioms abi_slot_verweigert
#print axioms abi_fehlalign_verweigert

end Gabbro.Grammatik.X86
