/-
  File:      Grammatik/X86/HwLockFetch.lean
  Subject:   LOCK family on the coherent machine: fetched-byte dispatch,
             narrower widths and other addressing modes as stated
             refusals, split-lock (cache-line crossing) as refusal.

  Lane 1209: follow-up of lane 1119 (`HwLockRmw.lean`). The 1119 plug
  takes a PARSED `LockAnweisung`; fetch stays with the single-core
  662 `lockByteschritt`. This module adds fetched-byte dispatch ON
  `HwMaschine` (decode from the core's fetched window, execute
  permission, `ExtendedExecution` discipline via 662 `decodeLockExt`),
  the SIB addressing mode 662 accepts, and split-lock refusal.
  Narrower widths (8/16/32-bit) and non-mod=2 modes have no 662 row:
  they are refused here at the decoder, never executed.
  The old evaluators are lifted, never redefined.
-/
import Grammatik.X86.Hw.Familien.HwLockRmw

namespace Gabbro.Grammatik.X86

/-- Fetched decode on the coherent machine: the 662 `lockFetch` on the
    core projection (actual executable bytes at the core RIP, combined
    decoder, length and execute-permission checks). -/
def hwLockFetch (m : HwMaschine) (c : Nat) :
    Option (LockAnweisung × List Byte) :=
  lockFetch (lockMaschineVonHw m c)

/-- The coherent fetch IS the 662 fetch on the projection: no second
    fetch model. -/
theorem hwLockFetch_aus_projektion (m : HwMaschine) (c : Nat) :
    hwLockFetch m c = lockFetch (lockMaschineVonHw m c) := rfl

/-! ## 2. Split-lock guard and the fetched step.

  A locked word crossing a cache line is a split lock (Intel SDM
  Vol. 3A 9.1.1: split locks may take a bus lock; with alignment
  checking they fault). This layer performs no bus transaction and
  claims no #AC control state, so the crossing shape is a stated
  admission refusal (`none`), never a fault claim. Line size 64 is a
  named silicon assumption (see CUTS). -/

/-- Cache-line size of the selected profile: 64 bytes (named silicon
    assumption). -/
def cacheLinie : Nat := 64

/-- Split-lock guard: true exactly when the 8-byte word at `tgt`
    meets two 64-byte lines. -/
def splitSperre (tgt : Adresse) : Bool :=
  decide ((tgt.toNat / cacheLinie) ≠ ((tgt.toNat + 7) / cacheLinie))

/-- The word footprint of a locked form on the coherent machine, if
    the form touches memory. -/
def lockFuss (m : HwMaschine) (c : Nat) : LockForm → Option Adresse
  | .xadd64 _ base d => some (effAddr (projZustand m c) base d)
  | .cmpxchg64 _ base d => some (effAddr (projZustand m c) base d)
  | .mfence => none

/-- One fetched LOCK step on the coherent machine: fetch from the
    core window, refuse parsed #UD, refuse split-lock words, admit
    the rest through the 1119 parsed plug. Takes only the machine:
    no caller-supplied decoded value ever becomes a trusted fetch. -/
def hwLockFetchSchritt (m : HwMaschine) (c : Nat) : Option HwMaschine :=
  match hwLockFetch m c with
  | none => none
  | some (a, _) =>
    match a with
    | .ud _ _ => none
    | .ok f _ =>
      match lockFuss m c f with
      | some tgt =>
        match splitSperre tgt with
        | true => none
        | false => hwLockSchritt m c a
      | none => hwLockSchritt m c a

/-- The fetched LOCK producer plug over `Unit`: the fetch decides,
    never the caller. -/
def adapterLockFetch : HwAdapter Unit :=
  ⟨fun m c _ => hwLockFetchSchritt m c⟩

/-! ## 3. Fetched-step equations and well-formedness.

  The fetched step is the parsed 1119 plug step wherever the fetch
  admits a non-split form; every other shape refuses. -/

/-- Fetch refusal refuses the fetched step. -/
theorem hwLockFetchSchritt_ohne_fetch (m : HwMaschine) (c : Nat)
    (h : hwLockFetch m c = none) :
    hwLockFetchSchritt m c = none := by
  unfold hwLockFetchSchritt
  simp only [h]

/-- A fetched parsed #UD never executes. -/
theorem hwLockFetchSchritt_ud (m : HwMaschine) (c : Nat) (g : LockUdGrund)
    (len : Nat) (rest : List Byte)
    (h : hwLockFetch m c = some (.ud g len, rest)) :
    hwLockFetchSchritt m c = none := by
  unfold hwLockFetchSchritt
  simp only [h]

/-- Split-lock words refuse the fetched step (stated admission
    refusal, never a fault claim). -/
theorem hwLockFetchSchritt_split (m : HwMaschine) (c : Nat)
    (f : LockForm) (len : Nat) (rest : List Byte)
    (h : hwLockFetch m c = some (.ok f len, rest))
    (tgt : Adresse) (hff : lockFuss m c f = some tgt)
    (hs : splitSperre tgt = true) :
    hwLockFetchSchritt m c = none := by
  unfold hwLockFetchSchritt
  simp only [h, hff, hs]

/-- Without split, the fetched step is exactly the parsed plug step
    on the fetched instruction. -/
theorem hwLockFetchSchritt_ohne_split (m : HwMaschine) (c : Nat)
    (f : LockForm) (len : Nat) (rest : List Byte)
    (h : hwLockFetch m c = some (.ok f len, rest))
    (hs : match lockFuss m c f with
      | some tgt => splitSperre tgt = false
      | none => True) :
    hwLockFetchSchritt m c = hwLockSchritt m c (.ok f len) := by
  unfold hwLockFetchSchritt
  cases hff : lockFuss m c f with
  | none =>
    simp only [h, hff]
  | some tgt =>
    have hs2 : splitSperre tgt = false := by
      simp only [hff] at hs
      exact hs
    simp only [h, hff, hs2]

/-- Every fetched successor preserves well-formedness: profiles are
    untouched (the 1119 re-embedding), so admission still has silicon
    behind it. -/
theorem adapterLockFetch_wf (m : HwMaschine) (c : Nat) (u : Unit)
    (m' : HwMaschine)
    (h : adapterLockFetch.schritt m c u = some m') (hwf : HwWf m) :
    HwWf m' := by
  have h2 : hwLockFetchSchritt m c = some m' := h
  cases hf : hwLockFetch m c with
  | none =>
    rw [hwLockFetchSchritt_ohne_fetch m c hf] at h2
    cases h2
  | some pr =>
    cases pr with
    | mk a rest =>
      cases a with
      | ud g len =>
        rw [hwLockFetchSchritt_ud m c g len rest hf] at h2
        cases h2
      | ok f len =>
        cases hff : lockFuss m c f with
        | none =>
          rw [hwLockFetchSchritt_ohne_split m c f len rest hf
            (by simp only [hff])] at h2
          exact adapterLockRmw_wf m c _ m' h2 hwf
        | some tgt =>
          by_cases hs : splitSperre tgt = true
          · rw [hwLockFetchSchritt_split m c f len rest hf tgt hff hs] at h2
            cases h2
          · rw [hwLockFetchSchritt_ohne_split m c f len rest hf
              (by simp only [hff]; simpa using hs)] at h2
            exact adapterLockRmw_wf m c _ m' h2 hwf

/-! ## 4. ExtendedExecution discipline and the single-core bridge.

  The 662 combined decoder tries the accepted `decodeExt` first, so
  every older row keeps its bytes: where the unified dispatcher
  accepts, the coherent LOCK fetch refuses. And every admitted
  fetched step rides the single-core 662 `lockByteschritt` outcome. -/

/-- Where the unified dispatcher accepts, the coherent LOCK fetch
    refuses: older rows keep their bytes (`decodeExt` first by
    construction, never shadowed). -/
theorem hwLockFetch_weicht_aelter (m : HwMaschine) (c : Nat)
    (e : ExtInstr) (rest : List Byte)
    (h : decodeExt (geholt (projZustand m c)) = some (e, rest)) :
    hwLockFetch m c = none := by
  unfold hwLockFetch
  have hde : decodeLockExt (geholt (lockMaschineVonHw m c).zu) = none :=
    decodeLockExt_aelter _ e rest h
  unfold lockFetch
  rw [hde]

/-- A parsed-plug successor is a single-core fetched `.ok`: the
    fetched instruction runs `lockSchrittVoll` on the same projection
    with the same profiles. -/
theorem hwLockSchritt_trifft_byteschritt (m : HwMaschine) (c : Nat)
    (a : LockAnweisung) (rest : List Byte) (m' : HwMaschine)
    (hf : hwLockFetch m c = some (a, rest))
    (h : hwLockSchritt m c a = some m') :
    lockArt (lockByteschritt (lockMaschineVonHw m c) c m.hw
      (m.bereit c)) = .ok := by
  have hfe : lockFetch (lockMaschineVonHw m c) = some (a, rest) := hf
  have e1 : lockByteschritt (lockMaschineVonHw m c) c m.hw (m.bereit c)
      = lockSchrittVoll a c (lockMaschineVonHw m c) m.hw (m.bereit c) := by
    unfold lockByteschritt
    simp only [hfe]
  unfold hwLockSchritt at h
  cases h1 : lockSchrittVoll a c (lockMaschineVonHw m c) m.hw
    (m.bereit c) with
  | ok lm ev =>
    rw [e1, h1]
    rfl
  | speicherFehler => rw [h1] at h; cases h
  | udFehler g => rw [h1] at h; cases h
  | verweigert => rw [h1] at h; cases h

/-- Every admitted fetched step is a single-core fetched `.ok` on the
    same projection: fetch consistency across the two machines. -/
theorem hwLockFetchSchritt_trifft_lockByteschritt (m : HwMaschine)
    (c : Nat) (m' : HwMaschine)
    (h : hwLockFetchSchritt m c = some m') :
    lockArt (lockByteschritt (lockMaschineVonHw m c) c m.hw
      (m.bereit c)) = .ok := by
  cases hf : hwLockFetch m c with
  | none =>
    rw [hwLockFetchSchritt_ohne_fetch m c hf] at h
    cases h
  | some pr =>
    cases pr with
    | mk a rest =>
      cases a with
      | ud g len =>
        rw [hwLockFetchSchritt_ud m c g len rest hf] at h
        cases h
      | ok f len =>
        cases hff : lockFuss m c f with
        | none =>
          rw [hwLockFetchSchritt_ohne_split m c f len rest hf
            (by simp only [hff])] at h
          exact hwLockSchritt_trifft_byteschritt m c _ rest m' hf h
        | some tgt =>
          by_cases hs : splitSperre tgt = true
          · rw [hwLockFetchSchritt_split m c f len rest hf tgt hff hs] at h
            cases h
          · rw [hwLockFetchSchritt_ohne_split m c f len rest hf
              (by simp only [hff]; simpa using hs)] at h
            exact hwLockSchritt_trifft_byteschritt m c _ rest m' hf h

/-! ## 5. Closed pins: split-lock and the aligned baseline.

  The witness word 8192 sits at a line start (no split); the split
  machine aims at 8188, whose 8-byte footprint meets lines 127
  and 128. -/

/-- Split-machine registers: delta 5 in rax, base 8188 in rbp. -/
def hwLockFetchSplitReg : Register → Wort := lockZeugReg 5 8188 7

/-- Split-machine data window: 8184..8200, covering the crossing word. -/
def fetchSplitData (a : Adresse) : Bool :=
  decide (8184 ≤ a.toNat ∧ a.toNat < 8200)

/-- Split machine: LOCK XADD bytes at 4096, crossing word at 8188. -/
def hwLockFetchSplit : HwMaschine :=
  ⟨lockZeugSpeicher pinXadd 10 lockCodeExec fetchSplitData fetchSplitData,
    hwLockWitKernLesen hwLockFetchSplitReg, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- The split word really crosses a line: 8188 + 7 reaches line 128. -/
theorem hwLockFetchWit_split_wahr :
    splitSperre (BitVec.ofNat 64 8188) = true := by
  decide

/-- The aligned witness word never splits. -/
theorem hwLockFetchWit_kein_split :
    splitSperre (BitVec.ofNat 64 8192) = false := by
  decide

/-- Fetch on the split machine: the 9-byte word form with a 6-byte
    zero suffix. -/
theorem hwLockFetchWit_split_fetch :
    hwLockFetch hwLockFetchSplit 0 =
      some (.ok (.xadd64 .rax .rbp 0) 9,
        List.replicate 6 (BitVec.ofNat 8 0)) := by
  decide

/-- The split footprint pins to 8188. -/
theorem hwLockFetchWit_split_fuss :
    lockFuss hwLockFetchSplit 0 (.xadd64 .rax .rbp 0) =
      some (BitVec.ofNat 64 8188) := by
  decide

/-- Split-lock refuses the fetched step, although the parsed plug
    would admit the same bytes: the fetched path is stricter. -/
theorem hwLockFetchWit_split :
    hwLockFetchSchritt hwLockFetchSplit 0 = none :=
  hwLockFetchSchritt_split _ _ _ _ _ hwLockFetchWit_split_fetch
    _ hwLockFetchWit_split_fuss hwLockFetchWit_split_wahr

/-! ## 6. Narrower widths and other addressing modes: refused.

  662 models only the 64-bit word rows (REX.W) in mod=2
  base-plus-disp32. A 32-bit XADD without REX.W, a 16-bit shape with
  the operand-size prefix, and a mod=0 disp32-only shape have no 662
  row: the fetched path refuses them at the decoder, never executing
  a truncated or mis-decoded form. The SIB shape 662 accepts
  (base with low bits 4) dispatches and runs. -/

/-- 32-bit XADD bytes: LOCK prefix but no REX.W. -/
def pinXadd32 : List Byte :=
  [natByte 240, natByte 15, natByte 193, natByte 133,
   natByte 0, natByte 0, natByte 0, natByte 0]

/-- mod=0 shape: disp32 without base register. -/
def pinXaddMod0 : List Byte :=
  [natByte 240, natByte 72, natByte 15, natByte 193, natByte 5,
   natByte 0, natByte 0, natByte 0, natByte 0]

/-- 16-bit shape: operand-size prefix before LOCK. -/
def pinXadd16 : List Byte :=
  [natByte 102, natByte 240, natByte 72, natByte 15, natByte 193,
   natByte 133, natByte 0, natByte 0, natByte 0, natByte 0]

/-- Machine over given code bytes: word 10, delta 5, base 8192. -/
def hwLockFetchCode (prog : List Byte) : HwMaschine :=
  ⟨lockZeugSpeicher prog 10 lockCodeExec lockDataRW lockDataRW,
    hwLockWitKernLesen hwLockWitReg0, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- The 32-bit shape has no fetched decode. -/
theorem hwLockFetchWit_schmal32 :
    hwLockFetch (hwLockFetchCode pinXadd32) 0 = none := by
  decide

/-- The mod=0 shape has no fetched decode. -/
theorem hwLockFetchWit_mod0 :
    hwLockFetch (hwLockFetchCode pinXaddMod0) 0 = none := by
  decide

/-- The 16-bit shape has no fetched decode. -/
theorem hwLockFetchWit_schmal16 :
    hwLockFetch (hwLockFetchCode pinXadd16) 0 = none := by
  decide

/-- The refused decodes refuse the fetched step. -/
theorem hwLockFetchWit_schmal32_schritt :
    hwLockFetchSchritt (hwLockFetchCode pinXadd32) 0 = none :=
  hwLockFetchSchritt_ohne_fetch _ _ hwLockFetchWit_schmal32

/-- The refused mod=0 decode refuses the fetched step. -/
theorem hwLockFetchWit_mod0_schritt :
    hwLockFetchSchritt (hwLockFetchCode pinXaddMod0) 0 = none :=
  hwLockFetchSchritt_ohne_fetch _ _ hwLockFetchWit_mod0

/-- SIB registers: delta 5 in rax, base 8192 in rsp. -/
def hwLockFetchSibReg : Register → Wort := fun q =>
  if q = .rax then 5
  else if q = .rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- SIB machine: the 10-byte SIB XADD at 4096 over word 10. -/
def hwLockFetchSib : HwMaschine :=
  ⟨lockZeugSpeicher (encodeLock (.xadd64 .rax .rsp 0)) 10 lockCodeExec
      lockDataRW lockDataRW,
    hwLockWitKernLesen hwLockFetchSibReg, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- Fetch on the SIB machine: the 10-byte form with a 5-byte suffix. -/
theorem hwLockFetchWit_sib_fetch :
    hwLockFetch hwLockFetchSib 0 =
      some (.ok (.xadd64 .rax .rsp 0) 10,
        List.replicate 5 (BitVec.ofNat 8 0)) := by
  decide

/-- The fetched SIB step moves the word 10 to 15. -/
theorem hwLockFetchWit_sib_wort :
    hwLockWort (BitVec.ofNat 64 8192)
      (hwLockFetchSchritt hwLockFetchSib 0) = some 15 := by
  decide

/-! ## 7. The fetched two-core run and its refusals.

  Core 0 fetched-adds 5 (word 10 to 15) on the 1119 witness start;
  the fetched step equals the parsed plug step, so words, registers,
  buffers and TSO views transfer by rewriting. Core 1 fetched-adds
  7 after the drain (word 15 to 22). The fence, the pending own
  store, #UD shapes, missing SSE2, unreadable words and misaligned
  bases refuse on the fetched path exactly as on the parsed plug. -/

/-- Fetch on the witness start: the 9-byte word form. -/
theorem hwLockFetchWit_start0 :
    hwLockFetch hwLockWitStart 0 =
      some (.ok (.xadd64 .rax .rbp 0) 9,
        List.replicate 6 (BitVec.ofNat 8 0)) := by
  decide

/-- The witness footprint pins to the aligned word 8192. -/
theorem hwLockFetchWit_start_fuss :
    lockFuss hwLockWitStart 0 (.xadd64 .rax .rbp 0) =
      some (BitVec.ofNat 64 8192) := by
  decide

/-- The fetched core-0 step is the parsed plug step. -/
theorem hwLockFetchWit_nach1 :
    hwLockFetchSchritt hwLockWitStart 0 = hwLockWitNach1 :=
  hwLockFetchSchritt_ohne_split _ _ _ _ _ hwLockFetchWit_start0 (by
    simp only [hwLockFetchWit_start_fuss, hwLockFetchWit_kein_split])

/-- Fetched step one moves the word 10 to 15. -/
theorem hwLockFetchWit_nach1_wort :
    hwLockWort hwLockWitAdr (hwLockFetchSchritt hwLockWitStart 0) =
      some 15 := by
  rw [hwLockFetchWit_nach1]
  exact hwLockWit_nach1_wort

/-- Fetched step one returns the old word through rax. -/
theorem hwLockFetchWit_nach1_rax :
    hwLockReg 0 .rax (hwLockFetchSchritt hwLockWitStart 0) = some 10 := by
  rw [hwLockFetchWit_nach1]
  exact hwLockWit_nach1_rax

/-- Fetched step one keeps the foreign pending byte. -/
theorem hwLockFetchWit_nach1_fremd_buf :
    hwLockBuf 1 (hwLockFetchSchritt hwLockWitStart 0) = some 1 := by
  rw [hwLockFetchWit_nach1]
  exact hwLockWit_nach1_fremd_buf

/-- Owner-only forwarding through the fetched step. -/
theorem hwLockFetchWit_nach1_sicht :
    hwLockSicht (hwLockFetchSchritt hwLockWitStart 0) 1
        hwLockWitFremdAdr =
        some (some (BitVec.ofNat 8 99)) ∧
      hwLockSicht (hwLockFetchSchritt hwLockWitStart 0) 0
        hwLockWitFremdAdr =
        some (some (BitVec.ofNat 8 0)) := by
  rw [hwLockFetchWit_nach1]
  exact ⟨hwLockWit_nach1_eigen_sicht, hwLockWit_nach1_fremd_sicht⟩

/-- After the drain, the fetched core-1 step moves 15 to 22. -/
theorem hwLockFetchWit_nach2_wort :
    hwLockWort hwLockWitAdr
      (match hwLockWitBereit2 with
        | some m2 => hwLockFetchSchritt m2 1
        | none => none) = some 22 := by
  decide

/-- After the drain, the fetched core-1 step returns 15 via rax. -/
theorem hwLockFetchWit_nach2_rax1 :
    hwLockReg 1 .rax
      (match hwLockWitBereit2 with
        | some m2 => hwLockFetchSchritt m2 1
        | none => none) = some 15 := by
  decide

/-- The pending own byte refuses core 1 its fetched step. -/
theorem hwLockFetchWit_puffer :
    hwLockFetchSchritt hwLockWitStart 1 = none := by
  have hf : hwLockFetch hwLockWitStart 1 =
      some (.ok (.xadd64 .rax .rbp 0) 9,
        List.replicate 6 (BitVec.ofNat 8 0)) := by
    decide
  have hff : lockFuss hwLockWitStart 1 (.xadd64 .rax .rbp 0) =
      some (BitVec.ofNat 64 8192) := by
    decide
  have hplug : hwLockSchritt hwLockWitStart 1
      (.ok (.xadd64 .rax .rbp 0) 9) = none :=
    hwLock_puffer_bleibt_verweigert hwLockWitStart 1 .rax .rbp 0 9
      ⟨hwLockWitFremdAdr, BitVec.ofNat 8 99⟩ [] (by decide) (by decide)
  have hs : match lockFuss hwLockWitStart 1 (.xadd64 .rax .rbp 0) with
      | some tgt => splitSperre tgt = false
      | none => True := by
    simp only [hff, hwLockFetchWit_kein_split]
  rw [hwLockFetchSchritt_ohne_split _ _ _ _ _ hf hs, hplug]

/-- Fetched LOCK on a register destination stays refused. -/
theorem hwLockFetchWit_reg_ud :
    hwLockFetchSchritt
      (hwLockFetchCode pinRegUd) 0 = none := by
  have hf : hwLockFetch (hwLockFetchCode pinRegUd) 0 =
      some (.ud .lockAufRegister 5,
        List.replicate 10 (BitVec.ofNat 8 0)) := by
    decide
  exact hwLockFetchSchritt_ud _ _ _ _ _ hf

/-- Fence machine: MFENCE bytes at 4096, empty buffers. -/
def hwLockFetchZaun : HwMaschine :=
  ⟨lockZeugSpeicher pinMfence 0 lockCodeExec lockDataRW lockDataRW,
    hwLockWitKernLesen hwLockWitReg0, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- The fetched fence advances RIP past its 3 bytes. -/
theorem hwLockFetchWit_zaun_rip :
    hwLockRip 0 (hwLockFetchSchritt hwLockFetchZaun 0) =
      some (BitVec.ofNat 64 4099) := by
  decide

/-- The fence without admitted SSE2 refuses on the fetched path. -/
theorem hwLockFetchWit_sse2 :
    hwLockFetchSchritt hwLockWitOhneSse2 0 = none := by
  have hf : hwLockFetch hwLockWitOhneSse2 0 =
      some (.ok .mfence 3, List.replicate 12 (BitVec.ofNat 8 0)) := by
    decide
  have hff : lockFuss hwLockWitOhneSse2 0 .mfence = none := rfl
  have hplug : hwLockSchritt hwLockWitOhneSse2 0 (.ok .mfence 3) = none :=
    hwLock_mfence_ohne_sse2_verweigert hwLockWitOhneSse2 0 3
      (by decide) (by decide)
  have hs : match lockFuss hwLockWitOhneSse2 0 .mfence with
      | some tgt => splitSperre tgt = false
      | none => True := by
    simp only [hff]
  rw [hwLockFetchSchritt_ohne_split _ _ _ _ _ hf hs, hplug]

/-- The unreadable word refuses on the fetched path. -/
theorem hwLockFetchWit_lesefehler :
    hwLockFetchSchritt hwLockWitOhneLesen 0 = none := by
  have hf : hwLockFetch hwLockWitOhneLesen 0 =
      some (.ok (.xadd64 .rax .rbp 0) 9,
        List.replicate 6 (BitVec.ofNat 8 0)) := by
    decide
  have hff : lockFuss hwLockWitOhneLesen 0 (.xadd64 .rax .rbp 0) =
      some (BitVec.ofNat 64 8192) := by
    decide
  have hplug : hwLockSchritt hwLockWitOhneLesen 0
      (.ok (.xadd64 .rax .rbp 0) 9) = none := by
    apply hwLockSchritt_verweigert_bei
    rw [hwLockWit_lesefehler_art]
    decide
  have hs : match lockFuss hwLockWitOhneLesen 0 (.xadd64 .rax .rbp 0) with
      | some tgt => splitSperre tgt = false
      | none => True := by
    simp only [hff, hwLockFetchWit_kein_split]
  rw [hwLockFetchSchritt_ohne_split _ _ _ _ _ hf hs, hplug]

/-- The misaligned base refuses on the fetched path (unsupported
    profile, never a fault claim). -/
theorem hwLockFetchWit_unaligned :
    hwLockFetchSchritt hwLockWitUnaligned 0 = none := by
  have hf : hwLockFetch hwLockWitUnaligned 0 =
      some (.ok (.xadd64 .rax .rbp 0) 9,
        List.replicate 6 (BitVec.ofNat 8 0)) := by
    decide
  have hplug : hwLockSchritt hwLockWitUnaligned 0
      (.ok (.xadd64 .rax .rbp 0) 9) = none :=
    hwLock_unaligned_bleibt_verweigert hwLockWitUnaligned 0 .rax .rbp 0 9
      (by decide) (by decide) (by decide)
  -- 8193 stays on line 128: misaligned but never split.
  have hnosplit : splitSperre (BitVec.ofNat 64 8193) = false := by
    decide
  have hff : lockFuss hwLockWitUnaligned 0 (.xadd64 .rax .rbp 0) =
      some (BitVec.ofNat 64 8193) := by
    decide
  have hs : match lockFuss hwLockWitUnaligned 0 (.xadd64 .rax .rbp 0) with
      | some tgt => splitSperre tgt = false
      | none => True := by
    simp only [hff, hnosplit]
  rw [hwLockFetchSchritt_ohne_split _ _ _ _ _ hf hs, hplug]

/-! ## 8. Joint witness: every premise together on reached runs.

  Non-degenerate: core 0 fetched-adds 10 to 15 and core 1
  fetched-adds 15 to 22 in canonical memory (memory-changing steps
  on both cores), a buffered store is forwarded to its owner only,
  the drain lands it in shared memory, the SIB shape runs, and the
  split/narrow/mode/#UD/buffer/SSE2/permission refusals stand beside
  the run. -/

/-- Joint fetched LOCK witness on the coherent machine. -/
theorem hwLockFetch_zeuge :
    hwLockFetch hwLockWitStart 0 =
      some (.ok (.xadd64 .rax .rbp 0) 9,
        List.replicate 6 (BitVec.ofNat 8 0)) ∧
    hwLockWort hwLockWitAdr (hwLockFetchSchritt hwLockWitStart 0) =
      some 15 ∧
    hwLockReg 0 .rax (hwLockFetchSchritt hwLockWitStart 0) = some 10 ∧
    hwLockSicht (hwLockFetchSchritt hwLockWitStart 0) 1
      hwLockWitFremdAdr = some (some (BitVec.ofNat 8 99)) ∧
    hwLockSicht (hwLockFetchSchritt hwLockWitStart 0) 0
      hwLockWitFremdAdr = some (some (BitVec.ofNat 8 0)) ∧
    hwLockWort hwLockWitAdr
      (match hwLockWitBereit2 with
        | some m2 => hwLockFetchSchritt m2 1
        | none => none) = some 22 ∧
    hwLockReg 1 .rax
      (match hwLockWitBereit2 with
        | some m2 => hwLockFetchSchritt m2 1
        | none => none) = some 15 ∧
    HwWf hwLockWitStart ∧
    hwLockWort (BitVec.ofNat 64 8192)
      (hwLockFetchSchritt hwLockFetchSib 0) = some 15 ∧
    hwLockFetchSchritt hwLockFetchSplit 0 = none ∧
    hwLockFetchSchritt (hwLockFetchCode pinXadd32) 0 = none ∧
    hwLockFetchSchritt (hwLockFetchCode pinXaddMod0) 0 = none ∧
    hwLockFetchSchritt hwLockWitStart 1 = none ∧
    hwLockFetchSchritt hwLockWitOhneSse2 0 = none ∧
    hwLockFetchSchritt hwLockWitOhneLesen 0 = none ∧
    hwLockFetchSchritt hwLockWitUnaligned 0 = none := by
  refine ⟨hwLockFetchWit_start0, hwLockFetchWit_nach1_wort,
    hwLockFetchWit_nach1_rax, hwLockFetchWit_nach1_sicht.1,
    hwLockFetchWit_nach1_sicht.2, hwLockFetchWit_nach2_wort,
    hwLockFetchWit_nach2_rax1, hwLockWitStart_wf,
    hwLockFetchWit_sib_wort, hwLockFetchWit_split,
    hwLockFetchWit_schmal32_schritt, hwLockFetchWit_mod0_schritt,
    hwLockFetchWit_puffer, hwLockFetchWit_sse2, hwLockFetchWit_lesefehler,
    hwLockFetchWit_unaligned⟩

/- CUTS:
     Proved here: fetched-byte dispatch for the LOCK family on the
     coherent machine -- `hwLockFetch` as the 662 fetch on the core
     projection (actual executable bytes at the core RIP, combined
     decoder, length and execute-permission checks); the fetched step
     `hwLockFetchSchritt` with the `Unit` producer plug
     `adapterLockFetch` (the fetch decides, never the caller);
     split-lock (8-byte word crossing a 64-byte line) as a stated
     admission refusal, strictly stronger than the parsed 1119 plug;
     narrower widths (8/16/32-bit XADD/CMPXCHG have no 662 row) and
     non-mod=2 addressing modes refused at the decoder, never
     executed; the 662-accepted SIB shape dispatched and run;
     `HwWf` preservation of every fetched successor; exact
     agreement with the parsed plug off-split and with the
     single-core 662 `lockByteschritt` outcome; `ExtendedExecution`
     discipline (older rows keep their bytes); closed fetched pins
     for fetch equations, the two-core run (word 10 to 15 on core 0,
     15 to 22 on core 1 after the drain, owner-only forwarding), the
     fence, and every refusal; the joint non-degenerate witness
     `hwLockFetch_zeuge`.
     Silicon provenance: the LOCK/XADD/CMPXCHG/MFENCE rows are the
     accepted 662 rows (Intel SDM 325462-093US Sep 2026 Vol. 2A
     3-565/3-566, Vol. 2D 6-27/6-28, Vol. 2A 3-193/3-194, Vol. 2B
     4-15) -- this lane adds no new silicon claim beyond reusing
     those rows, except two NAMED ASSUMPTIONS: (i) cache lines are
     64 bytes (`cacheLinie`); (ii) a line-crossing locked word is
     refused admission here (no bus transaction performed, no #AC
     control state claimed, no timing claim).
     NOT proved here, and not claimed:
     - No hardware correspondence beyond self-consistency: encodings,
       flag effects and ordering rules are the accepted 662 rows.
     - No W/GX refinement and no per-access linearisation: the bridge
       owns them. No cycle, latency, progress or retry-bound claim.
     - Narrower widths and further addressing modes (mod=0/1,
       RIP-relative, SIB index/scale, segment overrides) stay open
       with 662; this layer only refuses them, never models them.
     - Unlocked XADD/CMPXCHG and REX-prefixed MFENCE are refused by
       the 662 decoder, not modelled here.
     - No self-modifying-code guard (open with 662).
     - Generic arbitrary-input disjointness beyond the pins: the
       combined decoder tries `decodeExt` first (no shadowing by
       construction); only closed rows are pinned refused/admitted.
     - No source, checker, contract, budget, duty or goal change:
       nothing here speaks about `Vertrag`, `Stmt`, duties or
       `gabbro_ziel`.
-/

#print axioms hwLockFetch_aus_projektion
#print axioms adapterLockFetch_wf
#print axioms hwLockFetchSchritt_ohne_split
#print axioms hwLockFetchSchritt_split
#print axioms hwLockFetch_weicht_aelter
#print axioms hwLockSchritt_trifft_byteschritt
#print axioms hwLockFetchSchritt_trifft_lockByteschritt
#print axioms hwLockFetchWit_nach1_wort
#print axioms hwLockFetchWit_nach2_wort
#print axioms hwLockFetchWit_sib_wort
#print axioms hwLockFetchWit_split
#print axioms hwLockFetchWit_schmal32_schritt
#print axioms hwLockFetch_zeuge

end Gabbro.Grammatik.X86
