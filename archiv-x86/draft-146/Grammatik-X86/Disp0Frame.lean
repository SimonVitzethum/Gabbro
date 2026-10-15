/-
  File:      Grammatik/X86/Disp0Frame.lean
  Subject:   The mod=00 (no-displacement) memory frame over the accepted
             selected address vocabulary.

  Lane 758: disp0 forms (`AdrForm` with `art = .kein`) admitted by the
  accepted `adrOk` (so `rbp`/`r13` never disp0: mod=00 r/m=101 is
  RIP-relative), with the canonical-address check per actual length and
  the SIB byte exactly where the base low code is 4 (`rsp`/`r12`).
  The `rbp`/`r13` base is covered by the disp8=0 escape (mod=01 with a
  zero byte), which computes the same address. All execution goes
  through the accepted fetched steps (`adrStoreSchritt`,
  `leaGeholtSchritt`); no address, register, memory, decoder or source
  model is invented here.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
  - `REFERENCES.json`: Intel SDM combined volumes 1-4, edition
    325462-093US September 2026 (official Intel index; AMD URLs
    returned 404, so no AMD provenance is claimed).
  - ModRM/SIB framing: Intel SDM Vol. 2 Table 2-2 (mod 00/01/10 select
    displacement length; r/m=100 forces a SIB byte; mod=00 r/m=101 is
    disp32/RIP-relative, never `[rbp]`/`[r13]`); SIB scale/index/base
    fields with index 100 meaning absent.
  - Canonical addresses: Vol. 1 Section 3.3.7.1 (bits 63..48 repeat
    bit 47), reused here through the accepted `kanonisch48` /
    `fussZugelassen` checks, not restated.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.AddressEncoding

namespace Gabbro.Grammatik.X86

/-- The disp0 (mod=00) frame: no displacement bytes plus the accepted
    admission (which refuses `rbp`/`r13` without displacement). -/
def disp0Form (f : AdrForm) : Bool :=
  decide (f.art = .kein) && adrOk f

/-- A plain base without displacement is in the frame. -/
theorem disp0Form_basisKein :
    disp0Form (basisKeinForm .rbx) = true := by
  decide

/-! ## 1. disp0 addresses and the SIB rule.

    mod=00 carries no displacement bytes, so the selected address is the
    bare base value. The SIB byte appears exactly where the base low
    code is 4 (`rsp`/`r12`, Intel SDM Vol. 2 Table 2-2 r/m=100); every
    other base encodes without it. -/

/-- A disp0 form computes the bare base value: no displacement added. -/
theorem disp0_adr_base (s : Zustand) (b : Register) (n : Adresse) :
    adrEff s n (basisKeinForm b) = s.register b := by
  simp [adrEff, basisKeinForm, dispWortArt]

/-- SIB exactly where base low code is 4: `rsp` encodes with the SIB. -/
theorem disp0_sib_rsp :
    regLow .rsp = 4 ∧
      encodeAdr .rax (basisKeinForm .rsp) =
        some [rexByte 0 0, modrmByte 0 0 4, sibByte 0 4 4] := by
  decide

/-- The high register with low code 4 (`r12`) needs the SIB too. -/
theorem disp0_sib_r12 :
    regLow .r12 = 4 ∧
      (encodeAdr .rax (basisKeinForm .r12)).map List.length = some 3 := by
  decide

/-- Any other low base encodes SIB-free in two bytes. -/
theorem disp0_ohne_sib_rbx :
    regLow .rbx ≠ 4 ∧
      encodeAdr .rax (basisKeinForm .rbx) =
        some [rexByte 0 0, modrmByte 0 0 (regLow .rbx)] := by
  decide

/-! ## 2. The `rbp`/`r13` corner: mod=00 r/m=101 is RIP-relative.

    Neither `[rbp]` nor `[r13]` has a disp0 encoding (Intel SDM Vol. 2
    Table 2-2: mod=00 r/m=101 names disp32, in 64-bit mode RIP-relative).
    The canonical spelling is mod=01 with a zero displacement byte,
    which computes exactly the bare base value. -/

/-- mod=00 never names `[rbp]`: the frame refuses it. -/
theorem disp0_rbp_verweigert :
    disp0Form (basisKeinForm .rbp) = false := by
  decide

/-- mod=00 never names `[r13]` either. -/
theorem disp0_r13_verweigert :
    disp0Form (basisKeinForm .r13) = false := by
  decide

/-- The `rbp` escape (mod=01 disp8=0) is admitted and computes the bare
    base: no second address model. -/
theorem disp0_rbp_entkommt (s : Zustand) (n : Adresse) :
    adrOk (basisDisp8Form .rbp (natByte 0)) = true ∧
      adrEff s n (basisDisp8Form .rbp (natByte 0)) = s.register .rbp := by
  refine ⟨by decide, ?_⟩
  have h1 : dispWortArt (basisDisp8Form .rbp (natByte 0)) = 0 := by
    simp only [basisDisp8Form, dispWortArt_d8, disp8Wort_null]
  have h2 : adrEff s n (basisDisp8Form .rbp (natByte 0)) =
      s.register .rbp + 0 +
        dispWortArt (basisDisp8Form .rbp (natByte 0)) := rfl
  rw [h2, h1]
  simp

/-- The `r13` escape behaves the same way. -/
theorem disp0_r13_entkommt (s : Zustand) (n : Adresse) :
    adrOk (basisDisp8Form .r13 (natByte 0)) = true ∧
      adrEff s n (basisDisp8Form .r13 (natByte 0)) = s.register .r13 := by
  refine ⟨by decide, ?_⟩
  have h1 : dispWortArt (basisDisp8Form .r13 (natByte 0)) = 0 := by
    simp only [basisDisp8Form, dispWortArt_d8, disp8Wort_null]
  have h2 : adrEff s n (basisDisp8Form .r13 (natByte 0)) =
      s.register .r13 + 0 +
        dispWortArt (basisDisp8Form .r13 (natByte 0)) := rfl
  rw [h2, h1]
  simp

/-! ## 3. Fetched disp0 witness: `mov [rbx], rax` through bytes.

    The image is the canonical three-byte mod=00 store (REX.W, 0x89,
    ModRM mod=00 reg=rax r/m=rbx); the data cell starts at zero and the
    source register carries 42. -/

/-- Witness image: `mov [rbx], rax` (mod=00, no SIB, no displacement). -/
def disp0WitBild : List Byte :=
  [natByte 72, natByte 137, natByte 3]

/-- Witness code bytes: the image at 4096, zeroes elsewhere. -/
def disp0WitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else
    match disp0WitBild[a.toNat - 4096]? with
    | some b => b
    | none => BitVec.ofNat 8 0

/-- Witness execute permission: exactly the three image bytes. -/
def disp0WitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4099)

/-- Witness data permission: sixteen bytes at 8192. -/
def disp0WitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8208)

/-- Witness memory: code is execute-only, data read/write-only. -/
def disp0WitSpeicher : Speicher :=
  { bytes := disp0WitBytes, lesbar := disp0WitDaten,
    schreibbar := disp0WitDaten, ausfuehrbar := disp0WitCode }

/-- Witness registers: `rax = 42`, `rbx = 8192`. -/
def disp0WitReg : Register → Wort
  | .rax => BitVec.ofNat 64 42
  | .rbx => BitVec.ofNat 64 8192
  | .rsp => BitVec.ofNat 64 8704
  | _ => BitVec.ofNat 64 0

/-- Witness start state: code at 4096. -/
def disp0WitZustand : Zustand :=
  { register := disp0WitReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := disp0WitSpeicher }

/-- The image decodes as the disp0 `[rbx]` store of `rax`. -/
theorem disp0Wit_dekodiert :
    decodeStoreIdx disp0WitBild =
      some (.rax, basisKeinForm .rbx, []) := by
  decide

/-- The fetched store lands 42 at `rbx = 8192`. -/
theorem disp0Wit_speichert :
    (adrStoreSchritt disp0WitZustand).map
        (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (BitVec.ofNat 8 42) := by
  decide

/-- The written word reads back whole. -/
theorem disp0Wit_liest :
    (adrStoreSchritt disp0WitZustand).bind
          (fun s => read64 s.speicher (BitVec.ofNat 64 8192)) =
        some (BitVec.ofNat 64 42) := by
  decide

/-- The data cell starts at zero: the run observably changes memory. -/
theorem disp0Wit_vorher_null :
    disp0WitZustand.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0 := by
  decide

/-- The fetched store advances RIP past its three actual bytes. -/
theorem disp0Wit_rip :
    (adrStoreSchritt disp0WitZustand).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4099) := by
  decide

/-- PERMISSION REFUSAL: the same fetched store with dark data memory
    admits no step. -/
theorem disp0Wit_dunkel_verweigert :
    adrStoreSchritt { disp0WitZustand with speicher :=
      { disp0WitSpeicher with schreibbar := fun _ => false } } = none := by
  decide

/-! ## 4. Connection: the disp0 frame reaches memory.

    A disp0 `[rbx]` form at a canonical writable address names the bare
    base, encodes in its two actual tail bytes, admits its eight-byte
    footprint through the accepted check, and the write succeeds. -/

/-- CONNECTION: the disp0 `[rbx]` form reaches its canonical writable
    address with its actual two-byte encoding and an admitted write. -/
theorem Disp0Frame_verbindung (f : AdrForm) (s : Zustand) (n : Adresse)
    (hf : f = basisKeinForm .rbx)
    (hbase : s.register .rbx = BitVec.ofNat 64 8192)
    (hwr : schreibbar8 s.speicher (BitVec.ofNat 64 8192) = true) :
    adrEff s n f = BitVec.ofNat 64 8192 ∧
    (encodeAdr .rax f).map List.length = some 2 ∧
    fussZugelassen s.speicher (adrEff s n f) true = true ∧
    ∃ m', write64 s.speicher (adrEff s n f) (s.register .rax) =
      some m' := by
  have haddr : adrEff s n (basisKeinForm .rbx) = BitVec.ofNat 64 8192 := by
    rw [disp0_adr_base, hbase]
  have hwr' : schreibbar8 s.speicher
      (adrEff s n (basisKeinForm .rbx)) = true := by
    rw [haddr]; exact hwr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf]; exact haddr
  · rw [hf]; exact encodeAdr_laenge_basisKein
  · rw [hf, haddr]
    unfold fussZugelassen
    rw [kanonisch48_8192]
    have hnw : decide ((BitVec.ofNat 64 8192).toNat + 8 ≤ 2 ^ 64) =
        true := by
      decide
    rw [hnw]
    simp [hwr]
  · have hlast := adrSchreiben_erlaubt s.speicher s n
      (basisKeinForm .rbx) hwr'
    rw [hf, haddr]
    rw [haddr] at hlast
    exact hlast

/-- JOINT WITNESS for `Disp0Frame_verbindung`: every premise on joint
    concrete values (the `[rbx]` form, the witness state with
    `rbx = 8192` and write rights) beside the fetched memory-changing
    run: 42 lands at 8192 from zero and reads back whole, with RIP past
    the three actual image bytes. -/
theorem Disp0Frame_verbindung_zeuge :
    ∃ (f : AdrForm) (s : Zustand) (n : Adresse),
      (f = basisKeinForm .rbx) ∧
      (s.register .rbx = BitVec.ofNat 64 8192) ∧
      (schreibbar8 s.speicher (BitVec.ofNat 64 8192) = true) ∧
      (adrEff s n f = BitVec.ofNat 64 8192) ∧
      (adrStoreSchritt s).map
          (fun t => t.speicher.bytes (BitVec.ofNat 64 8192)) =
          some (BitVec.ofNat 8 42) ∧
      (adrStoreSchritt s).bind
            (fun t => read64 t.speicher (BitVec.ofNat 64 8192)) =
          some (BitVec.ofNat 64 42) ∧
      s.speicher.bytes (BitVec.ofNat 64 8192) = BitVec.ofNat 8 0 ∧
      (adrStoreSchritt s).map (fun t => t.rip) =
        some (BitVec.ofNat 64 4099) := by
  exact ⟨basisKeinForm .rbx, disp0WitZustand, BitVec.ofNat 64 0,
    rfl, rfl, rfl, by rw [disp0_adr_base]; rfl, disp0Wit_speichert,
    disp0Wit_liest, disp0Wit_vorher_null, disp0Wit_rip⟩

/- CUTS:
    Proved here (all over the REUSED canonical vocabulary -- `AdrForm`,
    `adrEff`, `encodeAdr`, `parseAdrTail`, `kanonisch48`,
    `fussZugelassen`, `adrStoreSchritt`, `leaGeholtSchritt` -- no new
    register, memory, decoder or source model):
    - the disp0 frame predicate with its admission pin;
    - disp0 addresses are the bare base (no displacement added);
    - SIB exactly where the base low code is 4 (`rsp`, `r12`), pinned
      bytes, SIB-free two-byte encoding elsewhere;
    - mod=00 refuses `rbp`/`r13` (mod=00 r/m=101 is RIP-relative);
      the mod=01 disp8=0 escape is admitted and computes the bare base;
    - the `Disp0Frame_verbindung` connection (bare-base address, actual
      two-byte encoding length, accepted-footprint admission, admitted
      write) with the joint `Disp0Frame_verbindung_zeuge` witness: a
      fetched `mov [rbx], rax` through actual bytes lands 42 at 8192
      from zero, reads back whole, advances RIP past the three actual
      image bytes; dark-memory refusal beside it.
    NOT proved here, and not claimed:
    - No silicon correspondence: encodings follow Intel SDM Vol. 2
      Table 2-2 and Vol. 1 Section 3.3.7.1 as stated contracts against
      the local official snapshot; faults are the accepted
      permission-checked outcomes, not silicon.
    - No disp8/disp32 frame: those stay with the accepted
      `AddressEncoding` API and their own lanes.
    - No TSO/GX bridge: footprints are sequential per-byte sets;
      tearing and visibility stay open.
    - No source correspondence, no ABI/loader/entry/budget claim.
-/

#print axioms disp0Form_basisKein
#print axioms disp0_adr_base
#print axioms disp0_sib_rsp
#print axioms disp0_sib_r12
#print axioms disp0_ohne_sib_rbx
#print axioms disp0_rbp_verweigert
#print axioms disp0_r13_verweigert
#print axioms disp0_rbp_entkommt
#print axioms disp0_r13_entkommt
#print axioms disp0Wit_dekodiert
#print axioms disp0Wit_speichert
#print axioms disp0Wit_liest
#print axioms disp0Wit_vorher_null
#print axioms disp0Wit_rip
#print axioms disp0Wit_dunkel_verweigert
#print axioms Disp0Frame_verbindung
#print axioms Disp0Frame_verbindung_zeuge

end Gabbro.Grammatik.X86
