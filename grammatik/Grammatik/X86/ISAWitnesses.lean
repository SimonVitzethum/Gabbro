/-
  File:      Grammatik/X86/ISAWitnesses.lean
  Subject:   Witnesses and poison probes for the unified instruction set
             (`ISA.lean`, `ISAExecution.lean`).

  One MIXED program over all five families (pilot mov/cmp/store, mul/div
  imul, shift shl, setcc, narrow mov32/store32) is encoded with `encodeI`,
  laid out in executable memory, fetched and executed BOTH ways -- by
  `laufI` on the instruction list and by `laufBytesI` from actual bytes --
  and both change memory observably. The generic layout theorem is
  instantiated jointly on it. A second program with a taken jump exercises
  the trace theorem with control flow. Poison probes: non-canonical bytes,
  prefixes of one family continued by another family's opcode, truncated
  encodings, a fetch window cut by execute permission, a non-canonical
  shift count, and the mul/div trap. Reuses `bytesAusProg`, `witnessFlags`
  (`Byteschritt.lean`) for the memory layout vocabulary.
-/
import Grammatik.X86.ISAExecution

namespace Gabbro.Grammatik.X86

/-! ## 1. The mixed program. -/

/-- Mixed program: `rax := 6; rcx := 7; imul rax, rcx; shl rax, 1;
    cmp rax, rcx; setne dl; mov r8d, eax; mov [rbx], rax;
    mov dword [rbx+8], edx`. -/
def isaProg : List Instr :=
  [.pilot (.movImm64 .rax 6),
   .pilot (.movImm64 .rcx 7),
   .muldiv (.imul2 .rax .rcx),
   .shift (.imm .shl .rax 1),
   .pilot (.cmpReg64 .rax .rcx),
   .cond (.setcc .ne .rdx),
   .narrow (.mov32rr .r8 .rax),
   .pilot (.store64 .rbx .rax 0),
   .narrow (.store32 .rbx .rdx 8)]

/-- Its bytes, laid out back to back. -/
def isaBytes : List Byte := progBytes isaProg

/-- The layout is 52 bytes long. -/
theorem isaBytes_laenge : isaBytes.length = 52 := by decide

/-- Code window 4096..4196: executable only (never data-readable). -/
def isaExec (a : Adresse) : Bool := decide (4096 ≤ a.toNat ∧ a.toNat < 4196)

/-- Data cells 8192..8208: readable and writable, not executable. -/
def isaDaten (a : Adresse) : Bool := decide (8192 ≤ a.toNat ∧ a.toNat < 8208)

/-- Witness memory: the program at 4096, zeroed data at 8192. -/
def isaSpeicher : Speicher :=
  { bytes := bytesAusProg isaBytes 4096
    lesbar := isaDaten
    schreibbar := isaDaten
    ausfuehrbar := isaExec }

/-- Witness registers: `rbx` names the data cells, everything else zero. -/
def isaReg : Register → Wort := fun q =>
  if q = Register.rbx then BitVec.ofNat 64 8192 else BitVec.ofNat 64 0

/-- Witness start state. -/
def isaStart : Zustand :=
  { register := isaReg, flags := witnessFlags, rip := BitVec.ofNat 64 4096,
    speicher := isaSpeicher }

/-- Final-state observation: rax, rdx, r8, the data bytes at 8192 and
    8200, and RIP. -/
def isaBeob (s : Zustand) : Wort × Wort × Wort × Byte × Byte × Adresse :=
  (s.register .rax, s.register .rdx, s.register .r8,
    s.speicher.bytes (BitVec.ofNat 64 8192),
    s.speicher.bytes (BitVec.ofNat 64 8200), s.rip)

/-- Byte-run observation. -/
def isaAusgangBeob : ByteAusgang → Option (Wort × Wort × Wort × Byte × Byte × Adresse)
  | .weiter s => some (isaBeob s)
  | .verweigert => none

/-- ABSTRACT RUN: `laufI` on the instruction list computes 6*7 = 42,
    shifts to 84, sets dl from `84 != 7`, zero-extends into r8, and
    stores 84 and 1 into the data cells; RIP ends past the 52 bytes. -/
theorem isa_lauf_wert :
    (laufI (isaProg.map canonI) isaStart).map isaBeob =
      some (84, 1, 84, BitVec.ofNat 8 84, BitVec.ofNat 8 1,
        BitVec.ofNat 64 4148) := by
  decide

/-- BYTE RUN: nine fetched unified byte steps from ACTUAL memory reach the
    same observation. -/
theorem isa_bytes_wert :
    isaAusgangBeob (laufBytesI 9 isaStart) =
      some (84, 1, 84, BitVec.ofNat 8 84, BitVec.ofNat 8 1,
        BitVec.ofNat 64 4148) := by
  decide

/-- The data cells were zero before: the run changes memory observably. -/
theorem isa_speicher_vorher :
    isaStart.speicher.bytes (BitVec.ofNat 64 8192) = BitVec.ofNat 8 0 ∧
      isaStart.speicher.bytes (BitVec.ofNat 64 8200) = BitVec.ofNat 8 0 := by
  decide

/-! ## 2. Joint witness of the layout theorem. -/

theorem isaProg_kanonisch : ∀ i ∈ isaProg, kanonischI i = true := by decide

theorem isaProg_faellt : ∀ i ∈ isaProg, faelltDurchI i = true := by decide

/-- W^X of the witness memory: the code window and the data cells are
    disjoint intervals. -/
theorem isaSpeicher_wx : WX isaStart.speicher := by
  intro x hx
  simp only [isaStart, isaSpeicher, isaExec, decide_eq_true_eq] at hx
  show isaDaten x = false
  simp only [isaDaten, decide_eq_false_iff_not]
  omega

/-- The program bytes sit executable at the start RIP. -/
theorem isaStart_code : CodeAt isaStart.speicher isaStart.rip (progBytes isaProg) := by
  intro i hi
  have hl : i < 52 := by rw [← isaBytes_laenge]; exact hi
  revert i
  decide

/-- JOINT WITNESS for `laufBytesI_layout`: every premise instantiated on the
    mixed five-family program, the conclusion holds, and the run is
    memory-changing (two data bytes move from 0 to 84 and 1). -/
theorem laufBytesI_layout_zeuge :
    ∃ (is : List Instr) (s : Zustand),
      (∀ i ∈ is, kanonischI i = true) ∧ (∀ i ∈ is, faelltDurchI i = true) ∧
      WX s.speicher ∧ CodeAt s.speicher s.rip (progBytes is) ∧
      laufBytesI is.length s = ausgangVon (laufI (is.map canonI) s) ∧
      isaAusgangBeob (laufBytesI is.length s) =
        some (84, 1, 84, BitVec.ofNat 8 84, BitVec.ofNat 8 1,
          BitVec.ofNat 64 4148) ∧
      s.speicher.bytes (BitVec.ofNat 64 8192) = BitVec.ofNat 8 0 := by
  refine ⟨isaProg, isaStart, isaProg_kanonisch, isaProg_faellt, isaSpeicher_wx,
    isaStart_code, laufBytesI_layout isaProg isaStart isaProg_kanonisch
      isaProg_faellt isaSpeicher_wx isaStart_code, isa_bytes_wert,
    isa_speicher_vorher.1⟩

/-- Joint witness for `spurAn_layout` (same premises, trace conclusion). -/
theorem spurAn_layout_zeuge : SpurAn isaProg isaStart :=
  spurAn_layout isaProg isaStart isaProg_kanonisch isaProg_faellt
    isaSpeicher_wx isaStart_code

/-! ## 3. Control flow: the trace theorem with a taken jump. -/

/-- Jump program: `jmp +3` over three garbage bytes, then `mov rax, 42`
    and `mov [rbx], rax`. -/
def isaSprungProg : List Instr :=
  [.pilot (.jump32 3), .pilot (.movImm64 .rax 42), .pilot (.store64 .rbx .rax 0)]

/-- Its bytes: the jump, three 0xFF bytes no decoder accepts, the rest. -/
def isaSprungBytes : List Byte :=
  encodeI (.pilot (.jump32 3)) ++ [natByte 255, natByte 255, natByte 255] ++
    encodeI (.pilot (.movImm64 .rax 42)) ++ encodeI (.pilot (.store64 .rbx .rax 0))

def isaSprungStart : Zustand :=
  { isaStart with speicher := { isaSpeicher with bytes := bytesAusProg isaSprungBytes 4096 } }

/-- The garbage bytes are refused by every family: a straight-line fetch
    would stop there. -/
theorem sprung_muell_verweigert :
    decodeI [natByte 255, natByte 255, natByte 255] = none := by decide

/-- One step of a concrete run, as a named state. -/
theorem spurAn_schritt (i : Instr) (is : List Instr) (s s1 : Zustand)
    (hk : kanonischI i = true) (hw : ∃ suf, geholt s = encodeI i ++ suf)
    (hs : stepI (canonI i) s = some s1) (hn : SpurAn is s1) :
    SpurAn (i :: is) s :=
  ⟨hk, hw, fun s1' h' => by rw [hs] at h'; cases h'; exact hn⟩

theorem isaSprung_1_some : (stepI (canonI (.pilot (.jump32 3))) isaSprungStart).isSome = true := by
  decide

def isaSprung1 : Zustand := (stepI (canonI (.pilot (.jump32 3))) isaSprungStart).get isaSprung_1_some

theorem isaSprung_2_some : (stepI (canonI (.pilot (.movImm64 .rax 42))) isaSprung1).isSome = true := by
  decide

def isaSprung2 : Zustand :=
  (stepI (canonI (.pilot (.movImm64 .rax 42))) isaSprung1).get isaSprung_2_some

/-- The trace premise holds on the jump program: each executed instruction
    opens the fetch window at the RIP where it runs (the jump target 4104,
    not the garbage at 4101). -/
theorem sprung_spur : SpurAn isaSprungProg isaSprungStart := by
  refine spurAn_schritt _ _ _ isaSprung1 rfl ⟨_, (by decide :
      geholt isaSprungStart = encodeI (.pilot (.jump32 3)) ++
        ((geholt isaSprungStart).drop 5))⟩ (Option.some_get _).symm ?_
  refine spurAn_schritt _ _ _ isaSprung2 rfl ⟨_, (by decide :
      geholt isaSprung1 = encodeI (.pilot (.movImm64 .rax 42)) ++
        ((geholt isaSprung1).drop 10))⟩ (Option.some_get _).symm ?_
  refine ⟨rfl, ⟨_, (by decide :
      geholt isaSprung2 = encodeI (.pilot (.store64 .rbx .rax 0)) ++
        ((geholt isaSprung2).drop 7))⟩, fun _ _ => trivial⟩

/-- JOINT WITNESS for `laufBytesI_spur` with control flow: the byte run of
    the jump program equals `laufI`, and it stores 42 into the zeroed cell. -/
theorem laufBytesI_spur_zeuge :
    laufBytesI isaSprungProg.length isaSprungStart =
        ausgangVon (laufI (isaSprungProg.map canonI) isaSprungStart) ∧
      (laufI (isaSprungProg.map canonI) isaSprungStart).map
          (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (BitVec.ofNat 8 42) ∧
      isaSprungStart.speicher.bytes (BitVec.ofNat 64 8192) = BitVec.ofNat 8 0 :=
  ⟨laufBytesI_spur isaSprungProg isaSprungStart sprung_spur, by decide, by decide⟩

/-! ## 4. Joint witnesses of the codec and step theorems. -/

/-- One canonical instruction per family (the setcc/cmov family twice). -/
def isaJeFamilie : List Instr :=
  [.pilot (.store64 .r12 .r9 (BitVec.ofNat 32 0x10)),
   .muldiv (.idivRax .r8),
   .shift (.cl .sar .r11),
   .narrow (.movsx8 .r13 .rsi),
   .cond (.setcc .l .r9),
   .cond (.cmov .ge .r10 .r15)]

/-- Witness for `decodeI_encodeI`: every family round-trips with a
    nonempty suffix. -/
theorem decodeI_encodeI_zeuge :
    ∀ i ∈ isaJeFamilie, kanonischI i = true ∧
      decodeI (encodeI i ++ [natByte 195]) = some (canonI i, [natByte 195]) := by
  decide

/-- Witness for `familien_disjunkt` / `decF_fremd_encodeI`: on each
    family's bytes exactly ONE family decoder accepts. -/
theorem familien_disjunkt_zeuge :
    ∀ i ∈ isaJeFamilie, ∀ G ∈ alleFam,
      (decF G (encodeI i)).isSome = decide (G = famI i) := by
  decide

/-- Witness for `decodeI_eindeutig` and `decodeI_verbraucht`. -/
theorem decodeI_eindeutig_zeuge :
    ∀ i ∈ isaJeFamilie,
      famOf (encodeI i ++ [natByte 0]) = famI i ∧
      (decodeI (encodeI i ++ [natByte 0])).map (fun p => p.1.laenge + p.2.length) =
        some (encodeI i ++ [natByte 0]).length := by
  decide

/-- Witness for `byteschrittI_kanonisch` and `byteschrittI_erweitert`: the
    first fetched unified step of the mixed program is the pilot step. -/
theorem byteschrittI_kanonisch_zeuge :
    fetchDekodiertI isaStart =
        some (canonI (.pilot (.movImm64 .rax 6)), (geholt isaStart).drop 10) ∧
      ausgangRip (byteschrittI isaStart) = some (BitVec.ofNat 64 4106) ∧
      ausgangRip (byteschritt isaStart) = some (BitVec.ofNat 64 4106) := by
  decide

/-- Witness for `laufI_pilot`: a pilot-only run lifted into the unified run. -/
theorem laufI_pilot_zeuge :
    (laufI (zeugeProg.map liftPilot) zeugeZustand).map
        (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
      (lauf zeugeProg zeugeZustand).map
        (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) ∧
    (lauf zeugeProg zeugeZustand).map
        (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
      some (BitVec.ofNat 8 42) := by
  refine ⟨by rw [laufI_pilot], by decide⟩

/-- Witness for `laufI_append`: splitting the mixed program anywhere gives
    the same run. -/
theorem laufI_append_zeuge :
    ((laufI ((isaProg.take 4).map canonI) isaStart).bind
        (laufI ((isaProg.drop 4).map canonI))).map isaBeob =
      some (84, 1, 84, BitVec.ofNat 8 84, BitVec.ofNat 8 1,
        BitVec.ofNat 64 4148) := by
  rw [← laufI_append, ← List.map_append, List.take_append_drop]
  exact isa_lauf_wert

/-! ## 5. Poison probes. -/

/-- NON-CANONICAL: REX.X (0x4A) on a register move is refused by every
    family. -/
theorem gift_rex_x : decodeI [natByte 0x4A, natByte 0x89, natByte 0xC8] = none := by
  decide

/-- NON-CANONICAL: a register-indirect (mod=0) ModRM on IMUL is refused. -/
theorem gift_imul_mod0 :
    decodeI [natByte 0x48, natByte 0x0F, natByte 0xAF, natByte 0x01] = none := by
  decide

/-- OVERLAPPING PREFIX: REX.W (pilot/mul/div/cmov prefix) continued by the
    SETcc opcode `0F 95` is refused (SETcc admits only REX 40/41). -/
theorem gift_rexw_setcc :
    decodeI [natByte 0x48, natByte 0x0F, natByte 0x95, natByte 0xC0] = none := by
  decide

/-- OVERLAPPING PREFIX: REX 40 (setcc/narrow prefix) continued by the CMOV
    opcode `0F 45` is refused (CMOV needs REX.W). -/
theorem gift_rex40_cmov :
    decodeI [natByte 0x40, natByte 0x0F, natByte 0x45, natByte 0xC1] = none := by
  decide

/-- OVERLAPPING PREFIX: REX.W continued by the narrow MOVZX opcode `0F B6`
    is refused (narrow rows carry W = 0). -/
theorem gift_rexw_movzx :
    decodeI [natByte 0x48, natByte 0x0F, natByte 0xB6, natByte 0xC1] = none := by
  decide

/-- OVERLAPPING PREFIX: REX 41 (pilot push/pop prefix) continued by the
    IMUL opcode `0F AF` is refused (IMUL needs REX.W). -/
theorem gift_rex41_imul :
    decodeI [natByte 0x41, natByte 0x0F, natByte 0xAF, natByte 0xC1] = none := by
  decide

/-- OVERLAPPING PREFIX: REX.WR (0x4C) on a shift is refused (REX.R would
    rewrite the Group-2 digit). -/
theorem gift_rexwr_shift :
    decodeI [natByte 0x4C, natByte 0xC1, natByte 0xE0, natByte 0x01] = none := by
  decide

/-- TRUNCATED: every family's canonical encoding minus its last byte is
    refused. -/
theorem gift_abgeschnitten :
    ∀ i ∈ isaJeFamilie ++ isaProg, decodeI (encodeI i).dropLast = none := by
  decide

/-- TRUNCATED BY PERMISSION: with execute permission ending after the
    first three bytes of the mixed program, the unified byte step refuses
    (fetch never reads past executable memory). -/
def isaStumpf : Zustand :=
  { isaStart with speicher :=
    { isaSpeicher with ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4099) } }

theorem gift_fenster_kurz : ausgangRip (byteschrittI isaStumpf) = none := by
  decide

/-- MUTATED BYTE: forging the IMUL opcode byte (0F AF to 0F AE) in the
    laid-out program stops the byte run at that instruction, while the
    abstract run succeeds -- the actual bytes govern the run. -/
def isaMutiert : Zustand :=
  { isaStart with speicher :=
    { isaSpeicher with bytes := bytesAusProg (isaBytes.set 22 (natByte 0xAE)) 4096 } }

theorem gift_mutiert_verweigert :
    isaAusgangBeob (laufBytesI 9 isaMutiert) = none ∧
      ausgangRip (laufBytesI 2 isaMutiert) = some (BitVec.ofNat 64 4116) := by
  decide

/-- NON-CANONICAL SHIFT COUNT: a count of 300 has no one-byte encoding;
    its bytes decode to the count 44, so `kanonischI` is a necessary
    premise of `decodeI_encodeI`. -/
theorem gift_shift_300 :
    kanonischI (.shift (.imm .shl .rax 300)) = false ∧
      decodeI (encodeI (.shift (.imm .shl .rax 300))) =
        some (⟨.shift (.imm .shl .rax 44), 4⟩, []) := by
  decide

/-- TRAP: IDIV by zero is the mul/div hardware trap in `stepIE`, no
    successor in `stepI`, and a refused unified byte step. -/
def isaNullteiler : Zustand :=
  { isaStart with speicher :=
    { isaSpeicher with bytes := bytesAusProg (encodeI (.muldiv (.idivRax .rcx))) 4096 } }

theorem gift_idiv_null :
    (match stepIE (canonI (.muldiv (.idivRax .rcx))) isaNullteiler with
      | .hardwareHalt => true | _ => false) = true ∧
    (stepI (canonI (.muldiv (.idivRax .rcx))) isaNullteiler).isSome = false ∧
    ausgangRip (byteschrittI isaNullteiler) = none := by
  decide

/- CUTS:
   - The witnesses are concrete runs checked by kernel evaluation; they add
     no generic claim beyond `ISA.lean`/`ISAExecution.lean`.
   - `familien_disjunkt` can only be instantiated with `F = G` (that is its
     content); `familien_disjunkt_zeuge` shows the non-degenerate side:
     on each family's bytes the other five decoders refuse.
   - No hardware, TSO or source claim.
-/

#print axioms isaBytes_laenge
#print axioms isa_lauf_wert
#print axioms isa_bytes_wert
#print axioms isa_speicher_vorher
#print axioms isaProg_kanonisch
#print axioms isaProg_faellt
#print axioms isaSpeicher_wx
#print axioms isaStart_code
#print axioms laufBytesI_layout_zeuge
#print axioms spurAn_layout_zeuge
#print axioms sprung_muell_verweigert
#print axioms spurAn_schritt
#print axioms sprung_spur
#print axioms laufBytesI_spur_zeuge
#print axioms decodeI_encodeI_zeuge
#print axioms familien_disjunkt_zeuge
#print axioms decodeI_eindeutig_zeuge
#print axioms byteschrittI_kanonisch_zeuge
#print axioms laufI_pilot_zeuge
#print axioms laufI_append_zeuge
#print axioms gift_rex_x
#print axioms gift_imul_mod0
#print axioms gift_rexw_setcc
#print axioms gift_rex40_cmov
#print axioms gift_rexw_movzx
#print axioms gift_rex41_imul
#print axioms gift_rexwr_shift
#print axioms gift_abgeschnitten
#print axioms gift_fenster_kurz
#print axioms gift_mutiert_verweigert
#print axioms gift_shift_300
#print axioms gift_idiv_null

end Gabbro.Grammatik.X86
