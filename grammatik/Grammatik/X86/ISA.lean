/-
  File:      Grammatik/X86/ISA.lean
  Subject:   ONE unified integer instruction set over the ONE x86-64 state:
             one instruction type, one step, one run, one codec.

  Before this file the pilot `Befehl` (`Typen.lean`, stepped by
  `Ausfuehrung.schritt`, coded by `Codec.encode`/`decode`) was extended only
  by SEPARATE family modules, each with its own instruction type, step and
  codec. No single machine executed a program mixing them. This file joins
  them WITHOUT re-implementing any of them:

    family          instruction type   step (reused)          codec (reused)
    pilot           `Befehl`           `schritt`              `encode`/`decode`
    mul/div         `MulDivBefehl`     `mulDivSchritt`        `mulDivEncode`/`decodeMulDiv`
    shift           `ShiftForm`        `shiftSchritt`         `encodeShift`/`decodeShift`
    narrow          `NarrowOp`         `stepNarrow`           `encodeNarrow`/`decodeNarrow`
    setcc / cmov    `CondForm`         `setccSchrittBytes`,   `encodeSetCC`/`decodeSetCC`,
                                       `cmovSchrittBytes`     `encodeCmov`/`decodeCmov`
    compact (§2B)   `CompactBefehl`    `schrittC`             `encodeC`/`decodeC`
    integer core    `CoreBefehl`       `coreSchritt`          `encodeCore`/`decodeCore`

  All seven families run over the SAME `Zustand` (`Typen.lean`). The compact
  and integer-core families (`CompactForms.lean`, `IntegerCore.lean`) were
  joined by the four-step procedure of §5; the arbitrary-input signature and
  consumed-length facts they lacked are proved HERE (`decodeC_sig`,
  `decodeCore_sig`, `decodeC_verbraucht`, `decodeCore_verbraucht`). Their
  bytes do NOT genuinely overlap any earlier family: every shared prefix is
  separated by the opcode or, where the opcode is shared, by the ModRM mode
  or digit (see `famSig`), so no priority rule is needed and
  `familien_disjunkt` holds unconditionally over all eight decoders. Scalar float
  (`ScalarFloat.lean`), vector (`VectorCodec.lean`) and locked operations
  (`LockedOps.lean`) need extra state (`FpZustand`, `TSOZustand`) and are
  left OUT (see CUTS); no state is invented for them here.

  Contents:
    §1 `Instr`, `InstrDecoded`, `stepI` (delegation only), `laufI`,
       `laufI_append`, the pilot embedding `laufI_pilot`.
    §2 `encodeI`, the family decoders `decF`, `decodeI` (first family that
       accepts), length facts.
    §3 DISJOINTNESS over ARBITRARY byte strings: every family decoder that
       accepts a byte string forces the same signature `famOf` of its first
       three bytes, so at most one family accepts any byte string, and the
       priority order inside `decodeI` is irrelevant.
    §4 `decodeI_encodeI` round trip (canonical instructions), consumed-length
       agreement over arbitrary input.
    §5 How to add a further family (4 mechanical steps).
  Fetch-and-execute from executable memory lives in `ISAExecution.lean`,
  witnesses and poison probes in `ISAWitnesses.lean`.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.DecoderSoundness
import Grammatik.X86.MulDiv
import Grammatik.X86.MulDivCodec
import Grammatik.X86.ShiftCodec
import Grammatik.X86.NarrowCodec
import Grammatik.X86.ControlCodec
import Grammatik.X86.CompactForms
import Grammatik.X86.IntegerCore

namespace Gabbro.Grammatik.X86

/-! ## 1. One instruction type, one step, one run. -/

/-- The unified instruction set: one constructor per family, each wrapping
    the EXISTING family instruction type unchanged. -/
inductive Instr where
  | pilot (b : Befehl)
  | muldiv (b : MulDivBefehl)
  | shift (f : ShiftForm)
  | narrow (o : NarrowOp)
  | cond (c : CondForm)
  | compact (c : CompactBefehl)
  | core (c : CoreBefehl)
  deriving DecidableEq, Repr

/-- A decoded unified instruction with its consumed length (checked data,
    exactly as `Decodiert` carries it for the pilot). -/
structure InstrDecoded where
  instr : Instr
  laenge : Nat
  deriving DecidableEq, Repr

/-- Full unified step outcome. It REUSES the mul/div outcome type
    (`ok` / `hardwareHalt` / `misslungen`), because mul/div is the only
    family with a hardware trap (#DE on a zero divisor or quotient
    overflow); every other family maps its refusal to `misslungen`. -/
def stepIE : InstrDecoded → Zustand → MulDivErgebnis
  | ⟨.pilot b, l⟩, s =>
    match schritt ⟨b, l⟩ s with
    | some s' => .ok s'
    | none => .misslungen
  | ⟨.muldiv b, l⟩, s => mulDivSchritt ⟨b, l⟩ s
  | ⟨.shift f, l⟩, s =>
    match shiftSchritt ⟨f, l⟩ s with
    | some s' => .ok s'
    | none => .misslungen
  | ⟨.narrow o, l⟩, s =>
    match stepNarrow ⟨o, l⟩ s with
    | some s' => .ok s'
    | none => .misslungen
  | ⟨.cond (.setcc c dst), l⟩, s =>
    match setccSchrittBytes l s dst c with
    | some s' => .ok s'
    | none => .misslungen
  | ⟨.cond (.cmov c dst src), l⟩, s =>
    match cmovSchrittBytes l s dst src c with
    | some s' => .ok s'
    | none => .misslungen
  | ⟨.compact c, l⟩, s =>
    match schrittC ⟨c, l⟩ s with
    | some s' => .ok s'
    | none => .misslungen
  | ⟨.core c, l⟩, s =>
    match coreSchritt ⟨c, l⟩ s with
    | some s' => .ok s'
    | none => .misslungen

/-- The unified step over the one `Zustand`: pure delegation to each
    family's EXISTING step; no family semantics is re-implemented. The
    mul/div hardware trap is `none` here (no successor state); `stepIE`
    keeps the distinction. -/
def stepI : InstrDecoded → Zustand → Option Zustand
  | ⟨.pilot b, l⟩, s => schritt ⟨b, l⟩ s
  | ⟨.muldiv b, l⟩, s =>
    match mulDivSchritt ⟨b, l⟩ s with
    | .ok s' => some s'
    | _ => none
  | ⟨.shift f, l⟩, s => shiftSchritt ⟨f, l⟩ s
  | ⟨.narrow o, l⟩, s => stepNarrow ⟨o, l⟩ s
  | ⟨.cond (.setcc c dst), l⟩, s => setccSchrittBytes l s dst c
  | ⟨.cond (.cmov c dst src), l⟩, s => cmovSchrittBytes l s dst src c
  | ⟨.compact c, l⟩, s => schrittC ⟨c, l⟩ s
  | ⟨.core c, l⟩, s => coreSchritt ⟨c, l⟩ s

/-- Successor projection of the full outcome. -/
def MulDivErgebnis.nachfolger : MulDivErgebnis → Option Zustand
  | .ok s' => some s'
  | _ => none

/-- `stepI` is exactly the successor projection of the full outcome. -/
theorem stepI_eq_stepIE (d : InstrDecoded) (s : Zustand) :
    stepI d s = (stepIE d s).nachfolger := by
  obtain ⟨i, l⟩ := d
  cases i with
  | pilot b =>
    show schritt ⟨b, l⟩ s = _
    simp only [stepIE]
    cases schritt ⟨b, l⟩ s <;> rfl
  | muldiv b =>
    show (match mulDivSchritt ⟨b, l⟩ s with | .ok s' => some s' | _ => none) = _
    simp only [stepIE]
    cases mulDivSchritt ⟨b, l⟩ s <;> rfl
  | shift f =>
    show shiftSchritt ⟨f, l⟩ s = _
    simp only [stepIE]
    cases shiftSchritt ⟨f, l⟩ s <;> rfl
  | narrow o =>
    show stepNarrow ⟨o, l⟩ s = _
    simp only [stepIE]
    cases stepNarrow ⟨o, l⟩ s <;> rfl
  | cond c =>
    cases c with
    | setcc c dst =>
      show setccSchrittBytes l s dst c = _
      simp only [stepIE]
      cases setccSchrittBytes l s dst c <;> rfl
    | cmov c dst src =>
      show cmovSchrittBytes l s dst src c = _
      simp only [stepIE]
      cases cmovSchrittBytes l s dst src c <;> rfl
  | compact c =>
    show schrittC ⟨c, l⟩ s = _
    simp only [stepIE]
    cases schrittC ⟨c, l⟩ s <;> rfl
  | core c =>
    show coreSchritt ⟨c, l⟩ s = _
    simp only [stepIE]
    cases coreSchritt ⟨c, l⟩ s <;> rfl

/-- Only the mul/div family can raise the hardware trap. -/
theorem stepIE_halt_nur_muldiv (d : InstrDecoded) (s : Zustand)
    (h : stepIE d s = .hardwareHalt) :
    ∃ b, d.instr = .muldiv b := by
  obtain ⟨i, l⟩ := d
  cases i with
  | muldiv b => exact ⟨b, rfl⟩
  | pilot b =>
    simp only [stepIE] at h
    split at h <;> cases h
  | shift f =>
    simp only [stepIE] at h
    split at h <;> cases h
  | narrow o =>
    simp only [stepIE] at h
    split at h <;> cases h
  | cond c =>
    cases c with
    | setcc c dst =>
      simp only [stepIE] at h
      split at h <;> cases h
    | cmov c dst src =>
      simp only [stepIE] at h
      split at h <;> cases h
  | compact c =>
    simp only [stepIE] at h
    split at h <;> cases h
  | core c =>
    simp only [stepIE] at h
    split at h <;> cases h

/-! ### Delegation equations: each family's step IS the unified step. -/

theorem stepI_pilot (b : Befehl) (l : Nat) (s : Zustand) :
    stepI ⟨.pilot b, l⟩ s = schritt ⟨b, l⟩ s := rfl

theorem stepI_muldiv (b : MulDivBefehl) (l : Nat) (s : Zustand) :
    stepI ⟨.muldiv b, l⟩ s = (mulDivSchritt ⟨b, l⟩ s).nachfolger := by
  show (match mulDivSchritt ⟨b, l⟩ s with | .ok s' => some s' | _ => none) = _
  cases mulDivSchritt ⟨b, l⟩ s <;> rfl

theorem stepI_shift (f : ShiftForm) (l : Nat) (s : Zustand) :
    stepI ⟨.shift f, l⟩ s = shiftSchritt ⟨f, l⟩ s := rfl

theorem stepI_narrow (o : NarrowOp) (l : Nat) (s : Zustand) :
    stepI ⟨.narrow o, l⟩ s = stepNarrow ⟨o, l⟩ s := rfl

theorem stepI_setcc (c : Bedingung) (dst : Register) (l : Nat) (s : Zustand) :
    stepI ⟨.cond (.setcc c dst), l⟩ s = setccSchrittBytes l s dst c := rfl

theorem stepI_cmov (c : Bedingung) (dst src : Register) (l : Nat)
    (s : Zustand) :
    stepI ⟨.cond (.cmov c dst src), l⟩ s = cmovSchrittBytes l s dst src c := rfl

theorem stepI_compact (c : CompactBefehl) (l : Nat) (s : Zustand) :
    stepI ⟨.compact c, l⟩ s = schrittC ⟨c, l⟩ s := rfl

theorem stepI_core (c : CoreBefehl) (l : Nat) (s : Zustand) :
    stepI ⟨.core c, l⟩ s = coreSchritt ⟨c, l⟩ s := rfl

/-- A unified run: the decoded sequence applied in order; `none` is a loud
    failure (refusal or trap), never a silent halt. Same shape as `lauf`. -/
def laufI : List InstrDecoded → Zustand → Option Zustand
  | [], s => some s
  | d :: rest, s =>
    match stepI d s with
    | some s' => laufI rest s'
    | none => none

/-- Runs compose: running `p ++ q` is running `p`, then `q`. -/
theorem laufI_append (p q : List InstrDecoded) (s : Zustand) :
    laufI (p ++ q) s = (laufI p s).bind (laufI q) := by
  induction p generalizing s with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.cons_append, laufI]
    cases stepI d s with
    | none => rfl
    | some s' => exact ih s'

/-- Pilot embedding of one decoded pilot instruction. -/
def liftPilot (d : Decodiert) : InstrDecoded := ⟨.pilot d.befehl, d.laenge⟩

/-- EMBEDDING: on pilot-only programs the unified run IS the pilot run. -/
theorem laufI_pilot (p : List Decodiert) (s : Zustand) :
    laufI (p.map liftPilot) s = lauf p s := by
  induction p generalizing s with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.map_cons, laufI, lauf]
    show (match schritt ⟨d.befehl, d.laenge⟩ s with
      | some s' => laufI (rest.map liftPilot) s' | none => none) = _
    cases schritt d s with
    | none => rfl
    | some s' => exact ih s'

/-! ## 2. One codec: encoder and the family decoders. -/

/-- Unified canonical encoding: delegation to each family encoder. -/
def encodeI : Instr → List Byte
  | .pilot b => encode b
  | .muldiv b => mulDivEncode b
  | .shift f => encodeShift f
  | .narrow o => encodeNarrow o
  | .cond (.setcc c dst) => encodeSetCC c dst
  | .cond (.cmov c dst src) => encodeCmov c dst src
  | .compact c => encodeC c
  | .core c => encodeCore c

/-- Canonicity: the syntax that admits values without a canonical
    encoding is the shift immediate (`imm8 : Nat`, one byte), the compact
    disp0 memory forms over `rbp`/`r13` (mod=0 with those bases is the
    RIP-relative row, `CompactForms` §6), and an LEA index `rsp`
    (`IntegerCore.coreValid`). -/
def kanonischI : Instr → Bool
  | .shift (.imm _ _ n) => decide (n < 256)
  | .compact (.load64Disp0 _ base) => decide (base ≠ .rbp ∧ base ≠ .r13)
  | .compact (.store64Disp0 base _) => decide (base ≠ .rbp ∧ base ≠ .r13)
  | .core c => coreValid c
  | _ => true

/-- The canonical decoded form of an instruction: its encoding length. -/
def canonI (i : Instr) : InstrDecoded := ⟨i, (encodeI i).length⟩

/-- The family tags of the unified decoder (the conditional family has two
    independent decoders, so it carries two tags). -/
inductive Fam where
  | pilot | muldiv | shift | narrow | setcc | cmov | compact | core
  deriving DecidableEq, Repr

/-- Family tag of an instruction. -/
def famI : Instr → Fam
  | .pilot _ => .pilot
  | .muldiv _ => .muldiv
  | .shift _ => .shift
  | .narrow _ => .narrow
  | .cond (.setcc _ _) => .setcc
  | .cond (.cmov _ _ _) => .cmov
  | .compact _ => .compact
  | .core _ => .core

/-- Family decoders: each is the EXISTING family decoder, its result
    wrapped into `InstrDecoded`. -/
def decF : Fam → List Byte → Option (InstrDecoded × List Byte)
  | .pilot, bs =>
    match decode bs with
    | some (d, r) => some (⟨.pilot d.befehl, d.laenge⟩, r)
    | none => none
  | .muldiv, bs =>
    match decodeMulDiv bs with
    | some (d, r) => some (⟨.muldiv d.befehl, d.laenge⟩, r)
    | none => none
  | .shift, bs =>
    match decodeShift bs with
    | some (f, r) => some (⟨.shift f, shiftLaenge f⟩, r)
    | none => none
  | .narrow, bs =>
    match decodeNarrow bs with
    | some (d, r) => some (⟨.narrow d.op, d.laenge⟩, r)
    | none => none
  | .setcc, bs =>
    match decodeSetCC bs with
    | some ((c, dst), r) => some (⟨.cond (.setcc c dst), 4⟩, r)
    | none => none
  | .cmov, bs =>
    match decodeCmov bs with
    | some ((c, dst, src), r) => some (⟨.cond (.cmov c dst src), 4⟩, r)
    | none => none
  | .compact, bs =>
    match decodeC bs with
    | some (d, r) => some (⟨.compact d.befehl, d.laenge⟩, r)
    | none => none
  | .core, bs =>
    match decodeCore bs with
    | some (d, r) => some (⟨.core d.befehl, d.laenge⟩, r)
    | none => none

/-- First family in a list that accepts the bytes. -/
def erstesF : List Fam → List Byte → Option (InstrDecoded × List Byte)
  | [], _ => none
  | f :: fs, bs =>
    match decF f bs with
    | some x => some x
    | none => erstesF fs bs

/-- The family order of the unified decoder. By §3 the order is
    irrelevant (at most one family accepts any byte string); it is fixed
    here only to make `decodeI` a function. -/
def alleFam : List Fam :=
  [.pilot, .muldiv, .shift, .narrow, .setcc, .cmov, .compact, .core]

/-- Every family is in the decoder's list. -/
theorem mem_alleFam (f : Fam) : f ∈ alleFam := by
  cases f <;> simp [alleFam]

/-- The unified decoder: the first family decoder that accepts. -/
def decodeI (bs : List Byte) : Option (InstrDecoded × List Byte) :=
  erstesF alleFam bs

/-- Every compact encoding is 2..7 bytes long (no such lemma exists in
    `CompactForms.lean`; proved here from `encodeC` itself). -/
theorem encodeC_len (c : CompactBefehl) :
    1 ≤ (encodeC c).length ∧ (encodeC c).length ≤ 15 := by
  cases c <;> simp only [encodeC, leBytes32] <;> (try split) <;> simp

/-- Every unified encoding is 1..15 bytes long. -/
theorem encodeI_len (i : Instr) :
    1 ≤ (encodeI i).length ∧ (encodeI i).length ≤ 15 := by
  cases i with
  | pilot b => exact encode_len b
  | muldiv b => exact mulDivEncode_len_ok b
  | shift f => exact encodeShift_len_ok f
  | narrow o => exact encodeNarrow_len o
  | cond c =>
    cases c with
    | setcc c dst => exact show 1 ≤ 4 ∧ 4 ≤ 15 from by decide
    | cmov c dst src => exact show 1 ≤ 4 ∧ 4 ≤ 15 from by decide
  | compact c => exact encodeC_len c
  | core c => exact encodeCore_len_ok c

/-- The canonical length passes the shared decode-length guard. -/
theorem laengeOk_encodeI (i : Instr) : laengeOk (encodeI i).length = true := by
  simp only [laengeOk, decide_eq_true_eq]
  exact encodeI_len i

/-- FAMILY ROUND TRIP: the instruction's own family decoder inverts its
    canonical encoding, over any suffix. -/
theorem decF_encodeI (i : Instr) (hk : kanonischI i = true)
    (suffix : List Byte) :
    decF (famI i) (encodeI i ++ suffix) = some (canonI i, suffix) := by
  cases i with
  | pilot b =>
    simp only [famI, decF, encodeI, canonI, roundtrip b suffix]
  | muldiv b =>
    simp only [famI, decF, encodeI, canonI, roundtrip_muldiv b suffix]
  | shift f =>
    cases f with
    | imm r dst n =>
      have hn : n < 256 := by simpa [kanonischI] using hk
      simp only [famI, decF, encodeI, canonI,
        roundtripShiftImm r dst n hn suffix, encodeShift_laenge]
    | cl r dst =>
      simp only [famI, decF, encodeI, canonI, roundtripShiftCl r dst suffix,
        encodeShift_laenge]
  | narrow o =>
    simp only [famI, decF, encodeI, canonI, roundtripNarrow o suffix]
  | cond c =>
    cases c with
    | setcc c dst =>
      simp only [famI, decF, encodeI, canonI, roundtrip_setCC c dst suffix,
        encodeSetCC_len]
    | cmov c dst src =>
      simp only [famI, decF, encodeI, canonI, roundtrip_cmov c dst src suffix,
        encodeCmov_len]
  | compact c =>
    cases c with
    | movImm32Zx dst imm =>
      simp only [famI, decF, encodeI, canonI, roundtripC_movImm32Zx dst imm suffix]
    | movImm32Sx dst imm =>
      simp only [famI, decF, encodeI, canonI, roundtripC_movImm32Sx dst imm suffix]
    | aluImm8 op dst imm =>
      simp only [famI, decF, encodeI, canonI, roundtripC_aluImm8 op dst imm suffix]
    | aluImm32 op dst imm =>
      simp only [famI, decF, encodeI, canonI, roundtripC_aluImm32 op dst imm suffix]
    | load64Disp8 dst base disp =>
      simp only [famI, decF, encodeI, canonI,
        roundtripC_load64Disp8 dst base disp suffix]
    | store64Disp8 base src disp =>
      simp only [famI, decF, encodeI, canonI,
        roundtripC_store64Disp8 base src disp suffix]
    | load64Disp0 dst base =>
      have hb : base ≠ .rbp ∧ base ≠ .r13 := by simpa [kanonischI] using hk
      simp only [famI, decF, encodeI, canonI,
        roundtripC_load64Disp0 dst base suffix hb.1 hb.2]
    | store64Disp0 base src =>
      have hb : base ≠ .rbp ∧ base ≠ .r13 := by simpa [kanonischI] using hk
      simp only [famI, decF, encodeI, canonI,
        roundtripC_store64Disp0 base src suffix hb.1 hb.2]
    | jump8 rel =>
      simp only [famI, decF, encodeI, canonI, roundtripC_jump8 rel suffix]
    | jumpIf8 cond rel =>
      simp only [famI, decF, encodeI, canonI, roundtripC_jumpIf8 cond rel suffix]
  | core c =>
    have hv : coreValid c = true := by simpa [kanonischI] using hk
    simp only [famI, decF, encodeI, canonI, roundtripCore c hv suffix,
      encodeCore_laenge]

/-! ## 3. Disjointness over arbitrary byte strings.

    Every family decoder that accepts a byte string forces one signature
    of its first three bytes (`famOf`). Signatures of different families
    differ, so AT MOST ONE family accepts any byte string. This is proved
    over ARBITRARY input, not only over canonical encodings. The byte
    classes, read off the decoders:

      pilot   first byte 195/232/233/15/80..95, or 65 then 80..95, or
              REX.W (72/73/76/77) then 184..191/137/1/41/49/57/139
      muldiv  REX.W then 247, or REX.W then 15 175
      shift   72/73 then 193/211
      narrow  64/65/68/69 then 137, or then 15 182/190
      setcc   64/65 then 15 144..159
      cmov    REX.W then 15 64..79

    Shared PREFIXES do exist (REX.W 72/73/76/77 opens pilot, mul/div,
    shift and cmov rows; 65 opens pilot push/pop, narrow and setcc rows;
    15 after REX.W opens mul/div and cmov rows), but the second or third
    byte always separates them; no family decoder accepts a byte string
    another family decoder accepts. -/

/-- Head byte as a number; 256 (never a byte) for the empty list. -/
def kopfN : List Byte → Nat
  | [] => 256
  | b :: _ => byteNat b

/-- Family signature of the first three bytes. The compact and integer
    core rows share the REX.W prefixes 72/73/76/77 with pilot, mul/div,
    shift and cmov rows; the SECOND byte (opcode) and, where opcodes are
    shared, the THIRD byte (ModRM mode or digit, or the second opcode
    byte after `0F`) separate them:
      REX.W 0F: 175 mul/div, 64..79 cmov, 182/183/190/191 core;
      REX.W F7: ModRM digit 2/3 core (NOT/NEG), 4/6/7 mul/div;
      REX.W 89/8B: ModRM mod 0/1 compact, mod 2/3 pilot;
      REX.W C7/83/81: compact; REX.W 8D/21/09/85/63: core;
      REX.WX (74/75/78/79): core (LEA with an extended index only);
      65 then B8..BF: compact (`movImm32Zx` r8..r15);
      EB, 70..7F, B8..BF as first byte: compact. -/
def famSig (n1 n2 n3 : Nat) : Fam :=
  if n1 = 72 ∨ n1 = 73 ∨ n1 = 76 ∨ n1 = 77 then
    if n2 = 15 then
      (if n3 = 175 then .muldiv
       else if 64 ≤ n3 ∧ n3 < 80 then .cmov
       else if n3 = 182 ∨ n3 = 183 ∨ n3 = 190 ∨ n3 = 191 then .core
       else .pilot)
    else if n2 = 247 then
      (if n3 / 8 % 8 = 2 ∨ n3 / 8 % 8 = 3 then .core else .muldiv)
    else if (n1 = 72 ∨ n1 = 73) ∧ (n2 = 193 ∨ n2 = 211) then .shift
    else if n2 = 199 ∨ n2 = 131 ∨ n2 = 129 then .compact
    else if (n2 = 137 ∨ n2 = 139) ∧ n3 / 64 < 2 then .compact
    else if n2 = 141 ∨ n2 = 33 ∨ n2 = 9 ∨ n2 = 133 ∨ n2 = 99 then .core
    else .pilot
  else if n1 = 74 ∨ n1 = 75 ∨ n1 = 78 ∨ n1 = 79 then .core
  else if n1 = 64 ∨ n1 = 65 ∨ n1 = 68 ∨ n1 = 69 then
    if n2 = 15 then (if 144 ≤ n3 ∧ n3 < 160 then .setcc else .narrow)
    else if n2 = 137 then .narrow
    else if n1 = 65 ∧ 184 ≤ n2 ∧ n2 < 192 then .compact
    else .pilot
  else if n1 = 235 ∨ (112 ≤ n1 ∧ n1 < 128) ∨ (184 ≤ n1 ∧ n1 < 192) then .compact
  else .pilot

theorem kopfN_cons (b : Byte) (t : List Byte) : kopfN (b :: t) = byteNat b := rfl

/-- Signature of a byte string. -/
def famOf (bs : List Byte) : Fam :=
  famSig (kopfN bs) (kopfN (bs.drop 1)) (kopfN (bs.drop 2))

theorem famOf_cons (b : Byte) (rest : List Byte) :
    famOf (b :: rest) = famSig (byteNat b) (kopfN rest) (kopfN (rest.drop 1)) := rfl

theorem famOf_cons2 (b c : Byte) (rest : List Byte) :
    famOf (b :: c :: rest) = famSig (byteNat b) (byteNat c) (kopfN rest) := rfl

theorem famOf_cons3 (b c d : Byte) (rest : List Byte) :
    famOf (b :: c :: d :: rest) = famSig (byteNat b) (byteNat c) (byteNat d) :=
  rfl

/-! ### Signature evaluation lemmas.

    Each is closed by the same mechanical tactic: unfold `famSig`, split
    every `if`, and close each leaf by `rfl` (the right family) or by
    `omega` (the hypotheses contradict the branch). -/

/-- Mechanical evaluation of `famSig` under linear byte-class hypotheses. -/
macro "famSig_auswerten" : tactic =>
  `(tactic| (unfold famSig; repeat' (first | rfl | (exfalso; omega) | split)))

theorem famSig_sonst (n1 n2 n3 : Nat)
    (h1 : ¬ (n1 = 72 ∨ n1 = 73 ∨ n1 = 76 ∨ n1 = 77))
    (h2 : ¬ (n1 = 64 ∨ n1 = 65 ∨ n1 = 68 ∨ n1 = 69))
    (h3 : ¬ (n1 = 74 ∨ n1 = 75 ∨ n1 = 78 ∨ n1 = 79))
    (h4 : ¬ (n1 = 235 ∨ (112 ≤ n1 ∧ n1 < 128) ∨ (184 ≤ n1 ∧ n1 < 192))) :
    famSig n1 n2 n3 = .pilot := by
  famSig_auswerten

theorem famSig_rexPilot (n1 n2 n3 : Nat)
    (h1 : n1 = 72 ∨ n1 = 73 ∨ n1 = 76 ∨ n1 = 77)
    (h2 : (184 ≤ n2 ∧ n2 < 192) ∨ n2 = 1 ∨ n2 = 41 ∨ n2 = 49 ∨ n2 = 57 ∨
      ((n2 = 137 ∨ n2 = 139) ∧ 2 ≤ n3 / 64)) :
    famSig n1 n2 n3 = .pilot := by
  famSig_auswerten

theorem famSig_65Pilot (n2 n3 : Nat) (h2 : 80 ≤ n2 ∧ n2 < 96) :
    famSig 65 n2 n3 = .pilot := by
  famSig_auswerten

theorem famSig_muldiv (n1 n2 n3 : Nat)
    (h1 : n1 = 72 ∨ n1 = 73 ∨ n1 = 76 ∨ n1 = 77)
    (h2 : (n2 = 247 ∧ (n3 / 8 % 8 = 4 ∨ n3 / 8 % 8 = 6 ∨ n3 / 8 % 8 = 7)) ∨
      (n2 = 15 ∧ n3 = 175)) :
    famSig n1 n2 n3 = .muldiv := by
  famSig_auswerten

theorem famSig_shift (n1 n2 n3 : Nat) (h1 : n1 = 72 ∨ n1 = 73)
    (h2 : n2 = 193 ∨ n2 = 211) :
    famSig n1 n2 n3 = .shift := by
  famSig_auswerten

theorem famSig_narrow (n1 n2 n3 : Nat)
    (h1 : n1 = 64 ∨ n1 = 65 ∨ n1 = 68 ∨ n1 = 69)
    (h2 : n2 = 137 ∨ (n2 = 15 ∧ (n3 = 182 ∨ n3 = 190))) :
    famSig n1 n2 n3 = .narrow := by
  famSig_auswerten

theorem famSig_setcc (n1 n2 n3 : Nat) (h1 : n1 = 64 ∨ n1 = 65)
    (h2 : n2 = 15) (h3 : 144 ≤ n3 ∧ n3 < 160) :
    famSig n1 n2 n3 = .setcc := by
  famSig_auswerten

theorem famSig_cmov (n1 n2 n3 : Nat)
    (h1 : n1 = 72 ∨ n1 = 73 ∨ n1 = 76 ∨ n1 = 77)
    (h2 : n2 = 15) (h3 : 64 ≤ n3 ∧ n3 < 80) :
    famSig n1 n2 n3 = .cmov := by
  famSig_auswerten

/-- COMPACT signature classes. -/
theorem famSig_compact (n1 n2 n3 : Nat)
    (h : n1 = 235 ∨ (112 ≤ n1 ∧ n1 < 128) ∨ (184 ≤ n1 ∧ n1 < 192) ∨
      (n1 = 65 ∧ 184 ≤ n2 ∧ n2 < 192) ∨
      ((n1 = 72 ∨ n1 = 73 ∨ n1 = 76 ∨ n1 = 77) ∧
        (n2 = 199 ∨ n2 = 131 ∨ n2 = 129 ∨
          ((n2 = 137 ∨ n2 = 139) ∧ n3 / 64 < 2)))) :
    famSig n1 n2 n3 = .compact := by
  famSig_auswerten

/-- INTEGER-CORE signature classes. -/
theorem famSig_core (n1 n2 n3 : Nat)
    (h : (n1 = 74 ∨ n1 = 75 ∨ n1 = 78 ∨ n1 = 79) ∨
      ((n1 = 72 ∨ n1 = 73 ∨ n1 = 76 ∨ n1 = 77) ∧
        (n2 = 141 ∨ n2 = 33 ∨ n2 = 9 ∨ n2 = 133 ∨ n2 = 99 ∨
          (n2 = 247 ∧ (n3 / 8 % 8 = 2 ∨ n3 / 8 % 8 = 3)) ∨
          (n2 = 15 ∧ (n3 = 182 ∨ n3 = 183 ∨ n3 = 190 ∨ n3 = 191))))) :
    famSig n1 n2 n3 = .core := by
  famSig_auswerten

/-! ### Signatures forced by each family decoder (arbitrary input). -/

theorem decodeShiftOp_sig (bBit op : Nat) (rest : List Byte)
    (x : ShiftForm × List Byte) (h : decodeShiftOp bBit op rest = some x) :
    op = 193 ∨ op = 211 := by
  unfold decodeShiftOp at h
  by_cases h1 : op = 193
  · exact Or.inl h1
  · by_cases h2 : op = 211
    · exact Or.inr h2
    · simp [h1, h2] at h

/-- SHIFT signature: an accepted shift row starts 72/73 then 193/211. -/
theorem decodeShift_sig (bs : List Byte) (x : ShiftForm × List Byte)
    (h : decodeShift bs = some x) : famOf bs = .shift := by
  match bs, h with
  | [], h => simp [decodeShift] at h
  | [r], h => simp [decodeShift] at h
  | r :: op :: t, h =>
    rw [famOf_cons2]
    unfold decodeShift at h
    by_cases h72 : byteNat r = 72
    · simp only [h72] at h
      exact famSig_shift _ _ _ (Or.inl h72)
        (decodeShiftOp_sig 0 (byteNat op) t x (by simpa using h))
    · by_cases h73 : byteNat r = 73
      · simp only [h73] at h
        exact famSig_shift _ _ _ (Or.inr h73)
          (decodeShiftOp_sig 1 (byteNat op) t x (by simpa using h))
      · simp [h72, h73] at h

theorem decodeImulRex_sig (rBit bBit : Nat) (bs : List Byte)
    (x : MulDivDecodiert × List Byte) (h : decodeImulRex rBit bBit bs = some x) :
    kopfN bs = 175 := by
  match bs, h with
  | [], h => simp [decodeImulRex] at h
  | op2 :: t, h =>
    show byteNat op2 = 175
    unfold decodeImulRex at h
    by_cases h1 : byteNat op2 = 175
    · exact h1
    · simp [h1] at h

/-- The Group-3 mul/div ModRM carries digit 4, 6 or 7 (never the core's
    NOT/NEG digits 2/3), over arbitrary input. -/
theorem decodeF7Modrm_sig (bBit : Nat) (bs : List Byte)
    (x : MulDivDecodiert × List Byte) (h : decodeF7Modrm bBit bs = some x) :
    kopfN bs / 8 % 8 = 4 ∨ kopfN bs / 8 % 8 = 6 ∨ kopfN bs / 8 % 8 = 7 := by
  match bs, h with
  | [], h => simp [decodeF7Modrm] at h
  | m :: t, h =>
    show byteNat m / 8 % 8 = 4 ∨ byteNat m / 8 % 8 = 6 ∨ byteNat m / 8 % 8 = 7
    simp only [decodeF7Modrm] at h
    split at h
    · split at h <;> first | omega | simp at h
    · simp at h

theorem decodeNachRex_sig (rBit bBit : Nat) (bs : List Byte)
    (x : MulDivDecodiert × List Byte) (h : decodeNachRex rBit bBit bs = some x) :
    (kopfN bs = 247 ∧ (kopfN (bs.drop 1) / 8 % 8 = 4 ∨
      kopfN (bs.drop 1) / 8 % 8 = 6 ∨ kopfN (bs.drop 1) / 8 % 8 = 7)) ∨
      (kopfN bs = 15 ∧ kopfN (bs.drop 1) = 175) := by
  match bs, h with
  | [], h => simp [decodeNachRex] at h
  | op :: t, h =>
    show (byteNat op = 247 ∧ (kopfN t / 8 % 8 = 4 ∨ kopfN t / 8 % 8 = 6 ∨
      kopfN t / 8 % 8 = 7)) ∨ (byteNat op = 15 ∧ kopfN t = 175)
    unfold decodeNachRex at h
    by_cases h1 : byteNat op = 247
    · simp only [h1] at h
      exact Or.inl ⟨h1, decodeF7Modrm_sig bBit t x (by simpa using h)⟩
    · by_cases h2 : byteNat op = 15
      · simp only [h2] at h
        exact Or.inr ⟨h2, decodeImulRex_sig rBit bBit t x (by simpa using h)⟩
      · simp [h1, h2] at h

theorem decodeNachRexR_sig (rBit bBit : Nat) (bs : List Byte)
    (x : MulDivDecodiert × List Byte) (h : decodeNachRexR rBit bBit bs = some x) :
    kopfN bs = 15 ∧ kopfN (bs.drop 1) = 175 := by
  match bs, h with
  | [], h => simp [decodeNachRexR] at h
  | op :: t, h =>
    show byteNat op = 15 ∧ kopfN t = 175
    unfold decodeNachRexR at h
    by_cases h2 : byteNat op = 15
    · simp only [h2] at h
      exact ⟨h2, decodeImulRex_sig rBit bBit t x (by simpa using h)⟩
    · simp [h2] at h

/-- MUL/DIV signature: REX.W then 247, or REX.W then 15 175. -/
theorem decodeMulDiv_sig (bs : List Byte) (x : MulDivDecodiert × List Byte)
    (h : decodeMulDiv bs = some x) : famOf bs = .muldiv := by
  match bs, h with
  | [], h => simp [decodeMulDiv] at h
  | b :: t, h =>
    rw [famOf_cons]
    simp only [decodeMulDiv] at h
    split at h
    · rename_i hb
      exact famSig_muldiv _ _ _ (by omega) (decodeNachRex_sig 0 0 t x h)
    · rename_i hb
      exact famSig_muldiv _ _ _ (by omega) (decodeNachRex_sig 0 1 t x h)
    · rename_i hb
      exact famSig_muldiv _ _ _ (by omega)
        (Or.inr (decodeNachRexR_sig 1 0 t x h))
    · rename_i hb
      exact famSig_muldiv _ _ _ (by omega)
        (Or.inr (decodeNachRexR_sig 1 1 t x h))
    · simp at h

theorem rexNarrowBits_sig (r : Byte) (p : Nat × Nat)
    (h : rexNarrowBits r = some p) :
    byteNat r = 64 ∨ byteNat r = 65 ∨ byteNat r = 68 ∨ byteNat r = 69 := by
  unfold rexNarrowBits at h
  dsimp only at h
  split at h <;> first | omega | simp at h

theorem decodeNarrow0F_sig (rh bh : Nat) (bs : List Byte)
    (x : NarrowDec × List Byte) (h : decodeNarrow0F rh bh bs = some x) :
    kopfN bs = 182 ∨ kopfN bs = 190 := by
  match bs, h with
  | [], h => simp [decodeNarrow0F] at h
  | op :: t, h =>
    show byteNat op = 182 ∨ byteNat op = 190
    simp only [decodeNarrow0F] at h
    split at h <;> first | omega | simp at h

theorem decodeNarrowTail_sig (rh bh : Nat) (bs : List Byte)
    (x : NarrowDec × List Byte) (h : decodeNarrowTail rh bh bs = some x) :
    kopfN bs = 137 ∨ (kopfN bs = 15 ∧ (kopfN (bs.drop 1) = 182 ∨
      kopfN (bs.drop 1) = 190)) := by
  match bs, h with
  | [], h => simp [decodeNarrowTail] at h
  | b2 :: t, h =>
    show byteNat b2 = 137 ∨ (byteNat b2 = 15 ∧ (kopfN t = 182 ∨ kopfN t = 190))
    simp only [decodeNarrowTail] at h
    split at h
    · rename_i hb
      exact Or.inl hb
    · rename_i hb
      exact Or.inr ⟨hb, decodeNarrow0F_sig rh bh t x h⟩
    · simp at h

/-- NARROW signature: 64/65/68/69 then 137, or then 15 182/190. -/
theorem decodeNarrow_sig (bs : List Byte) (x : NarrowDec × List Byte)
    (h : decodeNarrow bs = some x) : famOf bs = .narrow := by
  match bs, h with
  | [], h => simp [decodeNarrow] at h
  | r :: t, h =>
    rw [famOf_cons]
    simp only [decodeNarrow] at h
    cases hr : rexNarrowBits r with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨rh, bh⟩ := p
      simp only [hr] at h
      exact famSig_narrow _ _ _ (rexNarrowBits_sig r _ hr)
        (decodeNarrowTail_sig rh bh t x h)

theorem decodeSetCCNach_sig (bBit : Nat) (p1 p2 m : Byte) (rest : List Byte)
    (x : (Bedingung × Register) × List Byte)
    (h : decodeSetCCNach bBit p1 p2 m rest = some x) :
    byteNat p1 = 15 ∧ 144 ≤ byteNat p2 ∧ byteNat p2 < 160 := by
  unfold decodeSetCCNach at h
  split at h
  · rename_i h15
    refine ⟨h15, ?_⟩
    by_cases hc : 144 ≤ byteNat p2 ∧ byteNat p2 < 160
    · exact hc
    · simp [hc] at h
  · simp at h

/-- SETCC signature: 64/65 then 15 then 144..159. -/
theorem decodeSetCC_sig (bs : List Byte)
    (x : (Bedingung × Register) × List Byte)
    (h : decodeSetCC bs = some x) : famOf bs = .setcc := by
  match bs, h with
  | [], h => simp [decodeSetCC] at h
  | [_], h => simp [decodeSetCC] at h
  | [_, _], h => simp [decodeSetCC] at h
  | [_, _, _], h => simp [decodeSetCC] at h
  | r :: p1 :: p2 :: m :: rest, h =>
    rw [famOf_cons3]
    simp only [decodeSetCC] at h
    split at h
    · rename_i hr
      obtain ⟨h1, h2⟩ := decodeSetCCNach_sig 0 p1 p2 m rest x h
      exact famSig_setcc _ _ _ (Or.inl hr) h1 h2
    · rename_i hr
      obtain ⟨h1, h2⟩ := decodeSetCCNach_sig 1 p1 p2 m rest x h
      exact famSig_setcc _ _ _ (Or.inr hr) h1 h2
    · simp at h

theorem decodeCmovNach_sig (rBit bBit : Nat) (p1 p2 m : Byte) (rest : List Byte)
    (x : (Bedingung × Register × Register) × List Byte)
    (h : decodeCmovNach rBit bBit p1 p2 m rest = some x) :
    byteNat p1 = 15 ∧ 64 ≤ byteNat p2 ∧ byteNat p2 < 80 := by
  unfold decodeCmovNach at h
  split at h
  · rename_i h15
    refine ⟨h15, ?_⟩
    by_cases hc : 64 ≤ byteNat p2 ∧ byteNat p2 < 80
    · exact hc
    · simp [hc] at h
  · simp at h

/-- CMOV signature: REX.W then 15 then 64..79. -/
theorem decodeCmov_sig (bs : List Byte)
    (x : (Bedingung × Register × Register) × List Byte)
    (h : decodeCmov bs = some x) : famOf bs = .cmov := by
  match bs, h with
  | [], h => simp [decodeCmov] at h
  | [_], h => simp [decodeCmov] at h
  | [_, _], h => simp [decodeCmov] at h
  | [_, _, _], h => simp [decodeCmov] at h
  | r :: p1 :: p2 :: m :: rest, h =>
    rw [famOf_cons3]
    simp only [decodeCmov] at h
    split at h
    · obtain ⟨h1, h2⟩ := decodeCmovNach_sig _ _ p1 p2 m rest x h
      exact famSig_cmov _ _ _ (by omega) h1 h2
    · obtain ⟨h1, h2⟩ := decodeCmovNach_sig _ _ p1 p2 m rest x h
      exact famSig_cmov _ _ _ (by omega) h1 h2
    · obtain ⟨h1, h2⟩ := decodeCmovNach_sig _ _ p1 p2 m rest x h
      exact famSig_cmov _ _ _ (by omega) h1 h2
    · obtain ⟨h1, h2⟩ := decodeCmovNach_sig _ _ p1 p2 m rest x h
      exact famSig_cmov _ _ _ (by omega) h1 h2
    · simp at h

/-- A pilot ModRM row is register-direct (mod 3) or disp32 (mod 2). -/
theorem decodeModrm_sig (rBit bBit op : Nat) (bs : List Byte)
    (x : Decodiert × List Byte) (h : decodeModrm rBit bBit op bs = some x) :
    2 ≤ kopfN bs / 64 := by
  match bs, h with
  | [], h => simp [decodeModrm] at h
  | m :: t, h =>
    show 2 ≤ byteNat m / 64
    simp only [decodeModrm] at h
    split at h <;> first | omega | simp at h

/-- PILOT opcode classes after REX.W: `B8..BF`, the four ALU rows, or
    `89`/`8B` with ModRM mode 2/3 (never the compact mode 0/1). -/
theorem decodeRex_sig (rBit bBit : Nat) (bs : List Byte)
    (x : Decodiert × List Byte) (h : decodeRex rBit bBit bs = some x) :
    (184 ≤ kopfN bs ∧ kopfN bs < 192) ∨ kopfN bs = 1 ∨ kopfN bs = 41 ∨
      kopfN bs = 49 ∨ kopfN bs = 57 ∨
      ((kopfN bs = 137 ∨ kopfN bs = 139) ∧ 2 ≤ kopfN (bs.drop 1) / 64) := by
  match bs, h with
  | [], h => simp [decodeRex] at h
  | op :: t, h =>
    show (184 ≤ byteNat op ∧ byteNat op < 192) ∨ byteNat op = 1 ∨
      byteNat op = 41 ∨ byteNat op = 49 ∨ byteNat op = 57 ∨
      ((byteNat op = 137 ∨ byteNat op = 139) ∧ 2 ≤ kopfN t / 64)
    simp only [decodeRex] at h
    split at h
    · omega
    · split at h
      · have := decodeModrm_sig rBit bBit 137 t x h
        omega
      · omega
      · omega
      · omega
      · omega
      · have := decodeModrm_sig rBit bBit 139 t x h
        omega
      · simp at h

/-- PILOT signature: no pilot row carries another family's signature. -/
theorem decode_sig (bs : List Byte) (x : Decodiert × List Byte)
    (h : decode bs = some x) : famOf bs = .pilot := by
  match bs, h with
  | [], h => simp [decode] at h
  | b :: t, h =>
    rw [famOf_cons]
    simp only [decode] at h
    split at h
    · exact famSig_sonst _ _ _ (by omega) (by omega) (by omega) (by omega)
    · exact famSig_sonst _ _ _ (by omega) (by omega) (by omega) (by omega)
    · exact famSig_sonst _ _ _ (by omega) (by omega) (by omega) (by omega)
    · exact famSig_sonst _ _ _ (by omega) (by omega) (by omega) (by omega)
    · rename_i hb
      rw [hb]
      match t, h with
      | [], h => simp at h
      | b2 :: t2, h =>
        apply famSig_65Pilot
        show 80 ≤ byteNat b2 ∧ byteNat b2 < 96
        simp only at h
        by_cases h1 : 80 ≤ byteNat b2 ∧ byteNat b2 < 88
        · omega
        · by_cases h2 : 88 ≤ byteNat b2 ∧ byteNat b2 < 96
          · omega
          · simp [h1, h2] at h
    · exact famSig_rexPilot _ _ _ (by omega) (decodeRex_sig 0 0 t x h)
    · exact famSig_rexPilot _ _ _ (by omega) (decodeRex_sig 0 1 t x h)
    · exact famSig_rexPilot _ _ _ (by omega) (decodeRex_sig 1 0 t x h)
    · exact famSig_rexPilot _ _ _ (by omega) (decodeRex_sig 1 1 t x h)
    · rename_i n hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hn9
      by_cases h1 : 80 ≤ byteNat b ∧ byteNat b < 88
      · exact famSig_sonst _ _ _ (by omega) (by omega) (by omega) (by omega)
      · by_cases h2 : 88 ≤ byteNat b ∧ byteNat b < 96
        · exact famSig_sonst _ _ _ (by omega) (by omega) (by omega) (by omega)
        · simp [h1, h2] at h

/-! ### The two new families: compact forms and the integer core. -/

/-- After a compact REX.W: `C7`/`83`/`81`, or `89`/`8B` with mode 0/1. -/
theorem decodeCRex_sig (rBit bBit : Nat) (bs : List Byte)
    (x : CompactDecodiert × List Byte) (h : decodeCRex rBit bBit bs = some x) :
    kopfN bs = 199 ∨ kopfN bs = 131 ∨ kopfN bs = 129 ∨
      ((kopfN bs = 137 ∨ kopfN bs = 139) ∧ kopfN (bs.drop 1) / 64 < 2) := by
  match bs, h with
  | [], h => simp [decodeCRex] at h
  | op :: t, h =>
    show byteNat op = 199 ∨ byteNat op = 131 ∨ byteNat op = 129 ∨
      ((byteNat op = 137 ∨ byteNat op = 139) ∧ kopfN t / 64 < 2)
    simp only [decodeCRex] at h
    split at h
    · omega
    · omega
    · omega
    · match t, h with
      | [], h => simp at h
      | m :: t2, h =>
        show _ ∨ _ ∨ _ ∨ (_ ∧ byteNat m / 64 < 2)
        simp only at h
        split at h <;> first | omega | simp at h
    · match t, h with
      | [], h => simp at h
      | m :: t2, h =>
        show _ ∨ _ ∨ _ ∨ (_ ∧ byteNat m / 64 < 2)
        simp only at h
        split at h <;> first | omega | simp at h
    · simp at h

/-- COMPACT signature over arbitrary input. (`decodeC` is unfolded once and
    its list match reduced by `simp only`; its numeric-literal opcode
    match is then split, never handed to `simp [decodeC]`, whose equation
    lemmas for that match exceed the heartbeat budget.) -/
theorem decodeC_sig (bs : List Byte) (x : CompactDecodiert × List Byte)
    (h : decodeC bs = some x) : famOf bs = .compact := by
  rcases bs with _ | ⟨b, _ | ⟨b2, t⟩⟩
  · cases h
  · rw [famOf_cons]
    apply famSig_compact
    unfold decodeC at h
    simp only at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | omega
      | (simp [decodeCRex] at h; done)
  · rw [famOf_cons2]
    apply famSig_compact
    unfold decodeC at h
    simp only at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | omega
      | (have := decodeCRex_sig _ _ _ x h
         simp only [kopfN_cons, List.drop_succ_cons, List.drop_zero] at this
         omega)

theorem rexCoreBits_sig (r : Byte) (p : Nat × Nat × Nat)
    (h : rexCoreBits r = some p) : 72 ≤ byteNat r ∧ byteNat r < 80 := by
  unfold rexCoreBits at h
  dsimp only at h
  split at h
  · assumption
  · simp at h

theorem decodeCoreF7_sig (rh bh : Nat) (bs : List Byte)
    (x : CoreDecodiert × List Byte) (h : decodeCoreF7 rh bh bs = some x) :
    kopfN bs / 8 % 8 = 2 ∨ kopfN bs / 8 % 8 = 3 := by
  match bs, h with
  | [], h => simp [decodeCoreF7] at h
  | m :: t, h =>
    show byteNat m / 8 % 8 = 2 ∨ byteNat m / 8 % 8 = 3
    simp only [decodeCoreF7] at h
    split at h
    · split at h <;> first | omega | simp at h
    · simp at h

theorem decodeCore0F_sig (rh bh : Nat) (bs : List Byte)
    (x : CoreDecodiert × List Byte) (h : decodeCore0F rh bh bs = some x) :
    kopfN bs = 182 ∨ kopfN bs = 183 ∨ kopfN bs = 190 ∨ kopfN bs = 191 := by
  match bs, h with
  | [], h => simp [decodeCore0F] at h
  | [_], h => simp [decodeCore0F] at h
  | op2 :: m :: t, h =>
    show byteNat op2 = 182 ∨ byteNat op2 = 183 ∨ byteNat op2 = 190 ∨
      byteNat op2 = 191
    simp only [decodeCore0F] at h
    split at h
    · split at h
      · split at h <;> first | omega | simp at h
      · simp at h
    · simp at h

/-- After the core REX prefix: LEA, a register-register logic row, NOT/NEG
    (`F7` digit 2/3), a `0F` extension row or MOVSXD. -/
theorem decodeCoreTail_sig (rh xh bh : Nat) (bs : List Byte)
    (x : CoreDecodiert × List Byte) (h : decodeCoreTail rh xh bh bs = some x) :
    kopfN bs = 141 ∨ kopfN bs = 33 ∨ kopfN bs = 9 ∨ kopfN bs = 133 ∨
      kopfN bs = 99 ∨
      (kopfN bs = 247 ∧ (kopfN (bs.drop 1) / 8 % 8 = 2 ∨
        kopfN (bs.drop 1) / 8 % 8 = 3)) ∨
      (kopfN bs = 15 ∧ (kopfN (bs.drop 1) = 182 ∨ kopfN (bs.drop 1) = 183 ∨
        kopfN (bs.drop 1) = 190 ∨ kopfN (bs.drop 1) = 191)) := by
  match bs, h with
  | [], h => simp [decodeCoreTail] at h
  | op :: t, h =>
    show byteNat op = 141 ∨ byteNat op = 33 ∨ byteNat op = 9 ∨
      byteNat op = 133 ∨ byteNat op = 99 ∨
      (byteNat op = 247 ∧ (kopfN t / 8 % 8 = 2 ∨ kopfN t / 8 % 8 = 3)) ∨
      (byteNat op = 15 ∧ (kopfN t = 182 ∨ kopfN t = 183 ∨ kopfN t = 190 ∨
        kopfN t = 191))
    simp only [decodeCoreTail] at h
    by_cases h141 : byteNat op = 141
    · exact Or.inl h141
    · have hb : (byteNat op == 141) = false := by simpa using h141
      rw [if_neg (by simp [hb])] at h
      split at h
      · simp at h
      · split at h
        · omega
        · omega
        · omega
        · have := decodeCoreF7_sig rh bh t x h
          omega
        · have := decodeCore0F_sig rh bh t x h
          omega
        · omega
        · simp at h

/-- INTEGER-CORE signature over arbitrary input. -/
theorem decodeCore_sig (bs : List Byte) (x : CoreDecodiert × List Byte)
    (h : decodeCore bs = some x) : famOf bs = .core := by
  match bs, h with
  | [], h => simp [decodeCore] at h
  | r :: t, h =>
    rw [famOf_cons]
    apply famSig_core
    simp only [decodeCore] at h
    split at h
    · simp at h
    · rename_i p hr
      have h1 := rexCoreBits_sig r _ hr
      have h2 := decodeCoreTail_sig _ _ _ t x h
      omega

/-! ### Disjointness and the unified decoder. -/

/-- Every family decoder forces its own signature. -/
theorem decF_sig (F : Fam) (bs : List Byte) (x : InstrDecoded × List Byte)
    (h : decF F bs = some x) : famOf bs = F := by
  cases F with
  | pilot =>
    simp only [decF] at h
    split at h
    · rename_i hy
      exact decode_sig bs _ hy
    · simp at h
  | muldiv =>
    simp only [decF] at h
    split at h
    · rename_i hy
      exact decodeMulDiv_sig bs _ hy
    · simp at h
  | shift =>
    simp only [decF] at h
    split at h
    · rename_i hy
      exact decodeShift_sig bs _ hy
    · simp at h
  | narrow =>
    simp only [decF] at h
    split at h
    · rename_i hy
      exact decodeNarrow_sig bs _ hy
    · simp at h
  | setcc =>
    simp only [decF] at h
    split at h
    · rename_i hy
      exact decodeSetCC_sig bs _ hy
    · simp at h
  | cmov =>
    simp only [decF] at h
    split at h
    · rename_i hy
      exact decodeCmov_sig bs _ hy
    · simp at h
  | compact =>
    simp only [decF] at h
    split at h
    · rename_i hy
      exact decodeC_sig bs _ hy
    · simp at h
  | core =>
    simp only [decF] at h
    split at h
    · rename_i hy
      exact decodeCore_sig bs _ hy
    · simp at h

/-- DISJOINTNESS: over an ARBITRARY byte string at most one family decoder
    accepts. -/
theorem familien_disjunkt (F G : Fam) (bs : List Byte)
    (x y : InstrDecoded × List Byte)
    (hF : decF F bs = some x) (hG : decF G bs = some y) : F = G := by
  rw [← decF_sig F bs x hF, ← decF_sig G bs y hG]

/-- A family decoder only ever yields its own family's instructions. -/
theorem decF_famI (F : Fam) (bs : List Byte) (x : InstrDecoded × List Byte)
    (h : decF F bs = some x) : famI x.1.instr = F := by
  cases F with
  | pilot =>
    simp only [decF] at h
    split at h <;> first | (cases h; rfl) | simp at h
  | muldiv =>
    simp only [decF] at h
    split at h <;> first | (cases h; rfl) | simp at h
  | shift =>
    simp only [decF] at h
    split at h <;> first | (cases h; rfl) | simp at h
  | narrow =>
    simp only [decF] at h
    split at h <;> first | (cases h; rfl) | simp at h
  | setcc =>
    simp only [decF] at h
    split at h <;> first | (cases h; rfl) | simp at h
  | cmov =>
    simp only [decF] at h
    split at h <;> first | (cases h; rfl) | simp at h
  | compact =>
    simp only [decF] at h
    split at h <;> first | (cases h; rfl) | simp at h
  | core =>
    simp only [decF] at h
    split at h <;> first | (cases h; rfl) | simp at h

/-- The first accepting family in any list containing the accepting family
    is that family: by disjointness no earlier family accepts. -/
theorem erstesF_von (Fs : List Fam) (F : Fam) (bs : List Byte)
    (x : InstrDecoded × List Byte) (hmem : F ∈ Fs)
    (hF : decF F bs = some x) : erstesF Fs bs = some x := by
  induction Fs with
  | nil => simp at hmem
  | cons G Gs ih =>
    simp only [erstesF]
    cases hG : decF G bs with
    | some y =>
      have hFG : F = G := familien_disjunkt F G bs x y hF hG
      subst hFG
      rw [hF] at hG
      cases hG
      rfl
    | none =>
      apply ih
      cases List.mem_cons.mp hmem with
      | inl he =>
        subst he
        rw [hF] at hG
        cases hG
      | inr ht => exact ht

/-- Whatever a family decoder accepts, the unified decoder answers the same:
    the priority order of `alleFam` never matters. -/
theorem decodeI_von_fam (F : Fam) (bs : List Byte)
    (x : InstrDecoded × List Byte) (hF : decF F bs = some x) :
    decodeI bs = some x :=
  erstesF_von alleFam F bs x (mem_alleFam F) hF

/-- Every unified decode comes from exactly the family of the signature. -/
theorem erstesF_quelle (Fs : List Fam) (bs : List Byte)
    (x : InstrDecoded × List Byte) (h : erstesF Fs bs = some x) :
    ∃ F, decF F bs = some x := by
  induction Fs with
  | nil => simp [erstesF] at h
  | cons G Gs ih =>
    simp only [erstesF] at h
    cases hG : decF G bs with
    | some y =>
      rw [hG] at h
      cases h
      exact ⟨G, hG⟩
    | none =>
      rw [hG] at h
      exact ih h

/-- UNIQUENESS: a unified decode is exactly the decode of the family named
    by the byte signature, and its instruction belongs to that family. -/
theorem decodeI_eindeutig (bs : List Byte) (x : InstrDecoded × List Byte)
    (h : decodeI bs = some x) :
    decF (famOf bs) bs = some x ∧ famI x.1.instr = famOf bs := by
  obtain ⟨F, hF⟩ := erstesF_quelle alleFam bs x h
  have hs := decF_sig F bs x hF
  subst hs
  exact ⟨hF, decF_famI _ bs x hF⟩

/-- Canonical encodings of one family are refused by every other family. -/
theorem decF_fremd_encodeI (i : Instr) (G : Fam) (hk : kanonischI i = true)
    (hG : G ≠ famI i) (suffix : List Byte) :
    decF G (encodeI i ++ suffix) = none := by
  cases h : decF G (encodeI i ++ suffix) with
  | none => rfl
  | some y =>
    exact absurd (familien_disjunkt G (famI i) _ y _ h
      (decF_encodeI i hk suffix)) hG

/-! ## 4. Round trip and length agreement. -/

/-- ROUND TRIP: the unified decoder inverts the unified encoder on every
    canonical instruction, over any suffix, with the encoding length as
    decoded length. -/
theorem decodeI_encodeI (i : Instr) (hk : kanonischI i = true)
    (suffix : List Byte) :
    decodeI (encodeI i ++ suffix) = some (canonI i, suffix) :=
  decodeI_von_fam (famI i) _ _ (decF_encodeI i hk suffix)

/-- LENGTH AGREEMENT on canonical bytes: consumed length plus rest is the
    input, within 1..15. -/
theorem decodeI_encodeI_laenge (i : Instr) (hk : kanonischI i = true)
    (suffix : List Byte) :
    ∃ (n : Nat) (rest : List Byte),
      decodeI (encodeI i ++ suffix) = some (⟨i, n⟩, rest) ∧
        n + rest.length = (encodeI i ++ suffix).length ∧
        1 ≤ n ∧ n ≤ 15 :=
  ⟨(encodeI i).length, suffix, decodeI_encodeI i hk suffix,
    by rw [List.length_append], (encodeI_len i).1, (encodeI_len i).2⟩

/-! ### Consumed length over ARBITRARY input. -/

theorem decodeShiftModrm_rest (bBit : Nat) (bs : List Byte) (r : ShiftRichtung)
    (dst : Register) (rest : List Byte)
    (h : decodeShiftModrm bBit bs = some (r, dst, rest)) :
    bs.length = rest.length + 1 := by
  match bs, h with
  | [], h => simp [decodeShiftModrm] at h
  | m :: t, h =>
    simp only [decodeShiftModrm] at h
    split at h
    · split at h
      · cases h
        rfl
      · simp at h
    · simp at h

theorem decodeShiftOp_laenge (bBit op : Nat) (bs : List Byte) (f : ShiftForm)
    (rest : List Byte) (h : decodeShiftOp bBit op bs = some (f, rest)) :
    bs.length + 2 = shiftLaenge f + rest.length := by
  unfold decodeShiftOp at h
  dsimp only at h
  split at h
  · split at h
    · rename_i r dst i rest' hm
      cases h
      have := decodeShiftModrm_rest bBit bs r dst (i :: rest) hm
      simp only [List.length_cons] at this
      simp only [shiftLaenge]
      omega
    · simp at h
  · split at h
    · split at h
      · rename_i r dst rest' hm
        cases h
        have := decodeShiftModrm_rest bBit bs r dst rest hm
        simp only [shiftLaenge]
        omega
      · simp at h
    · simp at h

theorem decodeShift_laenge (bs : List Byte) (f : ShiftForm) (rest : List Byte)
    (h : decodeShift bs = some (f, rest)) :
    shiftLaenge f + rest.length = bs.length := by
  match bs, h with
  | [], h => simp [decodeShift] at h
  | [r], h => simp [decodeShift] at h
  | r :: op :: t, h =>
    unfold decodeShift at h
    by_cases h72 : byteNat r = 72
    · simp only [h72] at h
      have := decodeShiftOp_laenge 0 (byteNat op) t f rest (by simpa using h)
      simp only [List.length_cons]
      omega
    · by_cases h73 : byteNat r = 73
      · simp only [h73] at h
        have := decodeShiftOp_laenge 1 (byteNat op) t f rest (by simpa using h)
        simp only [List.length_cons]
        omega
      · simp [h72, h73] at h

theorem decodeSetCCNach_rest (bBit : Nat) (p1 p2 m : Byte) (rest : List Byte)
    (v : Bedingung × Register) (rest' : List Byte)
    (h : decodeSetCCNach bBit p1 p2 m rest = some (v, rest')) : rest' = rest := by
  unfold decodeSetCCNach at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm)
    | simp at h

theorem decodeSetCC_verbraucht (bs : List Byte) (v : Bedingung × Register)
    (rest : List Byte) (h : decodeSetCC bs = some (v, rest)) :
    4 + rest.length = bs.length := by
  match bs, h with
  | [], h => simp [decodeSetCC] at h
  | [_], h => simp [decodeSetCC] at h
  | [_, _], h => simp [decodeSetCC] at h
  | [_, _, _], h => simp [decodeSetCC] at h
  | r :: p1 :: p2 :: m :: t, h =>
    simp only [decodeSetCC] at h
    split at h
    · have := decodeSetCCNach_rest 0 p1 p2 m t v rest h
      subst this
      simp only [List.length_cons]
      omega
    · have := decodeSetCCNach_rest 1 p1 p2 m t v rest h
      subst this
      simp only [List.length_cons]
      omega
    · simp at h

theorem decodeCmovNach_rest (rBit bBit : Nat) (p1 p2 m : Byte)
    (rest : List Byte) (v : Bedingung × Register × Register)
    (rest' : List Byte)
    (h : decodeCmovNach rBit bBit p1 p2 m rest = some (v, rest')) :
    rest' = rest := by
  unfold decodeCmovNach at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm)
    | simp at h

theorem decodeCmov_verbraucht (bs : List Byte) (v : Bedingung × Register × Register)
    (rest : List Byte) (h : decodeCmov bs = some (v, rest)) :
    4 + rest.length = bs.length := by
  match bs, h with
  | [], h => simp [decodeCmov] at h
  | [_], h => simp [decodeCmov] at h
  | [_, _], h => simp [decodeCmov] at h
  | [_, _, _], h => simp [decodeCmov] at h
  | r :: p1 :: p2 :: m :: t, h =>
    simp only [decodeCmov] at h
    split at h <;>
      first
      | (have := decodeCmovNach_rest _ _ p1 p2 m t v rest h
         subst this
         simp only [List.length_cons]
         omega)
      | simp at h

/-! ### Consumed length of the two new families over ARBITRARY input.

    `CompactForms.lean` and `IntegerCore.lean` prove lengths only for
    encoder output (their CUTS). The arbitrary-input facts the unified
    decoder needs are proved here, layer by layer, from the decoders
    themselves (reusing `parseLe32_len` from `DecodingCoverage.lean`). -/

set_option hygiene false in
/-- Leaf discharge of the arbitrary-input length lemmas: a refused leaf,
    a constructor clash, or an accepted leaf whose consumed bytes are
    counted (with `parseLe32_len` for a 32-bit immediate). -/
macro "blatt_laenge" : tactic => `(tactic| first
  | (simp at h; done)
  | (simp only [Option.some.injEq, Prod.mk.injEq] at h
     obtain ⟨rfl, rfl⟩ := h
     dsimp only
     (try have := parseLe32_len _ _ _ ‹parseLe32 _ = some _›)
     (try simp only [List.length_cons, List.length_nil, true_and, and_true] at *) <;>
     omega))

theorem decodeMemC_len (isLoad mod01 : Bool) (rBit bBit reg rm : Nat)
    (bs : List Byte) (d : CompactDecodiert) (rest : List Byte)
    (h : decodeMemC isLoad mod01 rBit bBit reg rm bs = some (d, rest)) :
    d.laenge + rest.length = bs.length + 3 ∧ 3 ≤ d.laenge ∧ d.laenge ≤ 5 := by
  rcases bs with _ | ⟨b, _ | ⟨c, t⟩⟩ <;> simp only [decodeMemC] at h <;>
    (repeat' split at h)
  all_goals blatt_laenge

theorem decodeCRex_len (rBit bBit : Nat) (bs : List Byte) (d : CompactDecodiert)
    (rest : List Byte) (h : decodeCRex rBit bBit bs = some (d, rest)) :
    d.laenge + rest.length = bs.length + 1 ∧ 3 ≤ d.laenge ∧ d.laenge ≤ 7 := by
  rcases bs with _ | ⟨op, _ | ⟨m, _ | ⟨c, t⟩⟩⟩ <;> simp only [decodeCRex] at h <;>
    (repeat' split at h)
  all_goals first
    | blatt_laenge
    | (have := decodeMemC_len _ _ _ _ _ _ _ d rest h
       simp only [List.length_cons, List.length_nil] at *
       omega)

theorem decodeC_verbraucht (bs : List Byte) (d : CompactDecodiert)
    (rest : List Byte) (h : decodeC bs = some (d, rest)) :
    d.laenge + rest.length = bs.length ∧ 1 ≤ d.laenge ∧ d.laenge ≤ 15 := by
  rcases bs with _ | ⟨b, _ | ⟨b2, t⟩⟩
  · cases h
  · unfold decodeC at h
    simp only at h
    repeat' split at h
    all_goals first
      | blatt_laenge
      | (have := decodeCRex_len _ _ _ d rest h
         simp only [List.length_cons, List.length_nil] at *
         omega)
  · unfold decodeC at h
    simp only at h
    repeat' split at h
    all_goals first
      | blatt_laenge
      | (have := decodeCRex_len _ _ _ d rest h
         simp only [List.length_cons] at *
         omega)

theorem decodeCoreRegReg_len (mk : Register → Register → CoreBefehl) (rh bh : Nat)
    (bs : List Byte) (d : CoreDecodiert) (rest : List Byte)
    (h : decodeCoreRegReg mk rh bh bs = some (d, rest)) :
    d.laenge + rest.length = bs.length + 2 ∧ d.laenge = 3 := by
  rcases bs with _ | ⟨m, t⟩ <;> unfold decodeCoreRegReg at h <;> simp only at h <;>
    (repeat' split at h)
  all_goals blatt_laenge

theorem decodeCoreF7_len (rh bh : Nat) (bs : List Byte) (d : CoreDecodiert)
    (rest : List Byte) (h : decodeCoreF7 rh bh bs = some (d, rest)) :
    d.laenge + rest.length = bs.length + 2 ∧ d.laenge = 3 := by
  rcases bs with _ | ⟨m, t⟩ <;> unfold decodeCoreF7 at h <;> simp only at h <;>
    (repeat' split at h)
  all_goals blatt_laenge

theorem decodeCore0F_len (rh bh : Nat) (bs : List Byte) (d : CoreDecodiert)
    (rest : List Byte) (h : decodeCore0F rh bh bs = some (d, rest)) :
    d.laenge + rest.length = bs.length + 2 ∧ d.laenge = 4 := by
  rcases bs with _ | ⟨op2, _ | ⟨m, t⟩⟩ <;> unfold decodeCore0F at h <;>
    simp only at h <;> (repeat' split at h)
  all_goals blatt_laenge

theorem decodeCoreMovsxd_len (rh bh : Nat) (bs : List Byte) (d : CoreDecodiert)
    (rest : List Byte) (h : decodeCoreMovsxd rh bh bs = some (d, rest)) :
    d.laenge + rest.length = bs.length + 2 ∧ d.laenge = 3 := by
  rcases bs with _ | ⟨m, t⟩ <;> unfold decodeCoreMovsxd at h <;> simp only at h <;>
    (repeat' split at h)
  all_goals blatt_laenge

theorem decodeCoreLea_len (rh xh bh : Nat) (bs : List Byte) (d : CoreDecodiert)
    (rest : List Byte) (h : decodeCoreLea rh xh bh bs = some (d, rest)) :
    d.laenge + rest.length = bs.length + 2 ∧ d.laenge = 8 := by
  rcases bs with _ | ⟨modrm, _ | ⟨sib, t⟩⟩ <;> unfold decodeCoreLea at h <;>
    simp only at h <;> (repeat' split at h)
  all_goals blatt_laenge

theorem decodeCoreTail_len (rh xh bh : Nat) (bs : List Byte) (d : CoreDecodiert)
    (rest : List Byte) (h : decodeCoreTail rh xh bh bs = some (d, rest)) :
    d.laenge + rest.length = bs.length + 1 ∧ 3 ≤ d.laenge ∧ d.laenge ≤ 8 := by
  rcases bs with _ | ⟨op, t⟩
  · cases h
  · unfold decodeCoreTail at h
    simp only at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (have := decodeCoreLea_len _ _ _ t d rest h
         simp only [List.length_cons] at *
         omega)
      | (have := decodeCoreRegReg_len _ _ _ t d rest h
         simp only [List.length_cons] at *
         omega)
      | (have := decodeCoreF7_len _ _ t d rest h
         simp only [List.length_cons] at *
         omega)
      | (have := decodeCore0F_len _ _ t d rest h
         simp only [List.length_cons] at *
         omega)
      | (have := decodeCoreMovsxd_len _ _ t d rest h
         simp only [List.length_cons] at *
         omega)

theorem decodeCore_verbraucht (bs : List Byte) (d : CoreDecodiert)
    (rest : List Byte) (h : decodeCore bs = some (d, rest)) :
    d.laenge + rest.length = bs.length ∧ 1 ≤ d.laenge ∧ d.laenge ≤ 15 := by
  rcases bs with _ | ⟨r, t⟩
  · cases h
  · unfold decodeCore at h
    simp only at h
    split at h
    · simp at h
    · have := decodeCoreTail_len _ _ _ t d rest h
      simp only [List.length_cons]
      omega

/-- CONSUMED-LENGTH AGREEMENT over ARBITRARY input: every successful unified
    decode consumes exactly its stated length within 1..15. -/
theorem decodeI_verbraucht (bs : List Byte) (d : InstrDecoded)
    (rest : List Byte) (h : decodeI bs = some (d, rest)) :
    d.laenge + rest.length = bs.length ∧ 1 ≤ d.laenge ∧ d.laenge ≤ 15 := by
  obtain ⟨hF, _⟩ := decodeI_eindeutig bs (d, rest) h
  generalize famOf bs = F at hF
  cases F with
  | pilot =>
    simp only [decF] at hF
    split at hF
    · rename_i y r hy
      obtain ⟨h1, _, h2, h3⟩ := decode_verbraucht_praefix bs y r hy
      cases hF
      exact ⟨h1, h2, h3⟩
    · simp at hF
  | muldiv =>
    simp only [decF] at hF
    split at hF
    · rename_i y r hy
      have := decodeMulDiv_len_ok bs y r hy
      cases hF
      exact this
    · simp at hF
  | shift =>
    simp only [decF] at hF
    split at hF
    · rename_i f r hy
      have := decodeShift_laenge bs f r hy
      cases hF
      refine ⟨this, ?_, ?_⟩ <;> cases f <;> simp [shiftLaenge]
    · simp at hF
  | narrow =>
    simp only [decF] at hF
    split at hF
    · rename_i y r hy
      have := decodeNarrow_consumes bs y r hy
      cases hF
      exact this
    · simp at hF
  | setcc =>
    simp only [decF] at hF
    split at hF
    · rename_i c dst r hy
      have := decodeSetCC_verbraucht bs _ _ hy
      cases hF
      exact ⟨this, show 1 ≤ 4 from by omega, show 4 ≤ 15 from by omega⟩
    · simp at hF
  | cmov =>
    simp only [decF] at hF
    split at hF
    · rename_i c dst src r hy
      have := decodeCmov_verbraucht bs _ _ hy
      cases hF
      exact ⟨this, show 1 ≤ 4 from by omega, show 4 ≤ 15 from by omega⟩
    · simp at hF
  | compact =>
    simp only [decF] at hF
    split at hF
    · rename_i y r hy
      have := decodeC_verbraucht bs y r hy
      cases hF
      exact this
    · simp at hF
  | core =>
    simp only [decF] at hF
    split at hF
    · rename_i y r hy
      have := decodeCore_verbraucht bs y r hy
      cases hF
      exact this
    · simp at hF

/-! ## 5. Adding a further family: four mechanical steps.

    A new family `F` with an EXISTING instruction type `FBefehl`, step
    `fSchritt : FDec → Zustand → Option Zustand` over the same `Zustand`,
    encoder `encodeF`, decoder `decodeF` and round trip `roundtripF` joins
    the unified machine without touching any family file:

    1. CONSTRUCTOR. Add `| f (b : FBefehl)` to `Instr` and a tag `f` to
       `Fam`; extend `famI`. (If `F` needs a canonicity side condition, add
       its arm to `kanonischI`.)
    2. STEP DELEGATION. Add the arm `| ⟨.f b, l⟩, s => fSchritt ⟨b, l⟩ s` to
       `stepI` (and the `.ok`/`.misslungen` arm to `stepIE`), plus the
       one-line equation `stepI_f : … := rfl`. Never re-state `F`'s
       semantics. In `ISAExecution.lean` add the `F` arm of `stepI_rahmen`
       (memory protection and RIP advance, from `F`'s own frame lemmas).
    3. CODEC DELEGATION. Add `| .f b => encodeF b` to `encodeI`, the arm
       `| .f, bs => match decodeF bs with …` to `decF`, `.f` to `alleFam`,
       and the `F` arms of `encodeI_len`, `decF_encodeI` (from
       `roundtripF`) and `decodeI_verbraucht` (from `F`'s arbitrary-input
       length lemma).
    4. DISJOINTNESS CASE. Read `F`'s accepted first bytes off `decodeF`,
       give them a branch of `famSig` that no existing signature reaches,
       prove `decodeF_sig : decodeF bs = some x → famOf bs = .f` and add
       the arm to `decF_sig`. If the bytes of `F` genuinely OVERLAP an
       existing family (some byte string accepted by both decoders), the
       signature proof fails at exactly that byte class: record the
       concrete bytes as a finding and decide a priority rule instead
       (then `decodeI_von_fam` holds only for the winning family and needs
       the loser's refusal as a premise).
    Everything else -- `decodeI_von_fam`, `decodeI_encodeI`,
    `decodeI_eindeutig`, `byteschrittI_kanonisch`, `laufBytesI_spur`,
    `laufBytesI_layout` -- is generic in the family list and needs no edit.
-/

/- CUTS (what is NOT proved here):
   - Families left OUT because they need state beyond `Zustand`: scalar
     SSE2 double (`ScalarFloat.fpSchritt` runs on `FpZustand` = `Zustand`
     plus the XMM file and the FP control context), packed vector
     (`VectorCodec.stepVector` on `FpZustand` plus a readiness profile) and
     LOCK/MFENCE (`LockedOps.lockSchritt` on the TSO state `TSOZustand`, no
     byte codec at all). Joining them needs ONE extended state with the
     embedding of `Zustand`; no such state is invented here.
   - The shift/logic family contributes only its SHIFT rows: `ShiftLogic`
     defines AND/OR/NOT/NEG value helpers but no instruction form, step or
     codec, so there is nothing to delegate to.
   - `stepI` collapses the mul/div hardware trap (#DE) into `none`;
     `stepIE` keeps the trap distinct and `stepIE_halt_nur_muldiv` proves
     it is the only trapping family. No `hardware` stop class
     correspondence is claimed.
   - Canonicity is a side condition only for the shift immediate
     (`imm8 : Nat` above 255 has no encoding: `encodeShift` truncates and the
     decoder returns the truncated count -- see the probe in
     `ISAWitnesses.lean`).
   - The disjointness theorem is over the eight admitted family decoders
     (seven families, cond counted twice). Joining CompactForms and
     IntegerCore changed `famSig` and STRENGTHENED the helper signature
     lemmas (`decodeNachRex_sig` now also pins the Group-3 digit,
     `decodeRex_sig` pins the pilot opcode set and the ModRM mode of
     `89`/`8B`); `famSig_sonst`/`famSig_rexPilot`/`famSig_muldiv` take the
     correspondingly sharper premises. The main theorems keep their
     statements.
   - Integer-core encodings were previously refused by `decodeI`: one old
     poison probe (`48 0F B6 C1`, REX.W MOVZX) now decodes, correctly, as
     `movzx64From8 rax rcx`; `ISAWitnesses.lean` records the change.
     It says nothing about bytes NO family accepts (they are refused) and
     nothing about x86 instructions outside the selected subset.
   - No hardware correspondence: decoding and stepping agree with the
     family models, not with silicon; no TSO, no concurrency, no cost.
-/

#print axioms stepI_eq_stepIE
#print axioms stepIE_halt_nur_muldiv
#print axioms stepI_pilot
#print axioms stepI_muldiv
#print axioms stepI_shift
#print axioms stepI_narrow
#print axioms stepI_setcc
#print axioms stepI_cmov
#print axioms stepI_compact
#print axioms stepI_core
#print axioms laufI_append
#print axioms laufI_pilot
#print axioms mem_alleFam
#print axioms encodeC_len
#print axioms encodeI_len
#print axioms laengeOk_encodeI
#print axioms decF_encodeI
#print axioms kopfN_cons
#print axioms famOf_cons
#print axioms famOf_cons2
#print axioms famOf_cons3
#print axioms famSig_sonst
#print axioms famSig_rexPilot
#print axioms famSig_65Pilot
#print axioms famSig_muldiv
#print axioms famSig_shift
#print axioms famSig_narrow
#print axioms famSig_setcc
#print axioms famSig_cmov
#print axioms famSig_compact
#print axioms famSig_core
#print axioms decodeShiftOp_sig
#print axioms decodeShift_sig
#print axioms decodeImulRex_sig
#print axioms decodeF7Modrm_sig
#print axioms decodeNachRex_sig
#print axioms decodeNachRexR_sig
#print axioms decodeMulDiv_sig
#print axioms rexNarrowBits_sig
#print axioms decodeNarrow0F_sig
#print axioms decodeNarrowTail_sig
#print axioms decodeNarrow_sig
#print axioms decodeSetCCNach_sig
#print axioms decodeSetCC_sig
#print axioms decodeCmovNach_sig
#print axioms decodeCmov_sig
#print axioms decodeModrm_sig
#print axioms decodeRex_sig
#print axioms decode_sig
#print axioms decodeCRex_sig
#print axioms decodeC_sig
#print axioms rexCoreBits_sig
#print axioms decodeCoreF7_sig
#print axioms decodeCore0F_sig
#print axioms decodeCoreTail_sig
#print axioms decodeCore_sig
#print axioms decF_sig
#print axioms familien_disjunkt
#print axioms decF_famI
#print axioms erstesF_von
#print axioms decodeI_von_fam
#print axioms erstesF_quelle
#print axioms decodeI_eindeutig
#print axioms decF_fremd_encodeI
#print axioms decodeI_encodeI
#print axioms decodeI_encodeI_laenge
#print axioms decodeShiftModrm_rest
#print axioms decodeShiftOp_laenge
#print axioms decodeShift_laenge
#print axioms decodeSetCCNach_rest
#print axioms decodeSetCC_verbraucht
#print axioms decodeCmovNach_rest
#print axioms decodeCmov_verbraucht
#print axioms decodeMemC_len
#print axioms decodeCRex_len
#print axioms decodeC_verbraucht
#print axioms decodeCoreRegReg_len
#print axioms decodeCoreF7_len
#print axioms decodeCore0F_len
#print axioms decodeCoreMovsxd_len
#print axioms decodeCoreLea_len
#print axioms decodeCoreTail_len
#print axioms decodeCore_verbraucht
#print axioms decodeI_verbraucht

end Gabbro.Grammatik.X86
