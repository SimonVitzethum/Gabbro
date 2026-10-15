/-
  File:      Grammatik/X86/SystemDecode.lean
  Subject:   Byte decoder rows for the system and privileged instructions.

  Lane 1365: byte decode of what `HwSystemForms.lean` models but the
  capstone chain cannot read (report 1339: IRET is a decode gap, not a
  semantics gap). Decoder (`sysDecode`) plus encoder (`sysEncode`,
  round trip), the lowered event (`sysEreignisOfRow`), the `HwAdapter`
  plug (`adapterSysDecode`) in the style of `HwMulDivWidth.lean`, and
  the extended chain (`kapDecodeSys`) over `HwKapsteinDecoder.lean`
  with exact agreement on every byte string the old chain decodes.
  The ten modelled forms reuse the accepted `SysFormArt` evaluator
  unchanged (never redefined); the nine deferred rows decode to
  explicit refusals (no accepted evaluator exists for them).
-/
import Grammatik.X86.Hw.Familien.HwSystemForms
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder

namespace Gabbro.Grammatik.X86

/-- Deferred system rows: real opcodes with no accepted evaluator.
    They decode (bytes are pinned) but lower to `none`. -/
inductive SysExtra where
  | int3 | int1 | cld | std | rdtscp | xgetbv | rdmsr | wrmsr | rdpmc
  deriving DecidableEq, Repr

/-- One decoded system row: the nine fixed modelled forms, INT with
    its vector byte, or a deferred extra. `.iret` covers IRET (CF)
    and IRETQ (REX.W CF); `.sysret` covers SYSRET (0F 07) and the
    REX.W form (48 0F 07). -/
inductive SysDecodiert where
  | hlt | cli | sti | pause | cpuid | rdtsc | iret | syscall | sysret
  | intN : Nat → SysDecodiert
  | extra : SysExtra → SysDecodiert
  deriving DecidableEq, Repr

/-- Every modelled row maps to its accepted form; extras map to none. -/
def sysFormOfRow : SysDecodiert → Option SysFormArt
  | .hlt => some .hlt
  | .cli => some .cli
  | .sti => some .sti
  | .pause => some .pause
  | .cpuid => some .cpuid
  | .rdtsc => some .rdtsc
  | .iret => some .iret
  | .syscall => some .syscall
  | .sysret => some .sysret
  | .intN _ => some .intN
  | .extra _ => none

/-! ## 1. Byte decode: one row per system opcode.

  Fixed one-byte rows: HLT F4, CLI FA, STI FB, IRET CF, INT3 CC,
  INT1 F1, CLD FC, STD FD. INT CD ib consumes its vector byte.
  PAUSE is F3 90. The 0F escape carries RDTSC 31, CPUID A2, RDMSR
  32, WRMSR 30, RDPMC 33, SYSCALL 05, SYSRET 07, and the 0F 01
  group (RDTSCP F9, XGETBV D0). REX.W 48 prefixes IRETQ (CF) and
  the 64-bit SYSRET (0F 07). Truncated inputs refuse. -/

/-- Byte decode of the system rows, with the unconsumed tail. -/
def sysDecode : List Byte → Option (SysDecodiert × List Byte)
  | [] => none
  | b :: rest =>
    match byteNat b with
    | 244 => some (.hlt, rest)
    | 250 => some (.cli, rest)
    | 251 => some (.sti, rest)
    | 207 => some (.iret, rest)
    | 204 => some (.extra .int3, rest)
    | 241 => some (.extra .int1, rest)
    | 252 => some (.extra .cld, rest)
    | 253 => some (.extra .std, rest)
    | 205 =>
      match rest with
      | [] => none
      | b2 :: rest2 => some (.intN (byteNat b2), rest2)
    | 243 =>
      match rest with
      | [] => none
      | b1 :: rest1 =>
        match byteNat b1 with
        | 144 => some (.pause, rest1)
        | _ => none
    | 72 =>
      match rest with
      | [] => none
      | b1 :: rest1 =>
        match byteNat b1 with
        | 207 => some (.iret, rest1)
        | 15 =>
          match rest1 with
          | [] => none
          | b2 :: rest2 =>
            match byteNat b2 with
            | 7 => some (.sysret, rest2)
            | _ => none
        | _ => none
    | 15 =>
      match rest with
      | [] => none
      | b1 :: rest1 =>
        match byteNat b1 with
        | 49 => some (.rdtsc, rest1)
        | 162 => some (.cpuid, rest1)
        | 50 => some (.extra .rdmsr, rest1)
        | 48 => some (.extra .wrmsr, rest1)
        | 51 => some (.extra .rdpmc, rest1)
        | 5 => some (.syscall, rest1)
        | 7 => some (.sysret, rest1)
        | 1 =>
          match rest1 with
          | [] => none
          | b2 :: rest2 =>
            match byteNat b2 with
            | 249 => some (.extra .rdtscp, rest2)
            | 208 => some (.extra .xgetbv, rest2)
            | _ => none
        | _ => none
    | _ => none

/-- Every fixed modelled row decodes to its row. -/
theorem sysDecode_hlt : sysDecode [natByte 244] = some (.hlt, []) := by
  decide
theorem sysDecode_cli : sysDecode [natByte 250] = some (.cli, []) := by
  decide
theorem sysDecode_sti : sysDecode [natByte 251] = some (.sti, []) := by
  decide
theorem sysDecode_iret : sysDecode [natByte 207] = some (.iret, []) := by
  decide
theorem sysDecode_iretq :
    sysDecode [natByte 72, natByte 207] = some (.iret, []) := by
  decide
theorem sysDecode_pause :
    sysDecode [natByte 243, natByte 144] = some (.pause, []) := by
  decide
theorem sysDecode_cpuid :
    sysDecode [natByte 15, natByte 162] = some (.cpuid, []) := by
  decide
theorem sysDecode_rdtsc :
    sysDecode [natByte 15, natByte 49] = some (.rdtsc, []) := by
  decide
theorem sysDecode_syscall :
    sysDecode [natByte 15, natByte 5] = some (.syscall, []) := by
  decide
theorem sysDecode_sysret :
    sysDecode [natByte 15, natByte 7] = some (.sysret, []) := by
  decide
theorem sysDecode_sysretq :
    sysDecode [natByte 72, natByte 15, natByte 7] =
      some (.sysret, []) := by
  decide

/-- INT decodes with every vector byte (schematic, not one literal). -/
theorem sysDecode_intN (n : Nat) :
    sysDecode [natByte 205, natByte n] =
      some (.intN (byteNat (natByte n)), []) :=
  rfl

/-- Every deferred row decodes to its explicit refusal row. -/
theorem sysDecode_int3 : sysDecode [natByte 204] = some (.extra .int3, []) := by
  decide
theorem sysDecode_int1 : sysDecode [natByte 241] = some (.extra .int1, []) := by
  decide
theorem sysDecode_cld : sysDecode [natByte 252] = some (.extra .cld, []) := by
  decide
theorem sysDecode_std : sysDecode [natByte 253] = some (.extra .std, []) := by
  decide
theorem sysDecode_rdtscp :
    sysDecode [natByte 15, natByte 1, natByte 249] =
      some (.extra .rdtscp, []) := by
  decide
theorem sysDecode_xgetbv :
    sysDecode [natByte 15, natByte 1, natByte 208] =
      some (.extra .xgetbv, []) := by
  decide
theorem sysDecode_rdmsr :
    sysDecode [natByte 15, natByte 50] = some (.extra .rdmsr, []) := by
  decide
theorem sysDecode_wrmsr :
    sysDecode [natByte 15, natByte 48] = some (.extra .wrmsr, []) := by
  decide
theorem sysDecode_rdpmc :
    sysDecode [natByte 15, natByte 51] = some (.extra .rdpmc, []) := by
  decide

/-- Truncated inputs refuse: bare prefixes decode to nothing. -/
theorem sysDecode_leer : sysDecode [] = none := rfl
theorem sysDecode_int_abgeschnitten : sysDecode [natByte 205] = none := by
  decide
theorem sysDecode_esc_abgeschnitten : sysDecode [natByte 15] = none := by
  decide
theorem sysDecode_rex_abgeschnitten : sysDecode [natByte 72] = none := by
  decide

/-! ## 2. Encoder and round trip.

  The encoder writes the canonical bytes (one-byte IRET CF, two-byte
  SYSRET 0F 07); the decoder also accepts the REX.W twins. Decoding
  inverts encoding up to the vector-byte wrap (`sysNorm`). -/

/-- Canonical encoder: one byte string per decoded row. -/
def sysEncode : SysDecodiert → List Byte
  | .hlt => [natByte 244]
  | .cli => [natByte 250]
  | .sti => [natByte 251]
  | .pause => [natByte 243, natByte 144]
  | .cpuid => [natByte 15, natByte 162]
  | .rdtsc => [natByte 15, natByte 49]
  | .iret => [natByte 207]
  | .syscall => [natByte 15, natByte 5]
  | .sysret => [natByte 15, natByte 7]
  | .intN n => [natByte 205, natByte n]
  | .extra .int3 => [natByte 204]
  | .extra .int1 => [natByte 241]
  | .extra .cld => [natByte 252]
  | .extra .std => [natByte 253]
  | .extra .rdtscp => [natByte 15, natByte 1, natByte 249]
  | .extra .xgetbv => [natByte 15, natByte 1, natByte 208]
  | .extra .rdmsr => [natByte 15, natByte 50]
  | .extra .wrmsr => [natByte 15, natByte 48]
  | .extra .rdpmc => [natByte 15, natByte 51]

/-- Normal form of decoding after encoding: only the INT vector byte
    wraps (a `Nat` through eight bits). -/
def sysNorm : SysDecodiert → SysDecodiert
  | .intN n => .intN (byteNat (natByte n))
  | r => r

/-- Decoding inverts encoding on every row, up to the vector wrap. -/
theorem sysRoundTrip (r : SysDecodiert) :
    sysDecode (sysEncode r) = some (sysNorm r, []) := by
  cases r with
  | hlt => rfl
  | cli => rfl
  | sti => rfl
  | pause => rfl
  | cpuid => rfl
  | rdtsc => rfl
  | iret => rfl
  | syscall => rfl
  | sysret => rfl
  | intN n => rfl
  | extra x => cases x <;> rfl

/-- Encoded lengths match the opcode table (IRETQ/SYSRETQ twins take
    one byte more; see `sysDecode_iretq`/`sysDecode_sysretq`). -/
theorem sysEncode_laengen :
    (sysEncode .hlt).length = 1 ∧
      (sysEncode .cli).length = 1 ∧
      (sysEncode .sti).length = 1 ∧
      (sysEncode .pause).length = 2 ∧
      (sysEncode .cpuid).length = 2 ∧
      (sysEncode .rdtsc).length = 2 ∧
      (sysEncode (.intN 3)).length = 2 ∧
      (sysEncode .iret).length = 1 ∧
      (sysEncode .syscall).length = 2 ∧
      (sysEncode .sysret).length = 2 ∧
      (sysEncode (.extra .rdtscp)).length = 3 := by
  decide

/-! ## 3. Extended chain over the capstone chain.

  `kapDecodeSys` runs the old chain first and the system decoder
  only where the old chain refuses, so dispatch stays disjoint by
  construction. A maintainer extends the existing `kapDecode` of
  `HwKapsteinDecoder.lean` with a `sys` arm in last position
  (after the `avx2` arm); the agreement theorems below state
  exactly what that extension must satisfy. -/

/-- Extended decoded row: an old-chain row or a system row. -/
inductive SysKette where
  | alt : KapDekodiert → SysKette
  | sys : SysDecodiert → SysKette
  deriving DecidableEq, Repr

/-- Extended chain: the old chain first, the system rows only where
    it refuses. No old row is shadowed. -/
def kapDecodeSys : List Byte → Option (SysKette × List Byte) :=
  fun bs =>
    match kapDecode bs with
    | some (k, rest) => some (.alt k, rest)
    | none =>
      match sysDecode bs with
      | some (r, rest) => some (.sys r, rest)
      | none => none

/-- Exact agreement: on every byte string the old chain decodes, the
    extended chain takes the old row with the old tail. -/
theorem kapDecodeSys_alt (bs : List Byte) (k : KapDekodiert)
    (rest : List Byte) (h : kapDecode bs = some (k, rest)) :
    kapDecodeSys bs = some (.alt k, rest) := by
  unfold kapDecodeSys
  rw [h]

/-- Where both chains refuse, the extended chain refuses. -/
theorem kapDecodeSys_nichts (bs : List Byte)
    (h1 : kapDecode bs = none) (h2 : sysDecode bs = none) :
    kapDecodeSys bs = none := by
  unfold kapDecodeSys
  rw [h1, h2]

/-- The old chain refuses every new system row (no shadowing either
    way: the new rows are taken exactly once, by the new arm). -/
theorem kapDecode_nimmt_hlt_nicht :
    kapDecode [natByte 244] = none := by decide
theorem kapDecode_nimmt_cli_nicht :
    kapDecode [natByte 250] = none := by decide
theorem kapDecode_nimmt_sti_nicht :
    kapDecode [natByte 251] = none := by decide
theorem kapDecode_nimmt_iret_nicht :
    kapDecode [natByte 207] = none := by decide
theorem kapDecode_nimmt_iretq_nicht :
    kapDecode [natByte 72, natByte 207] = none := by decide
theorem kapDecode_nimmt_pause_nicht :
    kapDecode [natByte 243, natByte 144] = none := by decide
theorem kapDecode_nimmt_cpuid_nicht :
    kapDecode [natByte 15, natByte 162] = none := by decide
theorem kapDecode_nimmt_rdtsc_nicht :
    kapDecode [natByte 15, natByte 49] = none := by decide
theorem kapDecode_nimmt_syscall_nicht :
    kapDecode [natByte 15, natByte 5] = none := by decide
theorem kapDecode_nimmt_sysret_nicht :
    kapDecode [natByte 15, natByte 7] = none := by decide
theorem kapDecode_nimmt_sysretq_nicht :
    kapDecode [natByte 72, natByte 15, natByte 7] = none := by decide
theorem kapDecode_nimmt_int3_nicht :
    kapDecode [natByte 204] = none := by decide
theorem kapDecode_nimmt_int1_nicht :
    kapDecode [natByte 241] = none := by decide
theorem kapDecode_nimmt_cld_nicht :
    kapDecode [natByte 252] = none := by decide
theorem kapDecode_nimmt_std_nicht :
    kapDecode [natByte 253] = none := by decide
theorem kapDecode_nimmt_rdtscp_nicht :
    kapDecode [natByte 15, natByte 1, natByte 249] = none := by decide
theorem kapDecode_nimmt_xgetbv_nicht :
    kapDecode [natByte 15, natByte 1, natByte 208] = none := by decide
theorem kapDecode_nimmt_rdmsr_nicht :
    kapDecode [natByte 15, natByte 50] = none := by decide
theorem kapDecode_nimmt_wrmsr_nicht :
    kapDecode [natByte 15, natByte 48] = none := by decide
theorem kapDecode_nimmt_rdpmc_nicht :
    kapDecode [natByte 15, natByte 51] = none := by decide
theorem kapDecode_nimmt_leer_nicht : kapDecode [] = none := by decide

/-- Every new row decodes through the extended chain. -/
theorem kapSys_hlt :
    kapDecodeSys [natByte 244] = some (.sys .hlt, []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_hlt_nicht, sysDecode_hlt]
theorem kapSys_cli :
    kapDecodeSys [natByte 250] = some (.sys .cli, []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_cli_nicht, sysDecode_cli]
theorem kapSys_sti :
    kapDecodeSys [natByte 251] = some (.sys .sti, []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_sti_nicht, sysDecode_sti]
theorem kapSys_iret :
    kapDecodeSys [natByte 207] = some (.sys .iret, []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_iret_nicht, sysDecode_iret]
theorem kapSys_iretq :
    kapDecodeSys [natByte 72, natByte 207] = some (.sys .iret, []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_iretq_nicht, sysDecode_iretq]
theorem kapSys_pause :
    kapDecodeSys [natByte 243, natByte 144] =
      some (.sys .pause, []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_pause_nicht, sysDecode_pause]
theorem kapSys_cpuid :
    kapDecodeSys [natByte 15, natByte 162] =
      some (.sys .cpuid, []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_cpuid_nicht, sysDecode_cpuid]
theorem kapSys_rdtsc :
    kapDecodeSys [natByte 15, natByte 49] =
      some (.sys .rdtsc, []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_rdtsc_nicht, sysDecode_rdtsc]
theorem kapSys_syscall :
    kapDecodeSys [natByte 15, natByte 5] =
      some (.sys .syscall, []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_syscall_nicht, sysDecode_syscall]
theorem kapSys_sysret :
    kapDecodeSys [natByte 15, natByte 7] =
      some (.sys .sysret, []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_sysret_nicht, sysDecode_sysret]
theorem kapSys_sysretq :
    kapDecodeSys [natByte 72, natByte 15, natByte 7] =
      some (.sys .sysret, []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_sysretq_nicht, sysDecode_sysretq]
theorem kapDecode_nimmt_intN2_nicht :
    kapDecode [natByte 205, natByte 2] = none := by decide
theorem kapDecode_nimmt_intN3_nicht :
    kapDecode [natByte 205, natByte 3] = none := by decide
theorem kapSys_intN2 :
    kapDecodeSys [natByte 205, natByte 2] =
      some (.sys (.intN 2), []) := by
  have h2 : sysDecode [natByte 205, natByte 2] =
      some (.intN 2, []) := by decide
  simp only [kapDecodeSys, kapDecode_nimmt_intN2_nicht, h2]
theorem kapSys_intN3 :
    kapDecodeSys [natByte 205, natByte 3] =
      some (.sys (.intN 3), []) := by
  have h2 : sysDecode [natByte 205, natByte 3] =
      some (.intN 3, []) := by decide
  simp only [kapDecodeSys, kapDecode_nimmt_intN3_nicht, h2]
theorem kapSys_int3 :
    kapDecodeSys [natByte 204] = some (.sys (.extra .int3), []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_int3_nicht, sysDecode_int3]
theorem kapSys_int1 :
    kapDecodeSys [natByte 241] = some (.sys (.extra .int1), []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_int1_nicht, sysDecode_int1]
theorem kapSys_cld :
    kapDecodeSys [natByte 252] = some (.sys (.extra .cld), []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_cld_nicht, sysDecode_cld]
theorem kapSys_std :
    kapDecodeSys [natByte 253] = some (.sys (.extra .std), []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_std_nicht, sysDecode_std]
theorem kapSys_rdtscp :
    kapDecodeSys [natByte 15, natByte 1, natByte 249] =
      some (.sys (.extra .rdtscp), []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_rdtscp_nicht, sysDecode_rdtscp]
theorem kapSys_xgetbv :
    kapDecodeSys [natByte 15, natByte 1, natByte 208] =
      some (.sys (.extra .xgetbv), []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_xgetbv_nicht, sysDecode_xgetbv]
theorem kapSys_rdmsr :
    kapDecodeSys [natByte 15, natByte 50] =
      some (.sys (.extra .rdmsr), []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_rdmsr_nicht, sysDecode_rdmsr]
theorem kapSys_wrmsr :
    kapDecodeSys [natByte 15, natByte 48] =
      some (.sys (.extra .wrmsr), []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_wrmsr_nicht, sysDecode_wrmsr]
theorem kapSys_rdpmc :
    kapDecodeSys [natByte 15, natByte 51] =
      some (.sys (.extra .rdpmc), []) := by
  simp only [kapDecodeSys, kapDecode_nimmt_rdpmc_nicht, sysDecode_rdpmc]
theorem kapSys_leer : kapDecodeSys [] = none := by
  simp only [kapDecodeSys, kapDecode_nimmt_leer_nicht, sysDecode_leer]

/-! ## 4. Lowering to the accepted event and the machine plug.

  A decoded row plus the caller-supplied inputs (MSR snapshots, leaf
  answers, time stamp, IDT/TSS window: environment user logic, never
  invented) lowers to the accepted `SysEreignis`. INT carries its
  vector byte from the instruction; every other modelled row keeps
  the inputs unchanged. Deferred rows lower to `none`: no accepted
  evaluator exists for them, so nothing is admitted silently. -/

/-- Lowering: decoded row plus explicit inputs to the accepted event. -/
def sysEreignisOfRow : SysDecodiert → SysEingaben → Option SysEreignis
  | .intN n, ev => some ⟨.intN, { ev with vektor := n }⟩
  | .extra _, _ => none
  | r, ev =>
    match sysFormOfRow r with
    | some f => some ⟨f, ev⟩
    | none => none

/-- Every fixed modelled row lowers with unchanged inputs. -/
theorem sysEreignis_hlt (ev : SysEingaben) :
    sysEreignisOfRow .hlt ev = some ⟨.hlt, ev⟩ :=
  rfl
theorem sysEreignis_cli (ev : SysEingaben) :
    sysEreignisOfRow .cli ev = some ⟨.cli, ev⟩ :=
  rfl
theorem sysEreignis_sti (ev : SysEingaben) :
    sysEreignisOfRow .sti ev = some ⟨.sti, ev⟩ :=
  rfl
theorem sysEreignis_pause (ev : SysEingaben) :
    sysEreignisOfRow .pause ev = some ⟨.pause, ev⟩ :=
  rfl
theorem sysEreignis_cpuid (ev : SysEingaben) :
    sysEreignisOfRow .cpuid ev = some ⟨.cpuid, ev⟩ :=
  rfl
theorem sysEreignis_rdtsc (ev : SysEingaben) :
    sysEreignisOfRow .rdtsc ev = some ⟨.rdtsc, ev⟩ :=
  rfl
theorem sysEreignis_iret (ev : SysEingaben) :
    sysEreignisOfRow .iret ev = some ⟨.iret, ev⟩ :=
  rfl
theorem sysEreignis_syscall (ev : SysEingaben) :
    sysEreignisOfRow .syscall ev = some ⟨.syscall, ev⟩ :=
  rfl
theorem sysEreignis_sysret (ev : SysEingaben) :
    sysEreignisOfRow .sysret ev = some ⟨.sysret, ev⟩ :=
  rfl

/-- INT lowers with the vector byte from the instruction. -/
theorem sysEreignis_intN (n : Nat) (ev : SysEingaben) :
    sysEreignisOfRow (.intN n) ev =
      some ⟨.intN, { ev with vektor := n }⟩ :=
  rfl

/-- Every deferred row is refused by the lowering. -/
theorem sysEreignis_extra (x : SysExtra) (ev : SysEingaben) :
    sysEreignisOfRow (.extra x) ev = none := by
  cases x <;> rfl

/-! ## 5. The producer plug on the coherent machine.

  `adapterSysDecode` instantiates `HwAdapter` over decoded rows: a
  lowered event runs through the accepted `adapterSystem` plug;
  deferred rows admit no successor state. Only core data and shared
  memory move, so well-formedness survives every admitted step. -/

/-- The system-decode plug: one checked decoded-row step. -/
def adapterSysDecode : HwAdapter (SysSteuer × SysDecodiert × SysEingaben) :=
  ⟨fun m c p =>
    match sysEreignisOfRow p.2.1 p.2.2 with
    | none => none
    | some e => adapterSystem.schritt m c (p.1, e)⟩

/-- Agreement: the plug succeeds exactly where the accepted system
    plug succeeds on the lowered event. -/
theorem adapterSysDecode_ok (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (r : SysDecodiert) (ev : SysEingaben)
    (e : SysEreignis) (h : sysEreignisOfRow r ev = some e) :
    adapterSysDecode.schritt m c (st, r, ev) =
      adapterSystem.schritt m c (st, e) := by
  unfold adapterSysDecode
  show (match sysEreignisOfRow r ev with
    | none => (none : Option HwMaschine)
    | some e => adapterSystem.schritt m c (st, e)) =
    adapterSystem.schritt m c (st, e)
  rw [h]

/-- A deferred row admits no plug step. -/
theorem adapterSysDecode_extra (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (x : SysExtra) (ev : SysEingaben) :
    adapterSysDecode.schritt m c (st, .extra x, ev) = none := by
  have h := sysEreignis_extra x ev
  unfold adapterSysDecode
  show (match sysEreignisOfRow (.extra x) ev with
    | none => (none : Option HwMaschine)
    | some e => adapterSystem.schritt m c (st, e)) = none
  rw [h]

/-- The accepted system plug preserves well-formedness: only core
    data and memory move, profiles are untouched. -/
theorem adapterSystem_wf (m : HwMaschine) (c : Nat)
    (q : SysSteuer × SysEreignis) (m' : HwMaschine) (hwf : HwWf m)
    (h : adapterSystem.schritt m c q = some m') :
    HwWf m' := by
  unfold adapterSystem at h
  cases hs : sysSnapSchritt m c q.1 q.2 with
  | ok k' st' mem' =>
    simp [hs] at h
    cases h
    exact hwf
  | fehler f => simp [hs] at h
  | verweigert => simp [hs] at h

/-- Every admitted plug step preserves well-formedness. -/
theorem adapterSysDecode_wf (m : HwMaschine) (c : Nat)
    (p : SysSteuer × SysDecodiert × SysEingaben) (m' : HwMaschine)
    (hwf : HwWf m)
    (h : adapterSysDecode.schritt m c p = some m') :
    HwWf m' := by
  unfold adapterSysDecode at h
  cases he : sysEreignisOfRow p.2.1 p.2.2 with
  | none => simp [he] at h
  | some e =>
    simp [he] at h
    exact adapterSystem_wf m c (p.1, e) m' hwf h

/-! ## 6. Execution: decoded bytes reach the accepted machine.

  The HLT byte halts the witness core; the INT 2 bytes lower with
  the vector from the instruction and reach the accepted handler;
  the run changes real memory (INT frame bytes, TSO drain 0 to 42)
  on two cores, beside profile/privilege refusals. -/

/-- The HLT byte halts witness core 0 (CPL 0). -/
theorem sysWit_hlt_halt0 :
    sysHaltedOut (sysAusfuehren sysWitStart 0 ⟨.hlt, sysWitEingaben⟩) 0 =
      some true := by
  decide

/-- The INT 2 bytes lower with the vector from the instruction. -/
theorem sysEreignis_intN2_wit :
    sysEreignisOfRow (.intN 2) sysWitEingaben =
      some ⟨.intN, sysWitEingaben⟩ :=
  rfl

/-- Joint witness: every new row decodes through the extended chain,
    HLT halts, INT 2 lowers with its vector and reaches the accepted
    handler on both cores, the frame lands in memory, the TSO drain
    moves 0 to 42, and freestanding SYSCALL plus CPL-3 HLT refuse.
    Non-degenerate: real delivery frames and a memory-changing drain. -/
theorem sysDecode_zeuge :
    kapDecodeSys [natByte 244] = some (.sys .hlt, []) ∧
      kapDecodeSys [natByte 250] = some (.sys .cli, []) ∧
      kapDecodeSys [natByte 251] = some (.sys .sti, []) ∧
      kapDecodeSys [natByte 207] = some (.sys .iret, []) ∧
      kapDecodeSys [natByte 72, natByte 207] =
        some (.sys .iret, []) ∧
      kapDecodeSys [natByte 243, natByte 144] =
        some (.sys .pause, []) ∧
      kapDecodeSys [natByte 15, natByte 162] =
        some (.sys .cpuid, []) ∧
      kapDecodeSys [natByte 15, natByte 49] =
        some (.sys .rdtsc, []) ∧
      kapDecodeSys [natByte 15, natByte 5] =
        some (.sys .syscall, []) ∧
      kapDecodeSys [natByte 15, natByte 7] =
        some (.sys .sysret, []) ∧
      kapDecodeSys [natByte 72, natByte 15, natByte 7] =
        some (.sys .sysret, []) ∧
      kapDecodeSys [natByte 205, natByte 2] =
        some (.sys (.intN 2), []) ∧
      kapDecodeSys [natByte 204] =
        some (.sys (.extra .int3), []) ∧
      kapDecodeSys [natByte 241] =
        some (.sys (.extra .int1), []) ∧
      kapDecodeSys [natByte 252] =
        some (.sys (.extra .cld), []) ∧
      kapDecodeSys [natByte 253] =
        some (.sys (.extra .std), []) ∧
      kapDecodeSys [natByte 15, natByte 1, natByte 249] =
        some (.sys (.extra .rdtscp), []) ∧
      kapDecodeSys [natByte 15, natByte 1, natByte 208] =
        some (.sys (.extra .xgetbv), []) ∧
      kapDecodeSys [natByte 15, natByte 50] =
        some (.sys (.extra .rdmsr), []) ∧
      kapDecodeSys [natByte 15, natByte 48] =
        some (.sys (.extra .wrmsr), []) ∧
      kapDecodeSys [natByte 15, natByte 51] =
        some (.sys (.extra .rdpmc), []) ∧
      sysHaltedOut
        (sysAusfuehren sysWitStart 0 ⟨.hlt, sysWitEingaben⟩) 0 =
        some true ∧
      sysEreignisOfRow (.intN 2) sysWitEingaben =
        some ⟨.intN, sysWitEingaben⟩ ∧
      sysRipOut sysWitO_int 0 = some (BitVec.ofNat 64 0x2000) ∧
      sysMemOut sysWitO_int (BitVec.ofNat 64 16344) =
        some (BitVec.ofNat 8 0x02) ∧
      sysRipOut sysWitO_int1 1 = some (BitVec.ofNat 64 0x2000) ∧
      sysWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      sysKlasseOut (sysAusfuehren sysWitStart 0
        ⟨.syscall, { sysWitEingaben with profil := .freistehend }⟩) =
        some .ud ∧
      sysKlasseOut
        (sysAusfuehren sysWitHochM 0 ⟨.hlt, sysWitEingaben⟩) =
        some .gp := by
  exact ⟨kapSys_hlt, kapSys_cli, kapSys_sti, kapSys_iret, kapSys_iretq,
    kapSys_pause, kapSys_cpuid, kapSys_rdtsc, kapSys_syscall,
    kapSys_sysret, kapSys_sysretq, kapSys_intN2, kapSys_int3,
    kapSys_int1, kapSys_cld, kapSys_std, kapSys_rdtscp, kapSys_xgetbv,
    kapSys_rdmsr, kapSys_wrmsr, kapSys_rdpmc, sysWit_hlt_halt0,
    sysEreignis_intN2_wit, sysWit_int_rip, sysWit_int_frame_rip,
    sysWit_int1_rip, sysWit_spuelung_aendert_speicher, sysWit_ud_frei,
    sysWit_gp_hlt⟩

/- CUTS:
  Proved here: byte decode rows for 21 system/privileged opcode
  shapes (12 modelled byte rows over the ten accepted `SysFormArt`
  forms plus 9 deferred rows), the canonical encoder with round
  trip up to the INT vector-byte wrap, exact lengths, the extended
  chain `kapDecodeSys` with exact agreement on every byte string the
  old chain decodes and one-taking of every new row (old-chain
  refusal pinned per row), lowering to the accepted event with
  unchanged inputs (INT vector from the instruction), the
  `HwAdapter` plug with exact accepted-plug agreement, refusal of
  every deferred row at both levels, well-formedness preservation,
  and a reached two-core run (HLT halts, INT 2 delivers on both
  cores, frame bytes and a TSO drain 0-to-42 change real memory)
  beside profile/privilege refusals.
  NOT proved here, and not claimed:
  - No hardware correspondence beyond self-consistency: the opcode
    map is transcribed from the clone-local Intel snapshot
    `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
    (provenance, never a proof). No AMD manual is in the clone, so
    no AMD fact is claimed; the rows are defined identically on
    both vendors (common architecture).
  - The deferred rows (INT3, INT1, CLD, STD, RDTSCP, XGETBV,
    RDMSR, WRMSR, RDPMC) have no accepted evaluator: they decode
    and are refused, never executed. Their semantics (debug traps,
    RFLAGS.DF, TSC aux, MSR snapshots, counter selects) stay OPEN.
  - PREFETCHh (0F 18) and PREFETCHW (0F 0D) are not decoded: their
    ModRM/SIB/displacement tails need `AddressEncoding`, and no
    accepted hint semantics exists. SYSENTER/SYSEXIT, CLTS, INVD,
    WBINVD, LMSW/SMSW and control/debug-register moves are not
    covered either.
  - IRETQ and the REX.W SYSRET share the accepted `.iret`/`.sysret`
    legs (five-word software frame, 64-bit return only); error-code
    frames, task switches and selector validation stay OPEN (same
    CUTS as `HwSystemForms`).
  - Flags the architecture calls undefined stay FREE: no row
    constrains any flag beyond what the accepted legs keep.
  - Timing, serialisation and drain behaviour are the named
    assumptions of `HwSystemForms` (S-SERIAL-*); the bridge to W/GX
    ordering is OPEN.
  - Maintainer note: to wire these rows into the built chain, add a
    `sys` arm for `sysDecode` in last position of `kapDecode`
    (`HwKapsteinDecoder.lean`, after the `avx2` arm); the
    `kapDecodeSys_*` theorems state the required behaviour. The
    merge gate's `lean-layout --apply` moves this module to
    `Befehle/System/` (rule `^System\w+$`) and rewrites the import.
-/

#print axioms sysRoundTrip
#print axioms kapDecodeSys_alt
#print axioms kapDecodeSys_nichts
#print axioms adapterSysDecode_ok
#print axioms adapterSysDecode_extra
#print axioms adapterSystem_wf
#print axioms adapterSysDecode_wf
#print axioms sysEreignis_extra
#print axioms sysDecode_zeuge

end Gabbro.Grammatik.X86
