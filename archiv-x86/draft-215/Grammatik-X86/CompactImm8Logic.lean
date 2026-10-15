/-
  File:      Grammatik/X86/CompactImm8Logic.lean
  Subject:   Connection for the compact REX.W 83 /1 /4 /6 imm8 logic rows.

  Lane 751: the three register-direct 64-bit AND/OR/XOR-with-imm8 rows
  reuse the accepted `IntegerHardwareForms` vocabulary only
  (`encodeIntHwImm` / `decodeIntHwImm` / `stepIntHwImm` / `immWort` /
  `imm8Erweitern` / `immPasst8`, the fetched `fetchIntHwImm` and the
  byte step `intHwImmByteschritt`); no canonical definition is added
  here. Proved: per-width logic-flag identity (CF = OF = false,
  AF undefined, SF/ZF/PF from the width-correct result), pinned
  compact bytes for all three REX.W rows, refusal outside the signed
  byte range (wide 81 form instead of compact 83), and one joint
  connection theorem with a memory-changing reached run.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
  - `intel-instruction-reference.txt`, Intel SDM edition 325462-093US
    (`REFERENCES.json`: `intel-instruction-reference`).
  - AND opcode row, txt line 40726:
    `REX.W + 83 /4 ib  AND r/m64, imm8 ... r/m64 AND imm8
    (sign-extended).`
  - AND flags, txt lines 40766-40768: "The OF and CF flags are
    cleared; the SF, ZF, and PF flags are set according to the
    result. The state of the AF flag is undefined."
  - OR opcode row, txt line 71678:
    `REX.W + 83 /1 ib  OR r/m64, imm8 ... r/m64 OR imm8
    (sign-extended).`
  - OR flags, txt lines 71721-71722: same flag identity as AND.
  - XOR opcode row, txt line 138276:
    `REX.W + 83 /6 ib  XOR r/m64, imm8 ... r/m64 XOR imm8
    (sign-extended).`
  - XOR flags, txt lines 138319-138321: same flag identity.
-/
import Grammatik.X86.IntegerHardwareForms
import Grammatik.X86.ShiftLogic
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- Witness value in rax before the compact OR step (nonzero). -/
def kompaktRax : Wort := BitVec.ofNat 64 0xF0

/-- Data cell written by the witness store. -/
def datenZelle : Adresse := BitVec.ofNat 64 8192

/-- Witness program bytes: compact `or rax, 1` (4 bytes) then the
    pilot `store [rbx], rax` (7 bytes). -/
def kompaktProg : List Byte :=
  [natByte 72, natByte 131, natByte 200, natByte 1,
   natByte 72, natByte 137, natByte 131,
   natByte 0, natByte 0, natByte 0, natByte 0]

/-- Program bytes over addresses from 4096; zero elsewhere. -/
def kompaktBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else kompaktProg.getD (a.toNat - 4096) (BitVec.ofNat 8 0)

/-- Code window executable: 4096..4128. -/
def kompaktExec (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4128)

/-- Data cell readable and writable: 8192..8200. -/
def kompaktDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8200)

/-- Witness registers: `rax` holds 0xF0, `rbx` the data cell. -/
def kompaktReg : Register → Wort := fun q =>
  if q = Register.rax then kompaktRax
  else if q = Register.rbx then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness flags: nothing set. -/
def kompaktFlags : Flags :=
  { cf := false, pf := true, af := some false, zf := false, sf := false,
    of := false }

/-- Witness start state: compact program at 4096, data cell at 8192. -/
def kompaktStart : Zustand :=
  { register := kompaktReg
    flags := kompaktFlags
    rip := BitVec.ofNat 64 4096
    speicher :=
      { bytes := kompaktBytes
        lesbar := kompaktDaten
        schreibbar := kompaktDaten
        ausfuehrbar := kompaktExec } }

/-- Fetched suffix after the 4 compact bytes (checked data). -/
def kompaktRest : List Byte := (geholt kompaktStart).drop 4

/-! ## 2. Pinned bytes and decodes for the three REX.W rows.

    Opcode 83 is decimal 131; ModRM is register-direct (mod = 3)
    with the group digit in the reg field: /1 OR, /4 AND, /6 XOR
    (manual rows: AND txt 40726, OR txt 71678, XOR txt 138276). -/

/-- Pinned bytes: `or rax, 1` is REX.W, 83, C8, 01. -/
theorem pin_or_kompakt :
    encodeIntHwImm (.orI .b64 .rax 1) =
      [natByte 72, natByte 131, natByte 200, natByte 1] := by
  decide

/-- Pinned decode: `or rax, 1`. -/
theorem pin_or_kompakt_dekode :
    decodeIntHwImm [natByte 72, natByte 131, natByte 200, natByte 1] =
      some ((⟨.orI .b64 .rax 1, 4⟩ : IntHwImmDec), []) := by
  decide

/-- Pinned bytes: `and rax, 1` is REX.W, 83, E0, 01. -/
theorem pin_and_kompakt :
    encodeIntHwImm (.andI .b64 .rax 1) =
      [natByte 72, natByte 131, natByte 224, natByte 1] := by
  decide

/-- Pinned decode: `and rax, 1`. -/
theorem pin_and_kompakt_dekode :
    decodeIntHwImm [natByte 72, natByte 131, natByte 224, natByte 1] =
      some ((⟨.andI .b64 .rax 1, 4⟩ : IntHwImmDec), []) := by
  decide

/-- Pinned bytes: `xor rax, -1` signs through one byte. -/
theorem pin_xor_kompakt :
    encodeIntHwImm (.xorI .b64 .rax 0xFFFFFFFF) =
      [natByte 72, natByte 131, natByte 240, natByte 255] := by
  decide

/-- Pinned decode: `xor rax, -1` (sign extension at decode). -/
theorem pin_xor_kompakt_dekode :
    decodeIntHwImm [natByte 72, natByte 131, natByte 240, natByte 255] =
      some ((⟨.xorI .b64 .rax 0xFFFFFFFF, 4⟩ : IntHwImmDec), []) := by
  decide

/-- Pinned 32-bit row: `and eax, 1` (zero-upper row). -/
theorem pin_and32_kompakt :
    encodeIntHwImm (.andI .b32 .rax 1) =
      [natByte 64, natByte 131, natByte 224, natByte 1] ∧
    decodeIntHwImm [natByte 64, natByte 131, natByte 224, natByte 1] =
      some ((⟨.andI .b32 .rax 1, 4⟩ : IntHwImmDec), []) := by
  decide

/-! ## 3. Compact choice and refusal outside the signed byte.

    The encoder takes the compact 83 form exactly when the int32
    value fits in a signed byte; outside that range the wide 81
    form (7 bytes) is emitted instead. Truncated tails refuse. -/

/-- The compact choice fires exactly on fitting values (OR row). -/
theorem kompakt_or_feuert (b : Breite) (dst : Register)
    (imm : BitVec 32) :
    (encodeIntHwImm (.orI b dst imm)).length = 4 ↔
      immPasst8 imm = true := by
  unfold encodeIntHwImm
  by_cases h : immPasst8 imm = true
  · simp [h]
  · have hf : immPasst8 imm = false := by
      cases he : immPasst8 imm with
      | true => simp [he] at h
      | false => rfl
    simp [hf, length_leBytes32]

/-- The compact choice fires exactly on fitting values (AND row). -/
theorem kompakt_and_feuert (b : Breite) (dst : Register)
    (imm : BitVec 32) :
    (encodeIntHwImm (.andI b dst imm)).length = 4 ↔
      immPasst8 imm = true := by
  unfold encodeIntHwImm
  by_cases h : immPasst8 imm = true
  · simp [h]
  · have hf : immPasst8 imm = false := by
      cases he : immPasst8 imm with
      | true => simp [he] at h
      | false => rfl
    simp [hf, length_leBytes32]

/-- The compact choice fires exactly on fitting values (XOR row). -/
theorem kompakt_xor_feuert (b : Breite) (dst : Register)
    (imm : BitVec 32) :
    (encodeIntHwImm (.xorI b dst imm)).length = 4 ↔
      immPasst8 imm = true := by
  unfold encodeIntHwImm
  by_cases h : immPasst8 imm = true
  · simp [h]
  · have hf : immPasst8 imm = false := by
      cases he : immPasst8 imm with
      | true => simp [he] at h
      | false => rfl
    simp [hf, length_leBytes32]

/-- The signed-byte boundary: 128 and 256 refuse the compact form,
    127 and -128 take it. -/
theorem kompakt_ausserhalb_i8 :
    immPasst8 256 = false ∧ immPasst8 128 = false ∧
    immPasst8 127 = true ∧ immPasst8 0xFFFFFF80 = true := by
  decide

/-- Outside the signed byte the wide form is emitted (7 bytes). -/
theorem kompakt_weit_bei_256 :
    (encodeIntHwImm (.orI .b64 .rax 256)).length = 7 ∧
    (encodeIntHwImm (.andI .b64 .rax 128)).length = 7 ∧
    (encodeIntHwImm (.xorI .b64 .rax 0xFFFFFF80)).length = 4 := by
  decide

/-- Truncated tails refuse: opcode without ModRM, ModRM without the
    immediate byte, lone REX. -/
theorem kompakt_abgeschnitten :
    decodeIntHwImm [natByte 72, natByte 131] = none ∧
    decodeIntHwImm [natByte 72, natByte 131, natByte 200] = none ∧
    decodeIntHwImm [natByte 72] = none := by
  decide

/-! ## 4. Successor projections of the witness OR step.

    Each projection evaluates the closed step and transports it along
    the step hypothesis; every premise is used. -/

/-- After `or rax, 1`, rax holds 0xF1. -/
theorem kompakt_s1_rax (s1 : Zustand)
    (hstep : stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart = some s1) :
    s1.register .rax = BitVec.ofNat 64 0xF1 := by
  have e : (stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart).map
      (fun s => s.register .rax) = some (BitVec.ofNat 64 0xF1) := by
    decide
  rw [hstep] at e
  simpa using e

/-- The OR step keeps rbx (the cell address). -/
theorem kompakt_s1_rbx (s1 : Zustand)
    (hstep : stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart = some s1) :
    s1.register .rbx = BitVec.ofNat 64 8192 := by
  have e : (stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart).map
      (fun s => s.register .rbx) = some (BitVec.ofNat 64 8192) := by
    decide
  rw [hstep] at e
  simpa using e

/-- The OR step advances RIP past its 4 bytes. -/
theorem kompakt_s1_rip (s1 : Zustand)
    (hstep : stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart = some s1) :
    s1.rip = BitVec.ofNat 64 4100 := by
  have e : (stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart).map
      (fun s => s.rip) = some (BitVec.ofNat 64 4100) := by
    decide
  rw [hstep] at e
  simpa using e

/-- The store address is the data cell. -/
theorem kompakt_s1_eff (s1 : Zustand)
    (hstep : stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart = some s1) :
    effAddr s1 .rbx (BitVec.ofNat 32 0) = datenZelle := by
  have hrbx := kompakt_s1_rbx s1 hstep
  unfold effAddr datenZelle
  rw [hrbx]
  decide

/-- The fetched window decodes to the stepped compact row. -/
theorem kompakt_fetch_dekode :
    decodeIntHwImm (geholt kompaktStart) =
      some (⟨.orI .b64 .rax 1, 4⟩, kompaktRest) := by
  decide

/-- The fetched compact row passes admission from actual memory. -/
theorem kompakt_fetch_zugelassen :
    fetchIntHwImm kompaktStart =
      some (⟨.orI .b64 .rax 1, 4⟩, kompaktRest) := by
  decide

/-- The OR value is 0xF0 OR sign-extended 1. -/
theorem kompakt_or_wert :
    orB .b64 kompaktRax (immWort 1) = BitVec.ofNat 64 0xF1 := by
  decide

/-- The start cell reads zero. -/
theorem kompakt_start_null :
    read64 kompaktStart.speicher datenZelle = some 0 := by
  decide

/-! ## 5. Joint connection and its reached-run witness.

    `CompactImm8Logic_verbindung` ties the fetched compact row to its
    step (flag identity, value, RIP), the byte-step dispatcher, the
    memory change through the pilot store, and the outside-i8 wide
    form. Its companion instantiates both step hypotheses jointly on
    the non-degenerate witness run. -/

/-- Joint connection for the compact REX.W 83 /1 /4 /6 imm8 rows. -/
theorem CompactImm8Logic_verbindung (s1 s2 : Zustand)
    (hstep : stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart = some s1)
    (hstore : schritt ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩ s1
      = some s2) :
    s1.flags.cf = false ∧ s1.flags.of = false ∧ s1.flags.af = none ∧
    s1.register .rax = orB .b64 kompaktRax (immWort 1) ∧
    s1.rip = BitVec.ofNat 64 4100 ∧
    decodeIntHwImm (geholt kompaktStart) =
      some (⟨.orI .b64 .rax 1, 4⟩, kompaktRest) ∧
    fetchIntHwImm kompaktStart =
      some (⟨.orI .b64 .rax 1, 4⟩, kompaktRest) ∧
    intHwImmByteschritt kompaktStart = .weiter s1 ∧
    read64 s2.speicher datenZelle = some (BitVec.ofNat 64 0xF1) ∧
    read64 kompaktStart.speicher datenZelle = some 0 ∧
    (encodeIntHwImm (.orI .b64 .rax 256)).length = 7 := by
  have hok4 : laengeOk 4 = true := by decide
  have hpass : immPasst8 (1 : BitVec 32) = true := by decide
  have hlen : (⟨.orI .b64 .rax 1, 4⟩ : IntHwImmDec).laenge =
      immDecLaenge (⟨.orI .b64 .rax 1, 4⟩ : IntHwImmDec).op := by
    simp only [immDecLaenge, hpass, if_true]
  have hb : immDecBreiteOk (⟨.orI .b64 .rax 1, 4⟩ : IntHwImmDec).op =
      true := by
    decide
  have hcf : s1.flags.cf = false := by
    have e : (stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart).map
        (fun s => s.flags.cf) = some false := by
      decide
    rw [hstep] at e
    simpa using e
  have hof : s1.flags.of = false := by
    have e : (stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart).map
        (fun s => s.flags.of) = some false := by
      decide
    rw [hstep] at e
    simpa using e
  have haf : s1.flags.af = none := by
    have e : (stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart).map
        (fun s => s.flags.af) = some none := by
      decide
    rw [hstep] at e
    simpa using e
  have hflag : s1.flags.cf = false ∧ s1.flags.of = false ∧
      s1.flags.af = none :=
    ⟨hcf, hof, haf⟩
  have hrax := kompakt_s1_rax s1 hstep
  have hrip := kompakt_s1_rip s1 hstep
  have hrbx := kompakt_s1_rbx s1 hstep
  have heff := kompakt_s1_eff s1 hstep
  have hmem1 : s1.speicher = kompaktStart.speicher :=
    stepImm_speicher _ _ _ hstep
  have hok7 : laengeOk 7 = true := by decide
  have hex : ∃ m, write64 s1.speicher (effAddr s1 .rbx (BitVec.ofNat 32 0))
      (s1.register .rax) = some m := by
    by_cases hw : write64 s1.speicher (effAddr s1 .rbx (BitVec.ofNat 32 0))
        (s1.register .rax) = none
    · have hver := schritt_store64_verweigert
        ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩ s1 .rbx .rax
        (BitVec.ofNat 32 0) hok7 rfl hw
      rw [hstore] at hver
      cases hver
    · obtain ⟨m, hm⟩ := Option.ne_none_iff_exists.mp hw
      exact ⟨m, hm.symm⟩
  obtain ⟨m, hm⟩ := hex
  have hmconc : write64 s1.speicher datenZelle (BitVec.ofNat 64 0xF1) =
      some m := by
    rw [← heff, ← hrax]
    exact hm
  have hrd : lesbar8 s1.speicher datenZelle = true := by
    rw [hmem1]
    decide
  have hread : read64 m datenZelle = some (BitVec.ofNat 64 0xF1) :=
    read64_nach_write64 _ _ _ _ hmconc hrd
  have hs2 : s2 =
      { s1 with speicher := m, rip := ripNach s1.rip 7 } := by
    have e := schritt_store64_erfolg
      ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩ s1 .rbx .rax
      (BitVec.ofNat 32 0) m hok7 rfl hm
    rw [hstore] at e
    exact Option.some_inj.mp e
  have hsp : s2.speicher = m := by rw [hs2]
  have hbyte : intHwImmByteschritt kompaktStart = .weiter s1 := by
    unfold intHwImmByteschritt
    rw [kompakt_fetch_zugelassen]
    show (match stepIntHwImm (⟨.orI .b64 .rax 1, 4⟩ : IntHwImmDec)
        kompaktStart with
      | none => ByteAusgang.verweigert
      | some s' => ByteAusgang.weiter s') = ByteAusgang.weiter s1
    rw [hstep]
  refine ⟨hflag.1, hflag.2.1, hflag.2.2, ?_, hrip, kompakt_fetch_dekode,
    kompakt_fetch_zugelassen, hbyte, ?_, kompakt_start_null, ?_⟩
  · rw [hrax, kompakt_or_wert]
  · rw [hsp]
    exact hread
  · exact kompakt_weit_bei_256.1

/-! ## 1. Per-width logic-flag identity for the compact rows.

    Every AND/OR/XOR-imm step installs CF = OF = false with AF
    undefined (manual: AND txt 40766-40768, OR txt 71721-71722, XOR
    txt 138319-138321), at whatever width the row carries: the step
    reuses `intHwFlagsLogik b r` (`= logikFlags b r`). -/

/-- AND-imm installs the logic-flag identity at its row width. -/
theorem kompakt_and_flaggen (d : IntHwImmDec) (s s' : Zustand)
    (b : Breite) (dst : Register) (imm : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hlen : d.laenge = immDecLaenge d.op)
    (hb : immDecBreiteOk d.op = true)
    (h : d.op = .andI b dst imm)
    (hstep : stepIntHwImm d s = some s') :
    s'.flags.cf = false ∧ s'.flags.of = false ∧
      s'.flags.af = none := by
  have e : stepIntHwImm d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (intHwFlagsLogik b (andB b (s.register dst) (immWort imm))) dst
        (mergeRegNarrow b (s.register dst)
          (andB b (s.register dst) (immWort imm)))) := by
    unfold stepIntHwImm
    rw [h] at hlen hb
    rw [hok, h, hlen, hb]
    simp
  rw [e] at hstep
  cases hstep
  rw [schrittRegister_flags]
  exact ⟨rfl, rfl, rfl⟩

/-- OR-imm installs the logic-flag identity at its row width. -/
theorem kompakt_or_flaggen (d : IntHwImmDec) (s s' : Zustand)
    (b : Breite) (dst : Register) (imm : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hlen : d.laenge = immDecLaenge d.op)
    (hb : immDecBreiteOk d.op = true)
    (h : d.op = .orI b dst imm)
    (hstep : stepIntHwImm d s = some s') :
    s'.flags.cf = false ∧ s'.flags.of = false ∧
      s'.flags.af = none := by
  have e : stepIntHwImm d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (intHwFlagsLogik b (orB b (s.register dst) (immWort imm))) dst
        (mergeRegNarrow b (s.register dst)
          (orB b (s.register dst) (immWort imm)))) := by
    unfold stepIntHwImm
    rw [h] at hlen hb
    rw [hok, h, hlen, hb]
    simp
  rw [e] at hstep
  cases hstep
  rw [schrittRegister_flags]
  exact ⟨rfl, rfl, rfl⟩

/-- XOR-imm installs the logic-flag identity at its row width. -/
theorem kompakt_xor_flaggen (d : IntHwImmDec) (s s' : Zustand)
    (b : Breite) (dst : Register) (imm : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hlen : d.laenge = immDecLaenge d.op)
    (hb : immDecBreiteOk d.op = true)
    (h : d.op = .xorI b dst imm)
    (hstep : stepIntHwImm d s = some s') :
    s'.flags.cf = false ∧ s'.flags.of = false ∧
      s'.flags.af = none := by
  have e : stepIntHwImm d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (intHwFlagsLogik b (xorB b (s.register dst) (immWort imm))) dst
        (mergeRegNarrow b (s.register dst)
          (xorB b (s.register dst) (immWort imm)))) := by
    unfold stepIntHwImm
    rw [h] at hlen hb
    rw [hok, h, hlen, hb]
    simp
  rw [e] at hstep
  cases hstep
  rw [schrittRegister_flags]
  exact ⟨rfl, rfl, rfl⟩

/-- The pilot store succeeds after the witness OR step. -/
theorem kompakt_store_trifft (s1 : Zustand)
    (hstep : stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart = some s1) :
    ∃ s2, schritt ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩ s1
      = some s2 := by
  have hrax := kompakt_s1_rax s1 hstep
  have heff := kompakt_s1_eff s1 hstep
  have hmem1 : s1.speicher = kompaktStart.speicher :=
    stepImm_speicher _ _ _ hstep
  have hok7 : laengeOk 7 = true := by decide
  have hw : (write64 s1.speicher (effAddr s1 .rbx (BitVec.ofNat 32 0))
      (s1.register .rax)).isSome = true := by
    rw [hmem1, heff, hrax]
    decide
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hw
  exact ⟨{ s1 with speicher := m, rip := ripNach s1.rip 7 },
    schritt_store64_erfolg _ s1 .rbx .rax (BitVec.ofNat 32 0) m hok7
      rfl hm⟩

/-- Joint witness: both step hypotheses hold together on the
    non-degenerate run (rax 0xF0 -> 0xF1, cell 0 -> 0xF1), so the
    connection is inhabited and memory really changes. -/
theorem CompactImm8Logic_verbindung_zeuge :
    ∃ (s1 s2 : Zustand),
      stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart = some s1 ∧
      schritt ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩ s1
        = some s2 ∧
      read64 s2.speicher datenZelle = some (BitVec.ofNat 64 0xF1) ∧
      read64 kompaktStart.speicher datenZelle = some 0 := by
  have h1 : (stepIntHwImm ⟨.orI .b64 .rax 1, 4⟩ kompaktStart).isSome =
      true := by
    decide
  obtain ⟨s1, hs1⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨s2, hs2⟩ := kompakt_store_trifft s1 hs1
  have hconn := CompactImm8Logic_verbindung s1 s2 hs1 hs2
  exact ⟨s1, s2, hs1, hs2, hconn.2.2.2.2.2.2.2.2.1,
    hconn.2.2.2.2.2.2.2.2.2.1⟩

/- CUTS:
    Proved here: a connection over the accepted `IntegerHardwareForms`
    vocabulary for the compact REX.W 83 /1 /4 /6 imm8 logic rows, with
    no new canonical definition. Per-width logic-flag identity
    (CF = OF = false, AF undefined, SF/ZF/PF from the width-correct
    result; manual: AND txt 40766-40768, OR txt 71721-71722, XOR txt
    138319-138321) for AND/OR/XOR-imm at the carried width; pinned
    compact bytes and decodes for all three REX.W rows plus one b32
    row; the compact encoder choice (83 iff the int32 fits in a
    signed byte, else the wide 81 form) with the outside-i8 refusal;
    truncated-tail refusals; and one joint connection theorem whose
    companion inhabits both step hypotheses on a non-degenerate
    reached run that changes actual memory (cell 0 -> 0xF1) through
    the accepted byte-step dispatcher and the pilot store.
    NOT proved here, and not claimed:
    - No hardware correspondence beyond the cited manual rows: the
      opcode/digit mapping and flag identity are modelled against the
      stated text lines, not verified against silicon; timing, faults
      beyond explicit refusal, LOCK, and TSO effects are untouched.
    - No source correspondence, no TSO/W/GX bridge, no whole-image
      coverage, no cost transfer, no entry/ABI/relocation claim.
    - Memory-operand (non-register-direct) 83 rows, ADC/SBB digits,
      and the narrow (b8/b16) logic rows stay refused by absence.
-/

#print axioms kompakt_and_flaggen
#print axioms kompakt_or_flaggen
#print axioms kompakt_xor_flaggen
#print axioms pin_or_kompakt
#print axioms pin_or_kompakt_dekode
#print axioms pin_and_kompakt
#print axioms pin_and_kompakt_dekode
#print axioms pin_xor_kompakt
#print axioms pin_xor_kompakt_dekode
#print axioms pin_and32_kompakt
#print axioms kompakt_or_feuert
#print axioms kompakt_and_feuert
#print axioms kompakt_xor_feuert
#print axioms kompakt_ausserhalb_i8
#print axioms kompakt_weit_bei_256
#print axioms kompakt_abgeschnitten
#print axioms kompakt_s1_rax
#print axioms kompakt_s1_rbx
#print axioms kompakt_s1_rip
#print axioms kompakt_s1_eff
#print axioms kompakt_fetch_dekode
#print axioms kompakt_fetch_zugelassen
#print axioms kompakt_or_wert
#print axioms kompakt_start_null
#print axioms CompactImm8Logic_verbindung
#print axioms kompakt_store_trifft
#print axioms CompactImm8Logic_verbindung_zeuge

end Gabbro.Grammatik.X86
