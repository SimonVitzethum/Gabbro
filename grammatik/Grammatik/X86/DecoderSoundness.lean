/-
  Arbitrary-input pilot decoder soundness (lane 559).

  Closes the `Codec` CUT for arbitrary successfully decoded bytes from the
  decoder side only: every successful `decode` of an ARBITRARY byte list
  consumes exactly its stated length within 1..15, the rest is the exact
  suffix, and the fetched window splits the same way. All decoder-side
  length facts are derived from the reused `DecodingCoverage.decode_abdeckung`
  over the reused `Codec.decode`; this file adds no second decoder and no
  encoder round trip. Fetch facts go through the reused
  `Byteschritt.fetchDekodiert` correspondence. No hardware, source, TSO or
  whole-image claim is made here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.DecodingCoverage

namespace Gabbro.Grammatik.X86

/-- A valid decode length is within the 1..15 architectural bound. -/
theorem laengeOk_grenzen (l : Nat) (h : laengeOk l = true) :
    1 ≤ l ∧ l ≤ 15 := by
  unfold laengeOk at h
  exact of_decide_eq_true h

/-! ## 1. Generic decoder soundness over arbitrary input. -/

/-- CONSUMED-LENGTH/SUFFIX AGREEMENT with 1..15 bounds: every successful
    `decode` of an ARBITRARY byte list consumes exactly its stated length
    (the rest is the exact drop-suffix) within the architectural bound.
    Combines the reused decoder-side coverage with the window congruence;
    no encoder round trip is used. -/
theorem decode_verbraucht_praefix (bs : List Byte) (d : Decodiert)
    (rest : List Byte) (h : decode bs = some (d, rest)) :
    d.laenge + rest.length = bs.length ∧
      rest = bs.drop d.laenge ∧
      1 ≤ d.laenge ∧ d.laenge ≤ 15 := by
  obtain ⟨heq, hok, _, _⟩ := decode_abdeckung bs d rest h
  obtain ⟨hsuffix, _⟩ := decode_fenster_kongruenz bs d rest h
  obtain ⟨hlo, hhi⟩ := laengeOk_grenzen d.laenge hok
  exact ⟨heq, hsuffix, hlo, hhi⟩

/-! ## 2. Fetched-window/decode length properties. -/

/-- FETCHED CONSUMED-LENGTH AGREEMENT: a successful `fetchDekodiert` over
    actual executable memory carries the decoder soundness into the fetched
    window: stated length plus rest is the fetched window, the rest is the
    exact drop-suffix, the length is within 1..15 and fits the window (which
    fits the 15-byte cap), and the consumed prefix is executable. Derived
    from the generic decoder agreement through the reused
    fetch-to-decoder correspondence; the runtime length check is implied,
    never assumed. -/
theorem fetch_verbraucht_praefix (s : Zustand) (d : Decodiert)
    (rest : List Byte) (hf : fetchDekodiert s = some (d, rest)) :
    d.laenge + rest.length = (geholt s).length ∧
      rest = (geholt s).drop d.laenge ∧
      1 ≤ d.laenge ∧ d.laenge ≤ 15 ∧
      d.laenge ≤ (geholt s).length ∧ (geholt s).length ≤ fetchCap ∧
      ausfuehrbarN s.speicher s.rip d.laenge = true := by
  obtain ⟨hdec, _, _, hexe⟩ := fetchDekodiert_entspricht s d rest hf
  obtain ⟨heq, hsuffix, hlo, hhi⟩ := decode_verbraucht_praefix _ d rest hdec
  obtain ⟨_, hfit, hcap⟩ := fetch_nutzt_nur_praefix s d rest hf
  exact ⟨heq, hsuffix, hlo, hhi, hfit, hcap, hexe⟩

/-! ## 3. Branch probes: hand-written bytes with trailing bytes. -/

/-- Independently constructed inputs are literal bytes (never `encode`
    output); each carries a trailing byte proving the suffix passes
    through untouched. This batch covers the short dispatch branches:
    `ret`, `call32`, `jump32`, `jumpIf32`, low/high `push`/`pop`. -/
theorem sonde_ret_mit_rest :
    decode [natByte 195, natByte 7] =
      some ((⟨.ret, 1⟩ : Decodiert), [natByte 7]) := by
  decide

/-- Hand-written `call32` with a trailing byte. -/
theorem sonde_call32_mit_rest :
    decode [natByte 232, natByte 3, natByte 0, natByte 0, natByte 0,
      natByte 9] =
      some ((⟨.call32 3, 5⟩ : Decodiert), [natByte 9]) := by
  decide

/-- Hand-written `jump32` with a trailing byte. -/
theorem sonde_jump32_mit_rest :
    decode [natByte 233, natByte 1, natByte 0, natByte 0, natByte 0,
      natByte 9] =
      some ((⟨.jump32 1, 5⟩ : Decodiert), [natByte 9]) := by
  decide

/-- Hand-written conditional jump (`je`, second byte 132) with trailing. -/
theorem sonde_jumpIf32_mit_rest :
    decode [natByte 15, natByte 132, natByte 2, natByte 0, natByte 0,
      natByte 0, natByte 9] =
      some ((⟨.jumpIf32 .e 2, 6⟩ : Decodiert), [natByte 9]) := by
  decide

/-- Hand-written low `push` (`rcx`) with a trailing byte. -/
theorem sonde_push64_niedrig_mit_rest :
    decode [natByte 81, natByte 41] =
      some ((⟨.push64 .rcx, 1⟩ : Decodiert), [natByte 41]) := by
  decide

/-- Hand-written low `pop` (`rcx`) with a trailing byte. -/
theorem sonde_pop64_niedrig_mit_rest :
    decode [natByte 89, natByte 41] =
      some ((⟨.pop64 .rcx, 1⟩ : Decodiert), [natByte 41]) := by
  decide

/-- Hand-written high `push` (`r8`) with a trailing byte. -/
theorem sonde_push64_hoch_mit_rest :
    decode [natByte 65, natByte 80, natByte 11] =
      some ((⟨.push64 .r8, 2⟩ : Decodiert), [natByte 11]) := by
  decide

/-- Hand-written high `pop` (`r15`) with a trailing byte. -/
theorem sonde_pop64_hoch_mit_rest :
    decode [natByte 65, natByte 95, natByte 11] =
      some ((⟨.pop64 .r15, 2⟩ : Decodiert), [natByte 11]) := by
  decide

/-! ## 4. REX-branch probes: immediates, register and memory forms. -/

/-- Hand-written `movImm64` to `rax` with a trailing byte. -/
theorem sonde_movImm64_rax_mit_rest :
    decode [natByte 72, natByte 184, natByte 1, natByte 0, natByte 0,
      natByte 0, natByte 0, natByte 0, natByte 0, natByte 0, natByte 13] =
      some ((⟨.movImm64 .rax 1, 10⟩ : Decodiert), [natByte 13]) := by
  decide

/-- Hand-written `movImm64` to `r8` (extended prefix) with trailing. -/
theorem sonde_movImm64_r8_mit_rest :
    decode [natByte 73, natByte 184, natByte 8, natByte 7, natByte 6,
      natByte 5, natByte 4, natByte 3, natByte 2, natByte 1, natByte 55] =
      some ((⟨.movImm64 .r8 0x0102030405060708, 10⟩ : Decodiert),
        [natByte 55]) := by
  decide

/-- Hand-written register move with a trailing byte. -/
theorem sonde_movReg64_mit_rest :
    decode [natByte 72, natByte 137, natByte 216, natByte 31] =
      some ((⟨.movReg64 .rax .rbx, 3⟩ : Decodiert), [natByte 31]) := by
  decide

/-- Hand-written register add with a trailing byte. -/
theorem sonde_addReg64_mit_rest :
    decode [natByte 72, natByte 1, natByte 216, natByte 31] =
      some ((⟨.addReg64 .rax .rbx, 3⟩ : Decodiert), [natByte 31]) := by
  decide

/-- Hand-written register subtract with a trailing byte. -/
theorem sonde_subReg64_mit_rest :
    decode [natByte 72, natByte 41, natByte 216, natByte 31] =
      some ((⟨.subReg64 .rax .rbx, 3⟩ : Decodiert), [natByte 31]) := by
  decide

/-- Hand-written register xor with a trailing byte. -/
theorem sonde_xorReg64_mit_rest :
    decode [natByte 72, natByte 49, natByte 216, natByte 31] =
      some ((⟨.xorReg64 .rax .rbx, 3⟩ : Decodiert), [natByte 31]) := by
  decide

/-- Hand-written register compare with a trailing byte. -/
theorem sonde_cmpReg64_mit_rest :
    decode [natByte 72, natByte 57, natByte 216, natByte 31] =
      some ((⟨.cmpReg64 .rax .rbx, 3⟩ : Decodiert), [natByte 31]) := by
  decide

/-- Hand-written extended-register add (both REX bits) with trailing. -/
theorem sonde_addReg64_erweitert_mit_rest :
    decode [natByte 77, natByte 1, natByte 249, natByte 21] =
      some ((⟨.addReg64 .r9 .r15, 3⟩ : Decodiert), [natByte 21]) := by
  decide

/-- Hand-written load through `rbp` (disp32, no SIB) with trailing. -/
theorem sonde_load64_ohne_sib_mit_rest :
    decode [natByte 72, natByte 139, natByte 141, natByte 0, natByte 0,
      natByte 0, natByte 0, natByte 33] =
      some ((⟨.load64 .rcx .rbp 0, 7⟩ : Decodiert), [natByte 33]) := by
  decide

/-- Hand-written store through `r13` (disp32, no SIB) with trailing. -/
theorem sonde_store64_ohne_sib_mit_rest :
    decode [natByte 77, natByte 137, natByte 133, natByte 1, natByte 0,
      natByte 0, natByte 0, natByte 33] =
      some ((⟨.store64 .r13 .r8 1, 7⟩ : Decodiert), [natByte 33]) := by
  decide

/-- Hand-written load through `rsp` (SIB byte) with a trailing byte. -/
theorem sonde_load64_sib_mit_rest :
    decode [natByte 72, natByte 139, natByte 132, natByte 36, natByte 16,
      natByte 0, natByte 0, natByte 0, natByte 33] =
      some ((⟨.load64 .rax .rsp 16, 8⟩ : Decodiert), [natByte 33]) := by
  decide

/-- Hand-written store through `r12` (SIB byte) with a trailing byte. -/
theorem sonde_store64_sib_mit_rest :
    decode [natByte 73, natByte 137, natByte 148, natByte 36, natByte 0,
      natByte 0, natByte 0, natByte 0, natByte 33] =
      some ((⟨.store64 .r12 .rdx 0, 8⟩ : Decodiert), [natByte 33]) := by
  decide

/-! ## 5. Refusal probes: truncated and corrupted inputs stay shut. -/

/-- A lone extended REX prefix is truncated. -/
theorem decoder_weist_rex73_allein_zurueck :
    decode [natByte 73] = none := rfl

/-- An immediate with only three of eight bytes is truncated. -/
theorem decoder_weist_imm_abgeschnitten_zurueck :
    decode [natByte 72, natByte 184, natByte 1, natByte 0,
      natByte 0] = none := rfl

/-- A SIB access with only two of four displacement bytes is truncated. -/
theorem decoder_weist_sib_versatz_kurz_zurueck :
    decode [natByte 72, natByte 139, natByte 132, natByte 36, natByte 16,
      natByte 0] = none := rfl

/-- A full-length access with a forged SIB byte (37, not 36) is refused. -/
theorem decoder_weist_sib_falsch_zurueck :
    decode [natByte 72, natByte 139, natByte 132, natByte 37, natByte 0,
      natByte 0, natByte 0, natByte 0] = none := rfl

/-- An unknown first opcode byte (198) is refused. -/
theorem decoder_weist_opcode_falsch_zurueck :
    decode [natByte 198] = none := rfl

/-- A load with a mod=1 ModRM byte is not canonical and refused. -/
theorem decoder_weist_modus_eins_laden_zurueck :
    decode [natByte 72, natByte 139, natByte 69] = none := rfl

/-- A two-byte branch opener with a non-branch second byte is refused. -/
theorem decoder_weist_zweig_pseudo_zurueck :
    decode [natByte 15, natByte 200, natByte 0, natByte 0, natByte 0,
      natByte 0] = none := rfl

/-- A call with only two of four displacement bytes is truncated. -/
theorem decoder_weist_call_kurz_zurueck :
    decode [natByte 232, natByte 1, natByte 2] = none := rfl

/-- An extension prefix with a byte in neither push nor pop range is refused. -/
theorem decoder_weist_schub_falsch_zurueck :
    decode [natByte 65, natByte 70] = none := rfl

/-! ## 6. Joint witnesses: agreement plus memory-changing execution. -/

/-- JOINT DECODE WITNESS: a hand-written store with a trailing byte meets
    the generic agreement (length equation plus bounds), and its `schritt`
    on the concrete witness state moves 42 into actual memory (zero to 42
    at the data address). -/
theorem decode_verbraucht_praefix_zeuge :
    ∃ (bs : List Byte) (d : Decodiert) (rest : List Byte),
      decode bs = some (d, rest) ∧ d.laenge + rest.length = bs.length ∧
      1 ≤ d.laenge ∧ d.laenge ≤ 15 ∧
      dcStart.speicher.bytes (BitVec.ofNat 64 8192) = BitVec.ofNat 8 0 ∧
      (schritt d dcStart).map
        (fun s' => s'.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (BitVec.ofNat 8 42) := by
  refine ⟨[natByte 72, natByte 137, natByte 131, natByte 0, natByte 0,
    natByte 0, natByte 0, natByte 195],
    ⟨.store64 .rbx .rax 0, 7⟩, [natByte 195],
    by decide, by decide, by decide, by decide, rfl, by decide⟩

/-- JOINT FETCH WITNESS: fetching the actual store bytes from executable
    memory meets the fetched agreement (window equation plus bounds), and
    the byte step moves 42 into actual memory (zero to 42). -/
theorem fetch_verbraucht_praefix_zeuge :
    ∃ (s : Zustand) (d : Decodiert) (rest : List Byte),
      fetchDekodiert s = some (d, rest) ∧
      d.laenge + rest.length = (geholt s).length ∧
      1 ≤ d.laenge ∧ d.laenge ≤ 15 ∧
      s.speicher.bytes (BitVec.ofNat 64 8192) = BitVec.ofNat 8 0 ∧
      ausgangByte (BitVec.ofNat 64 8192) (byteschritt s) =
        some (BitVec.ofNat 8 42) := by
  refine ⟨dcAbholStart, ⟨.store64 .rbx .rax 0, 7⟩,
    List.replicate 8 (natByte 0), by decide, by decide, by decide,
    by decide, rfl, by decide⟩

/- CUTS:
    Proved here: the `laengeOk` bound projection (`laengeOk_grenzen`),
    the generic consumed-length/suffix agreement with 1..15 bounds over
    ARBITRARY successfully decoded bytes (`decode_verbraucht_praefix`,
    derived from the reused decoder-side coverage and window congruence,
    never from encoder round trips), the fetched-window/decode agreement
    with executable prefix (`fetch_verbraucht_praefix`, through the reused
    fetch-to-decoder correspondence), hand-written non-roundtrip probes
    with trailing bytes for every pilot dispatch branch (short forms,
    both immediates, all five register operations including an extended
    pair, all four memory shapes), nine truncated/corrupted refusal probes,
    and two joint witnesses tying the agreement to real memory-changing
    execution (zero to 42).
    NOT proved here, and not claimed:
    - No hardware correspondence: soundness is self-consistency of the
      pilot decoder; correspondence to silicon is open.
    - No complete x86 coverage: only the 14 canonical pilot forms carry
      theorems; other instructions, prefixes, addressing modes and operand
      sizes are refused by construction and uncovered here.
    - No source correspondence, no TSO or multi-byte-atomicity bridge, no
      concurrency, and no cost, ABI, entry or relocation claim.
    - No whole-image validation: one window decodes at a time; image
      coverage and control-flow validation stay with the closing
      validator (lanes 560/561/575 consume this interface).
    - No termination claim: refusal is the absence of a transition, never
      a halt; budget stops are untouched.
-/

#print axioms laengeOk_grenzen
#print axioms decode_verbraucht_praefix
#print axioms fetch_verbraucht_praefix
#print axioms sonde_ret_mit_rest
#print axioms sonde_call32_mit_rest
#print axioms sonde_jump32_mit_rest
#print axioms sonde_jumpIf32_mit_rest
#print axioms sonde_push64_niedrig_mit_rest
#print axioms sonde_pop64_niedrig_mit_rest
#print axioms sonde_push64_hoch_mit_rest
#print axioms sonde_pop64_hoch_mit_rest
#print axioms sonde_movImm64_rax_mit_rest
#print axioms sonde_movImm64_r8_mit_rest
#print axioms sonde_movReg64_mit_rest
#print axioms sonde_addReg64_mit_rest
#print axioms sonde_subReg64_mit_rest
#print axioms sonde_xorReg64_mit_rest
#print axioms sonde_cmpReg64_mit_rest
#print axioms sonde_addReg64_erweitert_mit_rest
#print axioms sonde_load64_ohne_sib_mit_rest
#print axioms sonde_store64_ohne_sib_mit_rest
#print axioms sonde_load64_sib_mit_rest
#print axioms sonde_store64_sib_mit_rest
#print axioms decoder_weist_rex73_allein_zurueck
#print axioms decoder_weist_imm_abgeschnitten_zurueck
#print axioms decoder_weist_sib_versatz_kurz_zurueck
#print axioms decoder_weist_sib_falsch_zurueck
#print axioms decoder_weist_opcode_falsch_zurueck
#print axioms decoder_weist_modus_eins_laden_zurueck
#print axioms decoder_weist_zweig_pseudo_zurueck
#print axioms decoder_weist_call_kurz_zurueck
#print axioms decoder_weist_schub_falsch_zurueck
#print axioms decode_verbraucht_praefix_zeuge
#print axioms fetch_verbraucht_praefix_zeuge

end Gabbro.Grammatik.X86
