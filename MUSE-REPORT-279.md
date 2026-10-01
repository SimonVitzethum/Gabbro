# Muse Report 279: Pilot byte codec and generic round-trip

Lane 279, wave B. Owner files only: `grammatik/Grammatik/X86/Codec.lean`,
one additive umbrella import (`import Grammatik.X86.Codec` at the end of
`grammatik/Grammatik.lean`, committed with the skeleton), and this report.
No Typen/goal/checker/emit/TODO/AGENTS/SATZKARTE/MARKE_EMIT changes, no
diagnostic/gift/example/CLI numbers, no new `Befehl` or state.

## What was done

Implemented the actual canonical byte encoder and first-instruction decoder
for all 14 `Befehl` constructors per `dokumente/x86/BYTE-PILOT.md`, and proved
the universal round trip with the exact TARGET statement:

- `roundtrip (b : Befehl) (suffix : List Byte) :
  decode (encode b ++ suffix) = some (⟨b, (encode b).length⟩, suffix)`
- `encode : Befehl → List Byte`, `decode : List Byte → Option (Decodiert × List Byte)`
- `encode_len`: every encoding satisfies `1 ≤ length ∧ length ≤ 15`.
- `roundtrip_len_ok`: on a successful round trip the decoded length is the
  consumed prefix length (`n + rest.length = total.length`) within 1..15.

The decoder parses bytes directly (first-byte dispatch, REX/opcode/ModRM/SIB
matching, little-endian reassembly). It never calls `encode`, never measures
against an emitter length, and never uses encode-equality over any instruction
enumeration. Register/condition reconstruction goes through `codeReg`/`codeCond`
with the generic inverses `codeReg_regCode`/`codeCond_condCode` as load-bearing
rewrite facts. Register-pair round trips (mov/add/sub/xor/cmp) and push/pop
close by kernel `rfl` after casing — i.e. definitional unfolding through the
parser, not search.

## New definitions and theorems (`Gabbro.Grammatik.X86`)

Codes: `regCode`, `codeReg`, `codeReg_regCode`, `regCode_lt`, `condCode`,
`codeCond`, `codeCond_condCode`, `condCode_lt`, `regHigh`, `regLow`,
`regHigh_lt`, `regLow_lt`, `regCode_split`, `rexByte`, `modrmReg`, `modrmMem`.
Bytes: `natByte`, `byteNat`, `byteNat_natByte_of_lt`, `natByte_byteNat`,
`byteNat_natByte_mod`, `byteNat_natByte_any` (@[simp]).
Little-endian: `leBytes32`, `parseLe32`, `parseLe32_leBytes32`, `leBytes64`,
`parseLe64`, `parseLe64_leBytes64`, `length_leBytes32`, `length_leBytes64`,
`parseLe32_cons`, `parseLe64_cons`.
Codec: `encode`, `encode_len`, `decodeRegReg`, `decodeMem`, `decodeModrm`,
`decodeRex`, `decode`.
Round trips: `roundtrip_ret`, `roundtrip_jump32`, `roundtrip_movReg64`,
`roundtrip_addReg64`, `roundtrip_subReg64`, `roundtrip_xorReg64`,
`roundtrip_cmpReg64`, `roundtrip_call32`, `roundtrip_jumpIf32`,
`roundtrip_push64`, `roundtrip_pop64`, `roundtrip_movImm64`,
`roundtrip_load64`, `roundtrip_store64`, `roundtrip`, `roundtrip_len_ok`.
Refusals (15): `decode_nichts_leer`, `decode_nichts_rex_allein`,
`decode_nichts_sprung_kurz`, `decode_nichts_zweibyte_allein`,
`decode_nichts_erweiterung_allein`, `decode_nichts_unbekannt`,
`decode_nichts_rex_x`, `decode_nichts_ohne_rex`, `decode_nichts_modus_null`,
`decode_nichts_lade_register`, `decode_nichts_sib_falsch`,
`decode_nichts_sib_kurz`, `decode_nichts_kurzsprung`, `decode_nichts_vorsatz`,
`decode_nichts_zweite_kein_sprung`.
Pins (22, bytes hand-computed from the contract, verified by `decide`):
`pin_movImm64_r8[_dekode]`, `pin_addReg64_erweitert[_dekode]`,
`pin_load64_rsp[_dekode]`, `pin_store64_r12[_dekode]`,
`pin_load64_rbp[_dekode]`, `pin_store64_r13[_dekode]`,
`pin_jump32_negativ[_dekode]`, `pin_push64_r8[_dekode]`,
`pin_pop64_r15[_dekode]`, `pin_ret[_dekode]`.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (369 jobs)`. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`. Axioms: inverses and `encode_len` axiom-free;
LE round trips `[propext, Quot.sound]`; `roundtrip`/`roundtrip_len_ok`
exactly `[propext, Classical.choice, Quot.sound]`; pins/refusals `[propext]`.

## Open / unclosed bridge (precise)

- No hardware correspondence: the round trip is self-consistency against
  BYTE-PILOT.md, not x86 truth. No source correspondence, execution, TSO
  bridge, ABI/image coverage, or cost transfer — none claimed.
- General length soundness (EVERY successful decode of an ARBITRARY input
  consumes exactly its stated length in 1..15) is proved only for round-trip
  instances (`roundtrip_len_ok`); the arbitrary-input version is open.
- The refusal set for non-canonical-but-architecturally-valid encodings is
  by construction; its correspondence to hardware is open.
- `set_option maxHeartbeats 4000000` scopes the two exhaustive 256-combination
  proofs (`roundtrip_load64`, `roundtrip_store64`) and is restored to 200000
  right after; single-pair cost is small, the budget is purely multiplicative.

## Notes on the task (all satisfied, one remark)

Every required pin is present (r8 immediate, extended-register arithmetic,
rsp AND r12 SIB, rbp AND r13 mod-10 disp32, negative branch displacement,
high-register push AND pop, RET) plus corrupted-opcode and
malformed/truncated-prefix refusals. Remark: `simp only` does not evaluate
closed Nat `/`, `%`, `==` in this toolchain (probed: `0 / 8`, `0 % 8 == 4`
do not reduce under `simp only []`), so the register-pair proofs use full
`simp` with explicit lemma sets (fast per goal) instead of `simp only`;
nothing in the task forbids this.
