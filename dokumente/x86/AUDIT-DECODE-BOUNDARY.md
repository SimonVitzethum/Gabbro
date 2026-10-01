# Audit: decode boundary (lane 406)

*Scope: `grammatik/Grammatik/X86/Codec.lean` (byte codec, lane 279),
`grammatik/Grammatik/X86/Byteschritt.lean` (fetch/decode/step, lane 319),
and their consumers, as merged at `0b3132b7`.
Read against `dokumente/x86/BYTE-PILOT.md`, `DIRECT-COMPILER-DESIGN.md` §§2-3,
`dokumente/x86/WORK-ALLOCATION.md` and the accepted `X86/Typen.lean` +
`X86/Ausfuehrung.lean`. Eight concrete Lean probes reproduced in
`.tmp/probe406_decode.lean` (private scratch, `./lean-probe`: 0 errors);
nothing in `grammatik/` was touched. Line numbers are as read on 2026-10-01.*

## 0. What this audit is not

No second architecture review: prior audits (`REVIEW-GRUNDLAGEN.md`,
`REVIEW-TSO.md`, `REVIEW-OPT-BINAER.md`, `REVIEW-QUELLE-INVARIANTEN.md`)
stand. No hardware correspondence is claimed by the audited files and none
is checked here. The explicitly OPEN bridges below are OPEN; they are
recorded as missing lemmas with named owners, not as bugs.

## 1. Implementation map

- Vocabulary: `Typen.lean` L53-68 fixes exactly 14 `Befehl` constructors;
  `Decodiert` (`Typen.lean` L70-73) is a bare pair `(befehl, laenge)` with
  **no provenance evidence** (which bytes, which address, which decode).
- Decoder: `Codec.decode` (`Codec.lean` L400-453) dispatches on the first
  byte, then `decodeRex` (L375-395), `decodeModrm` (L359-372),
  `decodeRegReg` (L316-327), `decodeMem` (L331-354), `parseLe32/parseLe64`.
  Only canonical `BYTE-PILOT.md` encodings are accepted; everything else
  answers `none`.
- Sole decoder consumer: `Byteschritt.fetchDekodiert` (`Byteschritt.lean`
  L49-56). Confirmed by grep: no other module under `grammatik/`
  imports `Grammatik.X86.Codec` except the `Grammatik.lean` umbrella.
  `ControlFlow`, `LockedOps`, `Bild`, `Relokation`, `Zugriffe` do not
  import it. Newer ISA side types (`MulDivBefehl` in `MulDiv.lean` L33,
  shift/logic/locked analogues) define their own step functions over
  their own types; **no decoder row accepts their bytes** (safe direction:
  `byteschritt` refuses them, it cannot mis-execute them).
- Sole execution entry over real bytes: `byteschritt` (`Byteschritt.lean`
  L70-76) takes ONLY the state, never a caller-supplied `Decodiert`, so a
  forged pair cannot be injected through it. `Ausfuehrung.schritt`
  (`Ausfuehrung.lean` L69-72) by contrast trusts any caller-supplied
  `(befehl, laenge)` apart from the `laengeOk` gate.

## 2. Executed-byte decode length: per-path accounting (verified by reading)

Every success path returns a literal length; each equals the bytes its
path structurally consumes:

| Path (Codec.lean) | Consumed | Returned `laenge` | Match |
|---|---|---|---|
| `ret` L404 | 1 (`C3`) | 1 | yes |
| `call32` L405-408 | 1 + disp32 (4) | 5 | yes |
| `jump32` L409-412 | 1 + 4 | 5 | yes |
| `jumpIf32` L413-425 | 2 + 4 | 6 | yes |
| `push64`/`pop64` high, `41`-prefix L426-439 | 2 | 2 | yes |
| `movImm64` via `decodeRex` L380-386 | REX + opcode + imm64 (8) | 10 | yes |
| reg-reg via `decodeRegReg` L316-327 | REX + opcode + ModRM | 3 | yes |
| mem via `decodeMem`, no SIB L346-354 | REX + opcode + ModRM + disp32 | 7 | yes |
| mem via `decodeMem`, SIB L335-345 | + SIB byte | 8 | yes |
| `push64`/`pop64` low, catch-all L444-453 | 1 | 1 | yes |

First-byte dispatch is disjoint (195 / 232 / 233 / 15 / 65 / 72,73,76,77 /
80-87 / 88-95, `Codec.lean` L403-453), and the `movImm64` opcode window
184-191 (`decodeRex` L380) is disjoint from the ModRM opcodes
137/1/41/49/57/139, whose reg-reg vs mem readings are split by the ModRM
mod field 3 vs 2 (`decodeModrm` L365-372; opcode 139 with mod=3 falls
through to `none`, so `load64` can never alias a register-direct form).
No canonical encoding is a strict prefix of another: lengths follow from
the first (and where needed second/ModRM) byte. All of this paragraph is
true by inspection and used by the code, but **none of it is a proved
lemma**; see §6 for the exact open statements.

## 3. Suffix handling (proved for round-trip instances)

`roundtrip` (`Codec.lean` L561-578) proves, per constructor with an
arbitrary suffix, that `decode (encode b ++ suffix)` returns exactly
`suffix` untouched. So the decoder never consumes suffix bytes and never
invents bytes on canonical inputs. Reproduced concretely:
`decode [C3, 00] = some ((ret,1), [00])` and
`decode (encode (movReg64 rax r15) ++ [C3])` keeps `[C3]` (probes 1-2,
0 errors). `parseLe32/parseLe64` take fixed counts and answer `none` on
short input, so a decoder can never read past the first instruction.

## 4. Malformed / overlong / truncated refusal

Pinned in `Codec.lean` L591-646 (`decode_nichts_*`: empty, lone REX,
short jump/displacement, lone `0F`, lone `41`, unknown opcode 255,
REX.X=74, REX-less register op, mod=0, register-direct load, wrong SIB,
short SIB displacement, short branch `EB`, `66` prefix, non-branch `0F 90`)
plus RSP/R12-SIB, RBP/R13-disp32, negative-displacement and high-reg
push/pop pins. The file's claim "explicit refusals of truncated,
non-canonical and corrupted inputs" checks out for what it pins.

Probed additionally (all `= none`, all pass, `.tmp/probe406_decode.lean`):

- mod=1 (`register plus disp8`): `[48,89,45]` refused — structurally
  inevitable (`decodeModrm` accepts only mod 3/2) but previously unpinned.
- REX 75 (`0x4B`, X bit set) before a register op: refused. (74 was
  pinned; 75/78/79 share the same fall-through to the catch-all, which
  accepts only 80-87/88-95 — verified by reading L440-453.)
- LOCK prefix `F0` before `RET`: refused (falls through all arms).
- `0F 05` (real-hardware syscall): refused — second byte outside 128-143.
- `movImm64` cut to 9 bytes: refused (`parseLe64` needs exactly 8).

No overlong acceptance exists by construction: every path consumes a
fixed count and returns the rest; redundant prefixes (`66`, `F0`, `F2`,
`F3`, `67`, segment overrides, `REX` without `W`, `REX.X`) match no arm.
Greedy-prefix semantics is correct here because encodings are prefix-free
(§2): a shorter canonical instruction can never be a strict prefix of a
longer one, so first-instruction consumption is unambiguous.

## 5. Instruction-entry provenance (the one structural weakness, contained)

`Decodiert` carries no evidence linking `(befehl, laenge)` to bytes or to
an address. Consequences, checked:

- `schritt` (`Ausfuehrung.lean` L69-72) executes any caller-supplied pair
  that passes `laengeOk`. A caller holding a stale/forged `Decodiert`
  (right length, wrong instruction) would step wrongly. Today no such
  caller exists: the only state-driven entry is `byteschritt`, which
  builds the pair from fetched bytes itself.
- `fetchDekodiert` re-establishes provenance at runtime for its one use:
  it decodes the actual fetched window and additionally checks
  `d.laenge + rest.length == fetched.length`, `laengeOk`, and execute
  permission of exactly the consumed prefix (`Byteschritt.lean` L53-55).
  Because `rest` is structurally a suffix of the input on every path,
  the length equation enforces `laenge = bytes actually consumed`.
- `Bild` explicitly books decoded starts as OPEN (`Bild.lean` L530-532:
  section matching, never decoded bytes); control-flow-target decoded-start
  checks belong to the validator skeleton (WORK-ALLOCATION C5 / lane 349),
  not to this boundary.

So provenance is enforced **once, at runtime, at one call site**, not by
the types. That is adequate today and brittle tomorrow: any second direct
consumer of `schritt` or `decode` must repeat the validation.

## 6. Round trip vs soundness vs completeness (exact ledger)

Proved (`Codec.lean`, build green, standard axioms via `./lean-bau`):

- `roundtrip` (L561): decoder completeness on canonical bytes AND
  soundness on those instances — every `encode b` decodes to `(b, len)`.
- `roundtrip_len_ok` (L581): on round-trip instances the consumed length
  is the prefix length within 1..15. The CUTS block (L788-790) honestly
  scopes this to round-trip instances.
- `encode_len` (L279): every canonical encoding is 1..15 bytes.

NOT proved (all three already declared OPEN in the files' own CUTS,
`Codec.lean` L783-792, `Byteschritt.lean` L477-484 — not new findings):

1. General length soundness:
   `forall bs d rest, decode bs = some (d, rest) ->
     d.laenge + rest.length = bs.length /\ 1 <= d.laenge /\ d.laenge <= 15`.
2. Encoder soundness on arbitrary bytes:
   `decode bs = some ((b, n), rest) -> List.take n bs = encode b`
   (no aliasing between distinct instructions off the canonical set).
3. `encode` injectivity (distinct `Befehl`s never share bytes).

The compensating control for (1) is the runtime length equation in
`fetchDekodiert`; canonical agreement for arbitrary *admitted*
instructions goes through round-trip instances only
(`kanonisch_schritt_ueberein`, `Byteschritt.lean` L227-252). This is a
legitimately incomplete deliverable with a working runtime check, not a
false theorem. Its scheduled owner is lane 435 (DecodingCoverage,
DIRECT-COMPILER.md L202); this audit assigns nothing that collides with it.

## 7. Fail-closed properties (positive findings)

- Extending `Befehl` with a new constructor breaks `encode` and
  `roundtrip` exhaustiveness **at compile time**: a new form can never
  silently inherit decode acceptance. Until its codec row (DESIGN §2B
  pattern: encoder row, decoder acceptance, length function,
  correspondence lemma) is added, its bytes are refused by `byteschritt`.
- Fetch can only turn acceptance into refusal, never into mis-decode:
  the 15-byte cap (`fetchCap`, `Byteschritt.lean` L18) exceeds every
  canonical length (max 10); cap truncation yields `none` via the fixed-
  count parsers. `geholt` never over-reads past a non-executable byte
  (proved: `geholt_nur_ausfuehrbar`, `fetch_nutzt_nur_praefix`), and the
  `ret`-at-boundary, truncated-prefix, execute-denied and forged-opcode
  witnesses (`Byteschritt.lean` L339-450) pin exactly this, all `by decide`
  over actual bytes.
- Multi-byte fetch atomicity under concurrent modification (self-
  modifying-code coherence, store-buffer interplay) isOPEN and correctly
  marked so (`Byteschritt.lean` L466-469); per-byte TSO steps elsewhere
  are not claimed to cover it. Not a finding, recorded to prevent one.

## 8. Prioritized repair / bridge tasks

- **P0 — bridge (owner: scheduled lane 435, do not duplicate):** prove
  open statements (1) and preferably (2) of §6. Until then the
  `fetchDekodiert` runtime equation is the load-bearing check; any
  refactor of `fetchDekodiert` must preserve it. No code change proposed
  here.
- **P1 — consumer discipline (owner: validator skeleton lane 349 / root):**
  keep `byteschritt` the sole state-driven decode-then-step entry, or
  introduce a `decodiertOk : List Byte -> Decodiert -> Bool` predicate
  (prefix equation) that every future direct `schritt`/`decode` consumer
  must discharge. One sentence in `DIRECT-COMPILER-DESIGN.md` §2 would
  suffice; suggested text: "No component calls `schritt` with a
  `Decodiert` that did not come from `fetchDekodiert` on the same state's
  fetched window."
- **P2 — coverage freeze discipline (owner: per-extension lanes per
  DESIGN §2B):** keep the rule that a new instruction form ships its
  decoder row, refusal pins for its near-neighbours (wrong mod, wrong
  prefix, truncated tail), and the `roundtrip_*` instance together, or it
  does not merge. No action now.
- **P3 — cheap hardening (owner: codec file owner, optional):** promote
  the §4 unpinned refusals (mod=1, REX 75/78/79, LOCK `F0`, `0F 05`,
  9-byte `movImm`) from my `.tmp` probes into `Codec.lean`
  `decode_nichts_*` pins. Demonstration only; I did not touch the file
  (outside lane ownership).

## 9. Verdict on proofs vs CUTS vs claims

Both files' CUTS blocks are accurate: what is claimed proved is proved
(`./lean-bau` green, 392 jobs, 2026-10-01), what is OPEN is named with
its reason. `DIRECT-COMPILER-DESIGN.md` L116 ("codec round-trip is
PROVED") matches `roundtrip`/`roundtrip_len_ok` as scoped. No vacuous
theorem, no second IR, no toy model, no desired-correctness assumption,
and no safety weakening is needed or proposed: every gap fails closed
(refusal), never open (mis-execution). The decode boundary is sound
within its stated canonical claim; its incompleteness (arbitrary-input
length/soundness lemmas, decoded-image coverage, provenance by
construction) is real, bounded, and already owned.
