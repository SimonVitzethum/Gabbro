# MUSE-REPORT-581: Independent exact-review of 563 (MulDiv byte codec)

## Scope and method

Reviewed the pinned 563 snapshot only from `.tmp/review/SNAPSHOT.json`
and `.tmp/review/author-563/` (task, PATCH.diff, candidate file copy,
build evidence). Verified branch `muse/581` in `/home/simon/Dokumente/gabbro-muse/a581`
before starting. No Lean or Rust file touched; this report is the only
owned path. Re-ran the candidate file through the queued `./lean-probe`
wrapper independently (0 errors) and ran the full queued `./lean-bau` on
this clone to confirm a green base.

## Candidate under review

CANDIDATE: 563 898c5b14493c1ba0eaae6944feba929f4dd0b0d8

Files in scope: `grammatik/Grammatik/X86/MulDivCodec.lean` (new, 846 lines),
additive umbrella import in `grammatik/Grammatik.lean`, plus the author report.
No checker, Spec, goal, emitter, or friend optimiser paths touched.

## What the candidate does

Canonical REX.W register-direct codec for MUL/IMUL/DIV/IDIV
(Group-3 `F7 /4 /6 /7`, two-operand `0F AF /r`), decoded through
independent REX/opcode/ModRM layers (`decodeMulDiv` via `decodeNachRex`,
`decodeNachRexR`, `decodeImulRex`, `decodeImulModrm`, `decodeF7Modrm`),
with `mulDivEncode` as the pinned producer. Execution reuses the accepted
`mulDivSchritt` and its `md_*` step equations, `zugelassen`,
`verweigert_heisst_halt`, and shared `rexByte`/`modrmReg`/`codeReg`/
`regSet`/`ripNach`/`laengeOk`/`read64`/`write64` shapes on the same `Zustand`.
No duplicated evaluator found.

## Checks performed

- Real names resolved: `MulDivBefehl`, `MulDivDecodiert`, `mulDivSchritt`,
  `md_mul_erfolg`, `md_imul_erfolg`, `md_div_erfolg`, `md_div_halt`,
  `md_idiv_erfolg`, `md_idiv_halt`, `zugelassen`, `verweigert_heisst_halt`,
  `laengeOk`, `rexByte`, `modrmReg`, `codeReg`, `natByte`, `byteNat`,
  `regSet`, `ripNach`, `mdZustandMul`, `mdZustandNull`, `zeugeSpeicher`,
  `zeugeFlags`, `read64_nach_write64`, `writeBytesN_hit`, `addrOff_null`
  all exist in the accepted `Codec`, `Ausfuehrung`, `Speicher`, `MulDiv` modules.
- Decoder independence: `decodeMulDiv` pattern-matches on raw byte values
  (72/73/76/77, 247, 15/175, mod/reg/rm fields), never on `mulDivEncode`
  output. Round trips (`roundtrip_mulRax/divRax/idivRax/imul2/muldiv`) go
  encode-to-decode by `cases` + `rfl` over all registers.
- Arbitrary-input length soundness: `decodeF7Modrm_len`,
  `decodeImulModrm_len`, `decodeImulRex_len`, `decodeNachRex_len`,
  `decodeNachRexR_len`, and the top-level `decodeMulDiv_len_ok`
  (consumed length exact, 1..15) proved by case analysis on every layer,
  stronger than the pilot codec's open point. `decodiert_laenge_ok`
  derives `laengeOk` from any successful decode.
- Decode-to-execute is genuine: each `decode_exec_*` takes a real decoded
  `(bs, d, rest)` with `hdec : decodeMulDiv bs = some (d, rest)` plus the
  `d.befehl = ...` selector, derives `hok` from `hdec` (never assumed),
  then applies the reused `md_*` equation. Implicit RDX:RAX dividend,
  divide refusal/trap split, unsigned/signed value and flag semantics all
  come from the reused layer. The DIV guard-trap agreement reuses
  `verweigert_heisst_halt`; the IDIV twin is `md_idiv_halt` with
  decode-derived length admissibility (minor naming asymmetry, no defect).
- No forged-input closure: main theorems quantify over decoded `d`;
  probes and pins use explicit literals but are tied to decode by the
  `pin_*_dekode` pairs and the generic round trip, so premises are jointly
  satisfiable, not vacuous.
- Truncation direction correct: `probe_idiv_negativ` (-7/2 = -3 r -1) and
  `probe_idiv_neg_teiler` (7/-1 = -7 r 0) confirm truncation toward zero,
  never floor. `probe_idiv_min_halt` (INT_MIN/-1) and `probe_idiv_null_halt`
  trap with guard refusal. Twelve `md_decode_nichts_*` refusals cover empty
  input and truncation at every prefix length plus non-canonical REX/mode/
  digit/opcode shapes, each by `decide`.
- Frame on the same target state: `decode_mul_speicher` (no memory change),
  `decode_div_flags` (flags kept), `decode_mul_rip` (RIP past consumed
  bytes). No memory-form, immediate, or one-operand-IMUL forms admitted;
  all refuse, as documented.
- Joint witness `muldiv_codec_zeuge`: MUL bytes decode, step to 42 via reused
  execution, product goes through permission-checked `write64`/`read64`
  with an observable byte change, DIV-by-zero traps with guard refusal,
  truncated bytes refuse. Nondegenerate (memory-changing store plus planted
  refusals), all premises jointly instantiated.
- Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the
  candidate; no `Prop`-typed premise; no `intro _` / `have _ :=` discard;
  no contract quantified away (no source-syntax premises at all, so no
  rule-13 obligation, witness still provided). CUTS block present and
  honest; `#print axioms` for every main theorem, all within
  `propext, Classical.choice, Quot.sound`, confirmed by the independent
  probe run. Umbrella import purely additive.
- Bounded claim discipline kept: hardware correspondence, memory forms,
  source correspondence, physical-fault/source-stop transfer, fetch
  integration, TSO/GX, and costs all left open in CUTS. The REX.R-over-
  Group-3 refusal is labelled a canonical-subset choice, not a silicon
  claim. No contract-duty weakening, no guessed widths, no atomicity or FP
  claims, no exaggerated closure.

## Findings

No blocking defect. Two non-blocking notes: (a) the IDIV guard-trap lemma
takes the quotient-`none` premise rather than the `zugelassen = false`
premise its DIV twin takes; harmless since the guard mirrors the quotient
option, but a symmetric statement would read cleaner; (b) signed probes run
on explicit decoded-shaped literals rather than threading the `d` from a
`hdec`, with the decode link carried by the pins and the joint witness;
acceptable at this layer, fetch integration (575) should thread decoded `d`
end to end. Neither warrants a repair cycle.

## Accepted bounded claim

Canonical register-direct MUL/IMUL/DIV/IDIV byte images round-trip, every
successful decode of any input consumes exactly its stated 3/4-byte length
in 1..15 with valid step length, and every decoded image steps through the
reused `mulDivSchritt` value/flag/trap semantics on the shared `Zustand`
with the stated frame facts, pins, refusals, truncation probes, and joint
decode/execute/memory/refusal witness. No silicon, source, fault-delivery,
fetch, concurrency, or cost transfer claimed.

## Producer interface for 575 and next integration

Stable producers: `mulDivEncode`, `decodeMulDiv`, `roundtrip_muldiv`,
`roundtrip_muldiv_len_ok`, `decodeMulDiv_len_ok`, `decodiert_laenge_ok`,
`decode_exec_mul/imul/div_ok/div_halt/idiv_ok/idiv_halt`,
`decode_div_verweigert_heisst_halt`, `decode_idiv_verweigert_heisst_halt`.
Measurable next step: 575 consumes exactly these to build the unified
permission-checked fetch plus byte step over the extended path; success is
a fetched-image decode that reuses `decodeMulDiv_len_ok` and selects the
matching `decode_exec_*` without re-proving lengths.

## Build evidence

- Independent `./lean-probe .tmp/review/author-563/grammatik/Grammatik/X86/MulDivCodec.lean`:
  0 errors, exit 0; per-theorem axioms none / propext / propext+Quot.sound /
  full goal set only.
- Full `./lean-bau` on this clone: == exit 0; 0 error lines in the COMPLETE
  output; Build completed successfully (429 jobs).
- Author evidence consistent: 0-error probe plus 428-job green build at the
  pinned head.

## Task remarks

Nothing in the owner or review task was wrong. The review task's
vacuity/forgery/width/closure checklist is fully answerable on this
candidate; the bounded byte-codec-to-execution link is real work, and the
remaining source/IR/final-byte chain is honestly left to 575 and the IR
owners rather than claimed here.

VERDICT: ACCEPT
