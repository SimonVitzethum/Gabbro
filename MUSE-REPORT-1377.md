# MUSE-REPORT-1377: Memory operands, MMX and REX.W forms of the three-byte maps

## What was done

NEW FILE `grammatik/Grammatik/X86/Befehle/Sse/SseThreeByteMem.lean`
(namespace `Gabbro.Grammatik.X86`, 2529 lines) plus one import line in
`grammatik/Grammatik.lean` plus one registry line in
`instrumente/lean-layout-map.json` (see §Placement below). It connects
twenty new SSSE3 forms to the coherent machine and the capstone chain:
five rows (PSHUFB `0F 38 00`, PABSB/W/D `0F 38 1C/1D/1E`, PALIGNR
`0F 3A 0F + imm8`) times four classes — XMM with memory source (REX.W
admitted, ignored by silicon), XMM register-direct with REX.W = 1,
MMX no-prefix register-direct, MMX no-prefix with m64 source.

- §1 ops/encoder: `SseMemOp` (20 ctors), `sseMemEscape/sseMemThird/
  sseMemNP/sseMemW`, `encodeMemTail` (mirrors the accepted
  `encodeAdr` arm-for-arm with an XMM/MMX reg field; same pilot
  refusals), `encodeSseMem`, nine `decide` encode pins covering
  base, disp8, SIB, RIP, high-register and MMX shapes.
- §2 decoder: `regOpXmm/regOpMmx/memOpXmm/memOpMmx`,
  `parseSseMemRM` (mirrors the accepted `parseAdrTail` mod arms,
  reusing `sibReg`/`codeReg`/`parseLe32`/`ripForm`/`u8Nach32`/
  `codeSkala`), `decodeSseMemTail/Nach`, `decodeSseMem`
  (`SseMemDec` carries the canonical encode length).
- §3 codec proofs: ten general register round trips
  (`roundtrip_pshufbRW/pabsBRW/pabsWRW/pabsDRW/palignrRW/
  pshufbMM/pabsBMM/pabsWMM/pabsDMM/palignrMM`, `cases`-`rfl` over an
  existential witness), eleven per-shape memory `decide` pins
  (`pin_pshufbRM/pabsBRM/pabsWRM/pabsDRM/palignrRM/pshufbRM_hoch/
  pshufbMN/pabsBMN/pabsWMN/pabsDMN/palignrMN`), nine planted
  decoder refusals (`sseMem_nichts_w0reg/kurz/escape/pilot/
  ohne_imm/ohne_rex/mmx_ohne_rex/mmx_erweitert/movbe`).
  Memory rows pin per canonical constructor only: a general
  inversion over open `AdrForm` would need a general
  `parse o encode = id` the accepted `AddressEncoding` never
  proved (its encoder is lossy on non-canonical disp bytes).
- §4 gates/semantics: `sseMemBrauchtAusrichtung`, `sseMemGp`
  (XMM 128-bit sources fault exactly on 16-byte misalignment;
  MMX m64 never faults), `sseMemLade` (two ordered `concLoad`
  `.b64` chunks through the shared TSO view, joined low-first),
  `mmPshufb/mmPabs/mmPalignr` (64-bit lane semantics from the
  accepted `laneNat`/`vecMk`/`pabsLane` vocabulary; XMM value
  semantics reuse `vecPabs`/`vecPshufb`/`vecPalignr` unchanged),
  per-lane equations plus high-zero lemmas, three `decide`
  silicon spot-checks, `sseMemDstX`.
- §5 adapter: `sseMemNachKern/sseMemNach`,
  `adapterSseMem : HwAdapter SseMemDec` (XMM memory + REX.W arms;
  all ten MMX arms are `none`), `setKernVonFp_wf`,
  `adapterSseMem_form/formNach/wf/mem`,
  length/profile/`mmx` refusals, ten per-ctor agreement equations
  (`okSseMem_*`: successor XMM value stated exactly as the
  accepted lane function of pre-state and forwarded load),
  five #GP + five load refusals, `stepSseMem_rip/flags/gpr/
  fremd` frames.
- §6 chain: `KapSseMem`, `kapDecodeSseMem` (old `kapDecodeSse`
  first, new decoder only where it refuses), agreement
  (`kapDecodeSseMem_alt/neu/nichts`), one alt pin, three
  old-chain refusal pins, nine new-arm `decide` pins,
  MOVBE/BLENDVPS joined refusals.
- §7 witness `sseMemWit_zeuge` (16 conjuncts): core-0 memory
  shuffle changes XMM (lane 1: 1 to 0), core-1 memory absolute
  value changes XMM (7 to 0), REX.W shuffle beside the run,
  misaligned and bad-length refusals, and the accepted
  lane-1369 TSO run reused unchanged (owner-only forwarding of
  99, memory-changing drain 0 to 99). Non-degenerate: XMM bytes
  change on both cores and shared memory changes.
- CUTS block and `#print axioms` for every main theorem (see
  §Axioms).

Last `./lean-bau` result line: `Build completed successfully
(712 jobs).` `./lean-probe` on the new file: 0 errors.
`python3 instrumente/lean-layout.py --check`: all 856 Lean files
placed. No `sorry`/`admit`/`axiom`/`native_decide`/`sorryAx`/
`unsafe` (only English prose hits like "admitted", same as lane
1369's accepted file).

## Axioms (`#print axioms` output)

- No axioms: `vecPabs vecPshufb vecPalignr mmPshufb mmPabs
  mmPalignr` (pure defs).
- `propext`: `encodeSseMem decodeSseMem roundtrip_pshufbRW
  roundtrip_pabsBMM sseMemLade sseMemWitStart_wf`.
- `propext + Quot.sound`: `stepSseMem_rip adapterSseMem
  adapterSseMem_wf adapterSseMem_formNach kapDecodeSseMem
  sseMemWit_zeuge` (same footprint class as lane 1369's
  `kapDecodeSse`/`sseWit_zeuge`).

## Open / not claimed (see CUTS in the file)

- No MMX machine step (`adapterSseMem_verweigert_mmx` proves the
  refusal): `HwKern` carries no MMX file and existing files may
  not be edited here. Maintainer hook: add
  `mm : MmxReg -> BitVec 64` to `HwKern`/`FpZustand` and lift the
  pure `mm*` functions through it.
- No general memory round trip over open `AdrForm`; no
  pilot-owned shapes (base-only disp32, SIB-36 disp32 refused
  both directions); MMX REX extension bits refused
  (under-admission); no VEX/EVEX/LOCK/source/loader/budget link;
  no per-access target-to-W/GX simulation.
- No hardware correspondence beyond self-consistency; silicon
  assumptions named in CUTS (opcode rows, REX.W ignored,
  16-byte #GP, m64 no-fault, 3-bit MMX indices, INT_MIN wrap,
  align counts, whole-XMM writes, no flag/GPR effect).
- Maintainer wiring: add the `decodeSseMem` arm behind every
  earlier arm of `HwKapsteinDecoder.kapDecode`.
- GPR 8/16-bit merge and 32-bit zero-extension from the generic
  task shape do not apply: XMM destinations are whole-register
  writes per SDM; there are no byte-register operands.

## Notes for the coordinator (please read before merging)

1. LANE.md line 26 is truncated mid-sentence at 2000 chars
   ("...must be 16-byte alig..."); the tail was unreadable with
   the allowed tools. Reconstructed scope from SDM + report
   1369: 16-byte alignment #GP for XMM memory, no alignment
   fault for m64, REX.W ignored with identical semantics,
   canonical REX always required. If the truncated tail asked
   for more (e.g. VEX, other third bytes), that part is NOT
   done and stays refused here.
2. Placement: the lane names
   `grammatik/Grammatik/X86/SseThreeByteMem.lean`, but hard
   rule 18 plus `lean-layout-rules.py` (`^Sse\w+$` ->
   `Befehle/Sse`) require `Befehle/Sse/`, and `--check` must
   pass before commit. I ran the sanctioned
   `lean-layout.py --apply`: the file now lives at
   `grammatik/Grammatik/X86/Befehle/Sse/SseThreeByteMem.lean`,
   the `Grammatik.lean` import reads
   `Grammatik.X86.Befehle.Sse.SseThreeByteMem`, and the tool
   added exactly one registry line to
   `instrumente/lean-layout-map.json` (kept for consistency;
   machine-maintained, no semantic content). No other file was
   touched by the move. Consequence: my edit allowlist still
   names the OLD path, so I can no longer edit the file; its
   header comment also still names the old path. Both are
   cosmetic; apropos the merge: the content is final and green.
3. The decoder initially extended the r/m register with the
   REX.R bit (`codeXmm (r*8+rm)`); the general register
   round trips failed exactly the high-src cases and exposed
   it. Fixed to REX.B (`codeXmm (b*8+rm)`); all round trips
   pass. The mem-tail parser already used B correctly.
4. `simp` unused-argument linter warnings remain in the file
   (hop/hlen/hfp/adapterSseMem in a few branches, three
   `sseMemNach_*` rewrite names in frames). They are harmless:
   the suggested `simp only` replacements were tried and fail
   (`simp only` does not perform the needed iota steps there),
   so the fuller simp calls stay. Do not "clean" them without
   re-probing.
5. Lean slot contention (up to ~15 lanes on one slot) repeatedly
   pushed probes past 60-minute timeouts; one turn's
   interrupted `lean-bau` left a stale `.lake` that a fresh
   `./lean-bau` rebuilt. Final state verified green end to end.
