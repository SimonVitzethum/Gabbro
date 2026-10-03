# MUSE-REPORT-993: Exact review of author 843 (Composition closing: feature-gate closing)

Lane 993, clone `/home/simon/Dokumente/gabbro-muse/a993`, branch `muse/993`.
Owns only this report. No source file touched, no live controls used.

## CANDIDATE and VERDICT

CANDIDATE: 843 `4bb20cd3e74967145e6ca2204c71e78f397083b4`
(pinned base `e7c75908456285d1e37c18dc32d4f9c0e10d1fa4`; files:
`MUSE-REPORT-843.md`, `grammatik/Grammatik.lean` (one import line),
`grammatik/Grammatik/X86/ComposeFeatureGate.lean` (new, 508 lines)).

VERDICT: ACCEPT — bounded to the composition as stated, with the CUTS below.
No repairs required. No guarantee weakened, no desired simulation assumed,
no fake closure found.

## What was reviewed

The exact pinned PATCH (632 lines, read in full from the review snapshot),
the owner task, the author report, and the build evidence. Every reused
producer name was checked against the accepted modules in this clone
(`CpuFeatureHardwareForms`, `FeatureProfile`, `VectorHardwareProfile`,
`VectorCodec`, `ScalarFloatCodec`, `ValidatorSkeleton`, `Codec`, `Speicher`,
`Bild`); every architectural claim below was verified, not taken on trust.

## Architecture findings (each checked)

- Bit positions are correct silicon: `edxSSE2` = EDX bit 26, `xcrXMM` =
  XCR0 bit 1, `ecxXSAVE` = ECX bit 26 (`CpuFeatureHardwareForms.lean:426-444`).
  The witness `zeugeOut1` = EAX 7 / EBX 0 / ECX `0x1C000000` / EDX
  `0x04000000` carries exactly SSE2 + XSAVE + OSXSAVE + AVX; `xcrLo 0x6`
  carries XMM. Reproduced by `decide` (see evidence).
- No dropped enable gates: scalar-double closes through `merkmalZugelassen`,
  which is silicon AND MXCSR-validity AND OS vector state
  (`FeatureProfile.lean:59-68`); the packed tier closes through
  `vektorHwZugelassen`, which is profile AND silicon SSE2 AND XCR0 SSE AND
  control freedom AND OS XMM (`VectorHardwareProfile.lean:70-72`). The extra
  observed-bit conjunct (`beobachtungsTor`) can only refuse more, never admit
  unsoundly; static-vs-observed correspondence is correctly left with the
  producer CUTS, not derived here.
- Scalar-integer rows close with no observed bit. Correct scoping, stated
  explicitly: base x86-64 integer forms have no CPUID gate bit. Not a weakening.
- The 256-bit AVX row is a permanent refusal via the accepted
  `stufe_avx256_verweigert` (`... = false := rfl`). A bounded refusal with
  implementation open is honest closure, not a fake accept.
- The main theorem reuses `cpu_kette_speichert_gatter` with all 22 chain
  premises in exact order and type — verified against
  `CpuFeatureHardwareForms.lean:973-997`. Nothing re-proved, no second
  interpreter or executor: the new file only defines Boolean gates over
  accepted decoders/admissions and proves refusals/composition about them.
- Every premise of `ComposeFeatureGate_verbindung` is used: the 22 chain
  premises via the accepted chain theorem; `hsse`/`hxmm`/`hgate` in both
  gate closes; `hval` in the per-image close; `leaf7` in the AVX2 refusal.
  No `intro _` / `have _ :=` discard; no banned tactic anywhere in the new
  file (grep over the snapshot confirms: only prose "admit(s)").
- Witness is non-degenerate and joint: all premises instantiated on the
  concrete reached CPUID-then-XGETBV chain, plus two memory-changing runs
  (chain store byte inequality via `writeBytesN_hit` + readback, and the
  admitted gated vector step with MOVSD store reused from the accepted
  `vectorHw_zeuge`). Two fetched steps run; two stores change memory.
- Negative mutations on both sides: absent-bit refusals (observation gate,
  both closings, both encodings, image-with-good-gates), undecodable-bytes
  refusals per tier, one-byte-mutated-image refusal under full gates; plus
  two planted accepts (canonical PXOR under vector gates, canonical ADDSD
  under SSE gates). Refusal comes from the right side in each case.
- CUTS are precise: silicon correspondence with producers, inherited
  between-fetch selector gap, pilot-only `valX86` coverage (vector/scalar
  bytes via validator-consumer adapters, no vector-bytes image claimed to
  pass `valX86`), no TSO bridge (names lane 660), no source/checker/emitter
  correspondence, no budget/timing, OS configuration stays user logic.
- Axioms as reported: refusal/encoding/image lemmas `[propext]`; connection,
  witness, memory-change lemmas `[propext, Quot.sound]` — a subset of the
  `gabbro_ziel` set, no new axioms.
- Scope compliance with the 2026-10-03 priority: 3 files only (report, one
  import line, one new leaf module). No diagnostic/gift/example/CLI numbers,
  no MARKE changes, no source/checker/Spec/goal/emitter edits, no
  friend-reserved optimiser files.

## Independent reproduction (this clone, queued wrapper)

Wrote scratch probe `.tmp/probe993_gate.lean` (private dir, not committed)
re-deciding the ten producer-side facts the candidate's closes depend on
(witness observed bits, baseline profile and enabled-state admissions,
`valX86` accept on `valZeuge`, generic AVX2-row refusal shape, mutated-image
refusal, zeroed-leaf gate refusal):

`./lean-probe .tmp/probe993_gate.lean` → `== 0 error(s) in the COMPLETE
output; exit 0`.

The candidate's own build evidence (in-snapshot) is consistent with this:
`./lean-bau` exit 0 (509 jobs), `./lean-probe` on the new file 0 errors,
one caught-and-fixed redundancy plus one fixed rewrite pair visible in the
iteration history. The candidate file itself was not re-applied here (this
lane owns only the report); all its producer interfaces exist with matching
signatures and identical decided behaviour at this clone's HEAD, so merge
risk is confined to the one import line plus the new leaf file, which the
merge gate re-checks.

## What remains open (inherited, correctly not claimed)

Per-access TSO bridge, source-to-final-bytes correspondence, extended-form
decode coverage per image, 256-bit AVX implementation, budget/timing
transfer. All are explicit CUTS naming the owning lanes — none is assumed.

## Task remarks

Nothing in the owner task looked wrong. The "close EVERY feature-gated
form" scope is met for the four finite features plus the AVX2 row; the
scalar-integer no-bit scoping is stated rather than papered over.
