# MUSE-REPORT-468: Independent exact-candidate review of 420 (ByteSwap) — re-review of NEW head

## Scope verified (NEW snapshot)
- Clone `/home/simon/Dokumente/gabbro-muse/a468`, branch `muse/468`: match.
- NEW snapshot `.tmp/review/SNAPSHOT.json`: author 420, head `45ca792311bca0301942b51eeaac0e042e887f04`, base `0b3132b7bb8bf108b3fd1613c70bc0955051f130`, files `MUSE-REPORT-420.md`, `grammatik/Grammatik.lean` (one additive import), `grammatik/Grammatik/X86/ByteSwap.lean`. Clean flag true. This supersedes the stale head `16641be95956cea5e385ebd6b26952638781ceaf` from my prior review; this report is a fresh substantive review of the NEW hash, not an approval of the stale one.
- Reviewed: `author-420/OWNER-TASK.md` (unchanged brief), `MUSE-REPORT-420.md` (112 lines, +21 vs before), `PATCH.diff` (703 lines, +21 vs before), `grammatik/Grammatik/X86/ByteSwap.lean` (570 lines), `BUILD-EVIDENCE.json` (69 entries, with the new report-only commit trail).
- Change analysis: per BUILD-EVIDENCE trail, NEW head `45ca7923` is a report-only commit on top of `16641be9` (`git add MUSE-REPORT-420.md`, 21 insertions). Verified mechanically: PATCH `+` lines for `ByteSwap.lean` (570/570) are byte-identical to the supplied file, and the `Grammatik.lean` hunk is still the single additive `import Grammatik.X86.ByteSwap`. The only delta is the new report section "Integration gate failure — analysis". No Lean line changed.

## Independent reproduction (own clone, queued wrapper only, re-run on NEW file)
- Staged only the NEW supplied `ByteSwap.lean` to `grammatik/Grammatik/X86/ByteSwap.lean`, ran `./lean-probe grammatik/Grammatik/X86/ByteSwap.lean`, then deleted it. No other clone read, no network.
- Result reproduced on the NEW file: `== 0 error(s) in the COMPLETE output; exit 0`.
- Axiom dump reproduced exactly: `bswap64_invol`, `bswap32_invol_bounded`, `wortByte_bswap64`, `bswap64_store_bytes`, `probe_bswap64_speicher`, `probe_bswap64_alias` on `[propext, Classical.choice, Quot.sound]` (the `gabbro_ziel` set); `wortByte_bswap32_lo/hi`, `read64_nach_bswap64`, `read32_nach_bswap32`, `bswap64_read_rahmen` on `[propext, Quot.sound]`; flag theorems on no axioms. Matches report.
- Forbidden-pattern grep on the NEW file body (excluding `#print axioms` lines): no `sorry`/`admit`/`native_decide`/`unsafe`, no bare `axiom` declaration, no `intro _`/`have _ :=`, no `forall rho`/`forall v` (44 theorems, 8 defs). `Befehl`/`schritt` occur only in header/CUTS comments; no new IR, executor, codec, or semantics.
- Full `./lean-bau` not re-run here (heavy umbrella link). The NEW report section documents the integration-gate evidence consistently with the BUILD-EVIDENCE tail in this snapshot: merge build reached `[397/398]`, printed the lane's `#print axioms` lines as `info` (no module error), then failed ONLY at the final umbrella target with `failed to create thread`, exit 134 — the same environmental signature as the author's earlier stash-control (skeleton state crashes identically). The new section claims no green build, weakens nothing, and asks the coordinator to free resources / re-run; that is honest and matches the evidence. Merge gate must still re-run `./lean-bau` + `gabbro_ziel` axiom check when the machine recovers.

## Material semantic checks (against accepted models in this checkout, re-confirmed)
- Dependencies real: `Bits` provides `bswap32n/bswap64n`, `_lt`, `_invol`, `split4/split8`, `byteOf_nest(_nest8)`, `byteOf`; `X86/Speicher` provides `wortByte` (= `(v.toNat / 256^i) % 256`), `write64/read64`, `write32/read32`, `writeBytesN_hit`, `read64_nach_write64`, `read32_nach_write32`, `write64_rahmen`, `read64_rahmen`, `disjunkt_von_intervallen`, `zeugenSpeicher` (all-zero, fully permissive); `X86/Typen` provides `Wort := BitVec 64`, `Breite` (`b8/b16/b32/b64`), `Flags`. No invented behavior; `Bits` imports only `Typen`, so no cycle.
- Value correctness: `bswap64` reverses 8 bytes; `decide` probe `0x0102030405060708 -> 0x0807060504030201` green. `bswap32` reverses low 4 bytes with zero extension; probe `-> 0x08070605` green. Negative probe `bswap32 0xFFFFFFFF00000000 = 0` green, and `bswap32_invol_bounded` correctly carries `< 2^32` (unbounded involution would be false since upper bytes clear) — load-bearing bound, not vacuity.
- Premises all used: `hx/hi` via splits + tail absurd; `hv` via `hx`; `hlo/hi` via `j` decomposition + tail; `hwr/hk/hrd/haussen/hdis` all threaded through actual `write64/read64` lemmas. No discarded premise, no conclusion-restates-premise, no `Prop`-typed premise.
- Memory witnesses non-degenerate: nonzero word, real `write64`/`write32` on `zeugenSpeicher`, read-back via actual `read64`/`read32`, plus `m.bytes a != m'.bytes a` (base byte `0x00` vs swapped `0x01`) proved jointly in `probe_bswap64_speicher`; alias witness keeps disjoint `read64 4096` while changing own byte via `probe_disjunkt` (`Disjunkt 0 4096`, decided no-wrap). No program-syntax quantification, so rule-13 `_zeuge` correctly not required.
- Flag/width interface honest: `bswap64f/bswap32f` are pure pair threading with `rfl` proofs, CUT as non-machine-step; `bswapBreite` maps exactly `.b32/.b64`, refuses `.b8/.b16` by `none` with `rfl` proofs — no invented 16-bit shape.
- Trust boundaries preserved: no `Befehl`/codec/`schritt` change, no source correspondence, no TSO/multi-byte atomicity, no timing/cost/hardware claim — all explicitly CUT. No checker/Rust/emitter touched. No safety weakening, no duplicated IR, no forged benchmark (blocked `lean-bau` reported as blocked, not green).

## Previous findings — re-inspected against NEW candidate
- Every prior finding was re-checked against the NEW file (fresh probe above, not assumed): dependencies, value correctness, load-bearing bound, premise use, witnesses, flag/width honesty, trust boundaries — all hold unchanged since the module is byte-identical.
- New report section reviewed in full: gate-failure analysis only, no new definitions/theorems, no changed proofs, no claim inflation. The author's sentence "Module commit `16641be9` keeps its accepted review" is their assertion; my verdict below is issued independently for the NEW head on the basis of this fresh review.

## Defects / repair direction
- None blocking. Minor note for merger (not a repair): re-run `./lean-bau` + `gabbro_ziel` `#print axioms` check at merge time; the one-line umbrella import is the only un-rebuilt artifact here.

## Bounded claim accepted
- Exactly the delivered bounded claim: pure 32/64-bit byte-swap value helpers with involution (bounded for 32), byte-order memory correspondence over actual stores/loads, width-extension effects, flag threading at the intended interface, 16/8-bit refusal, joint concrete witnesses. Not full compiler closure, native expansion, source lowering, or final-byte validation.

CANDIDATE: 420 45ca792311bca0301942b51eeaac0e042e887f04
VERDICT: ACCEPT
