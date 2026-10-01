# MUSE-REPORT-468: Independent exact-candidate review of 420 (ByteSwap)

## Scope verified
- Clone `/home/simon/Dokumente/gabbro-muse/a468`, branch `muse/468`: match.
- Snapshot `.tmp/review/SNAPSHOT.json`: author 420, head `16641be95956cea5e385ebd6b26952638781ceaf`, base `0b3132b7bb8bf108b3fd1613c70bc0955051f130`, files `MUSE-REPORT-420.md`, `grammatik/Grammatik.lean` (one additive import), `grammatik/Grammatik/X86/ByteSwap.lean`. Clean flag true.
- Reviewed: `author-420/OWNER-TASK.md`, `MUSE-REPORT-420.md`, `PATCH.diff` (682 lines), `grammatik/Grammatik/X86/ByteSwap.lean` (570 lines), `BUILD-EVIDENCE.json` (full probe history).

## Independent reproduction (own clone, queued wrapper only)
- Staged only the supplied `ByteSwap.lean` to `grammatik/Grammatik/X86/ByteSwap.lean`, ran `./lean-probe grammatik/Grammatik/X86/ByteSwap.lean`, then deleted it. No other clone read, no network.
- Result reproduced: `== 0 error(s) in the COMPLETE output; exit 0`.
- Axiom dump reproduced exactly: `bswap64_invol`, `bswap32_invol_bounded`, `wortByte_bswap64`, `bswap64_store_bytes`, `probe_bswap64_speicher`, `probe_bswap64_alias` on `[propext, Classical.choice, Quot.sound]` (the `gabbro_ziel` set); `wortByte_bswap32_lo/hi`, `read64_nach_bswap64`, `read32_nach_bswap32`, `bswap64_read_rahmen` on `[propext, Quot.sound]`; flag theorems on no axioms. Matches report section 3.
- Grep on staged file: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `intro _`/`have _ :=`, no `forall rho`/`forall v`. `Befehl`/`schritt` occur only in header/CUTS comments; no new IR, executor, codec, or semantics.
- Full `./lean-bau` not re-run here (heavy umbrella link; author documents environmental exit 134 OOM after 392/393 with stash-control showing identical crash without content). File-level import resolution (`Speicher`, `Bits`) is green here, so the bounded claim does not depend on the blocked umbrella link. Merge gate must still re-run `./lean-bau` + `gabbro_ziel` axiom check when the machine recovers, as the author already states.

## Material semantic checks (against accepted models in this checkout)
- Dependencies real: `Bits` provides `bswap32n/bswap64n`, `_lt`, `_invol`, `split4/split8`, `byteOf_nest(_nest8)`, `byteOf`; `X86/Speicher` provides `wortByte` (= `(v.toNat / 256^i) % 256`), `write64/read64`, `write32/read32`, `writeBytesN_hit`, `read64_nach_write64`, `read32_nach_write32`, `write64_rahmen`, `read64_rahmen`, `disjunkt_von_intervallen`, `zeugenSpeicher` (all-zero, fully permissive); `X86/Typen` provides `Wort := BitVec 64`, `Breite` (`b8/b16/b32/b64`), `Flags`. No invented behavior; `Bits` imports only `Typen`, so no cycle.
- Value correctness: `bswap64` reverses 8 bytes; `decide` probe `0x0102030405060708 -> 0x0807060504030201` green. `bswap32` reverses low 4 bytes with zero extension; probe `-> 0x08070605` green. Negative probe `bswap32 0xFFFFFFFF00000000 = 0` green, and `bswap32_invol_bounded` correctly carries `< 2^32` (unbounded involution would be false since upper bytes clear) — load-bearing bound, not vacuity.
- Premises all used: `hx/hi` via splits + tail absurd; `hv` via `hx`; `hlo/hi` via `j` decomposition + tail; `hwr/hk/hrd/haussen/hdis` all threaded through actual `write64/read64` lemmas. No discarded premise, no conclusion-restates-premise, no `Prop`-typed premise.
- Memory witnesses non-degenerate: nonzero word, real `write64`/`write32` on `zeugenSpeicher`, read-back via actual `read64`/`read32`, plus `m.bytes a != m'.bytes a` (base byte `0x00` vs swapped `0x01`) proved jointly in `probe_bswap64_speicher`; alias witness keeps disjoint `read64 4096` while changing own byte via `probe_disjunkt` (`Disjunkt 0 4096`, decided no-wrap). No program-syntax quantification, so rule-13 `_zeuge` correctly not required.
- Flag/width interface honest: `bswap64f/bswap32f` are pure pair threading with `rfl` proofs, CUT as non-machine-step; `bswapBreite` maps exactly `.b32/.b64`, refuses `.b8/.b16` by `none` with `rfl` proofs — no invented 16-bit shape.
- Trust boundaries preserved: no `Befehl`/codec/`schritt` change, no source correspondence, no TSO/multi-byte atomicity, no timing/cost/hardware claim — all explicitly CUT. No checker/Rust/emitter touched. No safety weakening, no duplicated IR, no forged benchmark (blocked `lean-bau` reported as blocked, not green).

## Defects / repair direction
- None blocking. Minor note for merger (not a repair): re-run `./lean-bau` + `gabbro_ziel` `#print axioms` check at merge time; the one-line umbrella import is the only un-rebuilt artifact here.

## Bounded claim accepted
- Exactly the delivered bounded claim: pure 32/64-bit byte-swap value helpers with involution (bounded for 32), byte-order memory correspondence over actual stores/loads, width-extension effects, flag threading at the intended interface, 16/8-bit refusal, joint concrete witnesses. Not full compiler closure, native expansion, source lowering, or final-byte validation.

CANDIDATE: 420 16641be95956cea5e385ebd6b26952638781ceaf
VERDICT: ACCEPT
