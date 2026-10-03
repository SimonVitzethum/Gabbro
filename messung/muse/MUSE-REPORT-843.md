# MUSE-REPORT-843: Composition closing — feature-gate closing

Lane 843, clone `/home/simon/Dokumente/gabbro-muse/a843`, branch `muse/843`
(matched). Owned files only: `grammatik/Grammatik/X86/ComposeFeatureGate.lean`
(new), `grammatik/Grammatik.lean` (one import line appended), this report.

## What was done

Closed every feature-gated form to its CPUID/XCR0/enabled-state gate,
re-checked per image, in one new leaf module
`grammatik/Grammatik/X86/ComposeFeatureGate.lean` (~510 lines). Only
already-accepted definitions are reused by name; nothing is re-proved and no
interpreter/executor is duplicated.

Producer/consumer interface closed: the observed CPUID/XCR0 answers of a
reached fetched CPUID-then-XGETBV chain (`cpu_kette_speichert_gatter`) +
finite profile admission (`merkmalZugelassen`) + checked enabled-state
readiness (`vektorHwZugelassen`) jointly admit one checked closing step per
feature and image; an absent observed bit refuses the encoding.

New definitions (all in `Gabbro.Grammatik.X86`):

- `beobachtungsTor` — per-feature observed-bit gate over the accepted
  `edxSSE2`/`xcrXMM` tests (scalar integer rows need no bit).
- `featureGateGeschlossen` — per-feature closing: finite profile AND
  observed bits (AND checked `vektorHwZugelassen` for the packed tier).
- `avx2ReiheGeschlossen` — unimplemented 256-bit row (`stufenZugelassenHw`
  `.avx256` AND `avx2Bereit`).
- `merkmalKodierungOk` — per-tier encoding check over the accepted
  `decode`/`fpDecode`/`decodeVector`.
- `kodierungTor` — encoding admission: feature closing AND decodable bytes.
- `bildFeatureTor` — per-image closing: `valX86` AND the feature gate,
  re-decided per image.
- `zeugeBlatt7` — zero second observed leaf for the AVX2 row.

New theorems:

- `avx2_reihe_verweigert_immer` (256-bit row always refuses).
- Gate refusals: `tor_sse_verweigert_ohne_bit`,
  `tor_paket_verweigert_ohne_bit`, `tor_paket_verweigert_ohne_xmm`,
  `geschlossen_sse_verweigert_ohne_bit`,
  `geschlossen_paket_verweigert_ohne_bit`,
  `geschlossen_paket_verweigert_ohne_merkmal`,
  `geschlossen_sse_verweigert_ohne_merkmal`.
- Encoding refusals/accepts: `kodierung_paket_verweigert_ohne_bit`,
  `kodierung_paket_verweigert_ohne_bytes`,
  `kodierung_sse_verweigert_ohne_bit`,
  `kodierung_sse_verweigert_ohne_bytes`,
  `kodierung_paket_akzeptiert` (PXOR bytes, `decide`),
  `kodierung_sse_akzeptiert` (ADDSD bytes, `decide`).
- Per-image: `bildFeatureTor_braucht_bild`, `bildFeatureTor_braucht_gate`,
  `bild_tor_verweigert_ohne_bild` (mutated image refuses under full gates),
  `bild_tor_verweigert_ohne_bit` (good image refuses on absent bit).
- `ComposeFeatureGate_verbindung` — main composition: a reached
  observation chain (all 22 chain premises reused via the accepted chain
  theorem) yields readback, RIP chaining, ECX faithfulness, the finite
  profile admission (via `vektorHw_braucht_merkmal`), the packed-tier
  closing, the per-image closing, and refusal of the 256-bit row from the
  same answers. Every premise is used.
- `compose_kette_speicher_aendert` — chain store changes a memory byte
  (`writeBytesN_hit` pattern).
- `ComposeFeatureGate_verbindung_zeuge` — joint companion: all premises
  instantiated on the concrete reached chain (`zeugeHw`/`zeigeScope`/
  `zeigeCtrl`/`zeigeStart0`/`zeigeS1`/`zeigeS1p`/`zeigeS2`/`zeigeOut1`,
  `basisHw`/`vecZeugeBereit`/`basisCpu`/`basisXcr0`/`basisKontrolle`,
  `.p48`/`valZeuge`) plus both memory-changing runs (chain store byte
  inequality + readback, and the admitted gated vector step with MOVSD
  store reused from `vectorHw_zeuge`). Non-degenerate: two fetched steps
  run, two stores change memory.

During the work the `lean-probe` linter caught one genuine redundancy (a
profile premise subsumed by the enabled-state admission); it was removed and
the profile admission is exposed as a conclusion instead.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (509 jobs)`. `./lean-probe` on the new file:
`== 0 error(s)`, no warnings. `#print axioms`: refusal/encoding/image
lemmas depend on `[propext]`; the connection, witness and memory-change
lemmas on `[propext, Quot.sound]` — a subset of the `gabbro_ziel`
(`propext`, `Classical.choice`, `Quot.sound`) set, no new axioms. No
`sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

## What remains open (CUTS in the file)

- Silicon correspondence of bit positions stays with the producer CUTS; no
  new hardware claim here. The between-fetch selector gap is inherited
  unchanged from the accepted chain.
- Scalar integer rows close to the profile only (no CPUID bit exists).
- Extended-form decode coverage per image stays open (`valX86` covers pilot
  forms; vector/scalar bytes go through the fetch-discipline adapters owned
  by validator consumers). No TSO bridge, no source/checker/emitter
  correspondence, no budget/timing, OS configuration stays user logic.
- The 256-bit AVX row is a permanent refusal here; implementation open.

## Task remarks

Nothing in the task looked wrong. One scoping note: "close EVERY
feature-gated form" is met for the four finite features plus the AVX2 row;
scalar-integer rows have no gate bit by construction (their `bereit` is
constantly true), which the file states explicitly rather than inventing a
refusal.
