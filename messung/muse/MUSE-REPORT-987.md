# Muse Report 987: Independent exact-candidate review of author 837 (fence-order closing)

## CANDIDATE and VERDICT

CANDIDATE: 837 da5a2868b2c2f95a2f3ec21a862bbc929b97f246
VERDICT: ACCEPT

- Pinned base: e7c75908456285d1e37c18dc32d4f9c0e10d1fa4, 3 files per SNAPSHOT.json:
  `MUSE-REPORT-837.md`, `grammatik/Grammatik.lean` (one import line),
  `grammatik/Grammatik/X86/ComposeFenceOrder.lean` (171 lines). Clean tree.
- Acceptance is bounded: TSO/fence composition level only.
- Scope of acceptance: the candidate closes fence placement to the stated
  per-access concurrent postcondition over the ONE canonical `TSOZustand`
  by composing already-accepted legs, with a jointly-inhabited
  non-degenerate memory-changing witness and two proved refusal legs.
  It does NOT close the target-to-W/GX simulation, `valX86_sound`, or any
  silicon/timing claim -- all explicitly left open in CUTS with the owning
  lanes named (567, 570, 573-574, validator owner). No fake closure found.

## What was inspected

- Exact pinned snapshot: `.tmp/review/author-837/grammatik/Grammatik/X86/ComposeFenceOrder.lean`
  (read in full), `OWNER-TASK.md`, `MUSE-REPORT-837.md`, `BUILD-EVIDENCE.json`,
  `PATCH.diff` (head), `SNAPSHOT.json` (full HEAD above).
- Producer legs in my own clone (base = candidate base, verified
  `muse/987` at `e7c75908` before review): `MfenceDrainOwn.lean`
  (mfenceDrain/mfenceSchrittAusBytes, `mfenceDrain_leert/bereit/fremd/ordnung/erreichbar_von`,
  `mfenceAbgeschnitten15_verweigert`, `mfenceNachbarLFENCE_verweigert`),
  `FenceDrain.lean` (drainVoll, fdS2/fdS3/fdX/fdY/fdEins, `fd_voll_schritt`,
  `fd_fremd_wartend`, `fd_speicher_aendert`, `fd_fremd_liest_alt/neu`,
  `fd_schritt1/2`), `SfenceStoreNarrow.lean` (`sfenceOrdnet`,
  `sfence_ordnet_schreibe/last_nicht`), `LfenceLoadNarrow.lean`
  (`lfenceSchritt`, `mfence_verweigert_bei_vollem_puffer`), `LockedOps.lean`
  (`lockSchritt` argument order).
- Official reference: `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
  (Intel SDM 325462-093US): MFENCE = `NP 0F AE F0` (serializes loads+stores),
  LFENCE = `NP 0F AE E8` (serializes loads), SFENCE = `NP 0F AE F8`
  (serializes stores); MFENCE does not serialize the instruction stream;
  SFENCE/SFENCE-before/after-Direct-store ordering notes.

## Findings (all checks passed)

1. Signature fidelity: every reused name exists in the base with a matching
   statement. `mfenceDrain_fremd` takes implicit `{d}` + `(hd : d != c)` --
   the candidate's `(d := 1) (by decide)` call is well-formed.
   `mfence_verweigert_bei_vollem_puffer s c (hne : s.puffer c != [])`
   concludes `lockSchritt .mfence c s = none` -- matches the final conjunct.
   `sfence_ordnet_last_nicht.1` is exactly `sfenceOrdnet .lese .lese = false`.
   `unfold mfenceDrain; exact fd_voll_schritt` is legitimate (`mfenceDrain :=
   drainVoll` definitionally). The witness's `TSOErreichbar` proof term
   mirrors the accepted `fd_lokal_nur` shape.
2. Premise use: all four premises of `ComposeFenceOrder_verbindung` are used
   (`hdrain` 5x, `hreach`, `hpend`, `hvoll` each at least 1x). No `intro _`
   / `have _ :=`. No conclusion-is-premise restatement; no contract
   quantification (no contracts involved); the drain is memory-changing
   (`fd_speicher_aendert`), not a check-only wrapper.
3. Forbidden tactics: none. A content search over the snapshot file finds
   only benign substrings (`admitted` in prose, `#print axioms`); no
   `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
4. Axioms (per pinned build evidence, `./lean-probe` 0 errors, `./lean-bau`
   509 jobs green): `fenceOrdnungGeschlossen` none, `verbindung`
   `[propext, Quot.sound]`, `zeuge` none, `keinEntfernen_ohne_zaun` none,
   `bytes_verweigern` `[propext]` -- all inside the `gabbro_ziel` budget.
5. Architecture: byte refusals are correct against the manual -- `[15]`
   truncation is nothing, and `[15,174,232]` is the LFENCE encoding
   (`NP 0F AE E8`), which must never run the MFENCE drain step (reg field
   5 vs 6). SFENCE store-only ordering and LFENCE no-drain/no-full-barrier
   match the manual's serialized-operation classes at the modeled TSO
   level. No invented determinism: undefined/foreign/device discharge stays
   refused by the reused legs; WC/NT, LOCK RMW beyond accepted rows,
   dispatch-serializing LFENCE and faults are explicit CUTS.
6. Witness non-degeneracy: `verbindung_zeuge` jointly inhabits ALL premises
   on fdS2/fdS3 -- two issued stores on two cores, reached run, drain that
   observably changes canonical memory (`fd_speicher_aendert`) plus the
   reached drained state. Meets the task bar.
7. Refusals answer the task's exact demand ("no fence removed on
   race-freedom alone"): `keinEntfernen_ohne_zaun` shows disjoint buffered
   bytes (`fdX != fdY`, i.e. no race) yet fence removal observably changes
   core 1's load of `fdX` and canonical memory; `bytes_verweigern` plants
   the truncation and neighbor-shape mutations. The gate-vs-drain conjunct
   (`lockSchritt .mfence 0 s2 = none` alongside drain success) makes the
   fence load-bearing on the same admitted pair.
8. Claim boundaries: CUTS lists exactly what is proved and names the missing
   producer legs with owners (567 shared TSO-history projection, 570
   source-world bytes, 573-574 W bridges) without assuming them; no
   source/checker/Spec/goal/emitter change; no diagnostic/gift/example/CLI
   numbers; no MARKE_EMIT changes; no friend-reserved optimiser files;
   only owned files touched.
9. "Conjunction of checks is not execution" (owner task): satisfied, not
   evaded -- the composed step's execution content (drain run, foreign-load
   move, memory change, reached extension) comes from the reused accepted
   legs applied to concrete decide-evaluated states, and the candidate adds
   the joint-holding plus same-state gate refusal. That is the composition
   the task asked for ("never re-prove their internals").

## Minor remarks (not repair-worthy)

- `def fenceOrdnungGeschlossen` is unused: no theorem states it (the main
  theorem inlines a 12-conjunct superset; the def covers 3). Dead but
  harmless; suggest using or dropping it in a follow-up.
- Skipped `e5` in the proof's have-numbering; cosmetic only.
- The fdS2/fdS3 witness uses single-entry buffers -- minimal yet
  non-degenerate per the task's bar (two cores, memory-changing reached run).

## Reproduction status (honest)

- Author's pinned build evidence: `./lean-probe` 0 errors (axiom prints
  match section 4 above), `./lean-bau` 509 jobs green, committed on a clean
  tree. I verified every reused signature, the witness/refusal proof terms,
  the byte encodings against the official SDM text, and the file scope --
  all by direct inspection of the exact snapshot and my base-tree clone.
- I did NOT re-run `./lean-bau`/`./lean-probe`: the sandbox permission
  classifier rejected my `bash` tool calls (including a read-only
  `grep` of the PATCH), so queued wrappers were unavailable from this lane.
  No source was touched here (report-only lane), so there is nothing of
  mine to keep green; the merge gate's fresh build remains the binding
  check. This bounded verification plus the author's evidence is what the
  ACCEPT above rests on -- stated plainly per HARD RULES 4.

## Task assessment

Nothing in the owner task appears wrong. The ZEUGE target is proved with a
jointly-inhabited non-degenerate companion, the "exact theorem or refusal"
demand is met with both, and the composition stops honestly at the
TSO/fence level with the W/GX legs named, not assumed.
