# Muse Report 482: Independent exact-candidate review of 434

## Scope

Reviewed the exact pinned candidate from `.tmp/review/SNAPSHOT.json`:

- author 434, head `9fac0f135cb48cc004935a4d09ba2dc5367ff478`,
  base `0b3132b7bb8bf108b3fd1613c70bc0955051f130`
- files: `MUSE-REPORT-434.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/HardwareAssumptions.lean`
- Task: generic selected-profile hardware-assumption records plus a derived
  conservative target step-cost aggregation fact over actual finite runs with
  explicit bounds; no assumed simulation, LOCK latency, progress, or ignored
  waiting.

Method: read OWNER-TASK, PATCH, the candidate module (353 lines), the
supplied BUILD-EVIDENCE.json in full, and the actual accepted models in my
own clone (`Typen.lean` Befehl, `Ausfuehrung.lean` lauf/zeuge*, `Gleitprofil.lean`
mxcsrGueltig, `LockedOps.lean` lockKosten). Staged only the supplied
candidate files temporarily in my clone (newer HEAD `1c54c6da`), reproduced
via the queued wrappers, then restored to report-only state before committing.

## Findings

1. Reuses accepted models, no duplicated IR/executor. `HardwareProfil`
   pairs the accepted `MXCSR` with a per-instruction bound table over the
   canonical `Befehl`; `laufKosten` folds the same finite `List Decodiert`
   that `lauf` folds. New definitions are only the profile record, the
   admission predicate, the cost fold, the witness table and the witness
   profile. No checker/Spec/Rust/emitter touched; friend files untouched.
2. Witness table is exhaustive and honest. `zeugeKosten` covers all 14 pilot
   `Befehl` constructors with named bounds (1 move/jump, 2 ALU/push/pop,
   3 load/store/call) and refuses `ret` (`none`) with a stated reason
   (stack-memory traffic no constant covers). Bounds are named assumptions,
   never measured latencies; `LockedOps.lockKosten` (verified to exist) is
   left as the separate shape count, no LOCK latency assumed.
3. Cost-7 claim reproduces. `zeugeProg` in `Ausfuehrung.lean` is exactly
   `[movImm64, store64, load64]`; under the witness table that is 1+3+3=7,
   and `zeuge_speicher_aendert_sich` (proved by `decide` in the accepted
   model) gives the real store-changing run (rbx=42, byte 8192 zero-to-42).
   `laufKosten_zeuge_erfolg` conjoins the `decide` cost fact with that
   theorem: a genuine non-degenerate joint witness, not an empty run.
4. MXCSR admission mirrors the accepted profile. `profilZeuge_gueltig`
   (`0x1F80` valid) and `profil_nicht_global` (`0x9F80` refused) match the
   accepted `mxcsr_standard` / `mxcsr_ftz_verweigert` pair in
   `Gleitprofil.lean`. Validity is per selected profile; no global silicon
   claim.
5. Lemmas are genuine, premises used. `anhang_erfolg` concludes a real sum
   split (both success premises used: head part by induction, tail part at
   the empty prefix); `schranke` concludes `t <= B * prog.length` with the
   bound hypothesis applied at every head and the success hypothesis at
   every outcome. Refusal lemmas propagate `none` both ways. No conclusion
   restates a premise; no contracts quantified away; nothing unexecutable
   is called a semantics.
6. Negative cases present: `ret` refusal by `decide`, head-refused and
   tail-refused lemmas, plus one joint `_zeuge` instantiation per generic
   lemma. CUTS block is explicit (no simulation/lowering, no progress or
   waiting claim, TSO granularity, narrow widths, sticky/NaN, code
   immutability, budget stops, observation channels, fault-vs-refusal
   separation, and the `simp`-loop proof-engineering note). `#print axioms`
   for every main theorem is present.
7. No forbidden tactics. Word-boundary grep for
   `sorry|admit|axiom|native_decide|unsafe` over the candidate module is
   empty (the two naive-grep hits are the English word "admitted" in
   comments).

## Reproduced build evidence (my clone, candidate files staged)

- `./lean-probe grammatik/Grammatik/X86/HardwareAssumptions.lean`:
  `== 0 error(s) ... exit 0`; axioms exactly as reported (several `none`,
  rest `[propext]` or `[propext, Quot.sound]`); no `sorry`/`admit`/`axiom`.
- `./lean-bau`: `Build completed successfully (399 jobs)` (399 vs the
  reported 393 is base drift: my HEAD is newer; green either way).
- `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`:
  `gabbro_ziel` still on `[propext, Classical.choice, Quot.sound]`.
- Umbrella diff is one purely additive import line. (Against current HEAD it
  lands after `ByteSwap` instead of after `AccessList`; import-union detail
  for the merger, not a defect.)

## Nits (not defects)

- The author report writes `zeigeProg`/`zeigeZustand`/`zeige_speicher_aendert_sich`;
  the accepted identifiers and the candidate file both use `zeuge*`.
  Prose-only slip; the file compiles.
- The transient `failed to create thread` (exit 134) episodes in
  BUILD-EVIDENCE are environmental load crashes, honestly recorded with
  retry-green; both of my runs passed first try.

## Verdict

The delivered bounded claim — per-profile hardware-assumption records with
admission separated from data, and a conservative cost aggregation with
append split and explicit per-step bound over finite decoded sequences,
witnessed jointly with a real store-changing run and explicit refusals —
is proved as stated, with nothing claimed about simulation, lowering,
physical hardware, progress, waiting, or measured speed. No safety
weakening, no vacuity, no forged evidence found.

CANDIDATE: 434 9fac0f135cb48cc004935a4d09ba2dc5367ff478
VERDICT: ACCEPT
