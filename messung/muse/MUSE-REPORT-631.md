# MUSE-REPORT-631: Independent review of author 630 (SourceAccessCompleteness, G5)

CANDIDATE: 630 4c0b97edcaf0be37d0427bec7dd1ccdce19b5cf2
VERDICT: ACCEPT

Reviewer lane 631, clone `/home/simon/Dokumente/gabbro-muse/a631`, branch `muse/631`.
Owned file: only this report. No source, Spec, or umbrella edits were made or committed.

## Identity and scope verification

- `SNAPSHOT.json` pins head `4c0b97edcaf0be37d0427bec7dd1ccdce19b5cf2`, base
  `a71b7e638d008cab47f352326a09e37980cff314`, files
  `MUSE-REPORT-630.md`, `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/SourceAccessCompleteness.lean`, clean `true`.
- Fetched `muse/630` from the author clone into local ref `muse/630-snap`:
  rev-parse equals the pinned HEAD exactly.
- `PATCH.diff` is byte-identical to `git diff base..head` (`cmp` clean, 41140 bytes both).
- Real diff touches exactly the three registered files: +105 report, +1 umbrella import,
  +733 new module. No other clone content involved.

## Build verification (reproduced, not trusted)

- Installed the exact candidate file transiently in my own clone (base `66e6e9b0`,
  strictly newer than the author base) and ran the queued wrapper:
  `./lean-probe grammatik/Grammatik/X86/SourceAccessCompleteness.lean` gives
  `== 0 error(s) in the COMPLETE output; exit 0`.
- Every `#print axioms` line is within `propext`, `Classical.choice`, `Quot.sound`
  (most use fewer; the two alignment facts use none). Exact-word scan for
  `sorry|admit|native_decide|unsafe|axiom`: zero hits. No `Prop`-typed premises,
  no `intro _` / `have _ :=` discards.
- Full `./lean-bau` was not rerun by this reviewer; the author's 447-job evidence
  stands, the probe above re-verifies elaboration against the newer base, and the
  serial merge gate builds before committing anyway.
- Transient file removed afterwards; final tree contains only this report.

## Interface verification (real producers, no toy semantics)

All consumed names resolve to existing producer modules with matching shapes
(verified by grep and, decisively, by the green elaboration itself):

- Source side: `execStmt`, `eval`, `Stmt.assignSlot`, `repOk`, `rep_schritt_bleibt`
  (+ its joint witness `rep_schritt_bleibt_zeuge`), `repOk_klingt`, `RepSlot`,
  `zahlWort_wortZahl`, `schreibSlot_fremd_tab`, `disjunkt_von_layout`, and the
  `witD`/`witI`/`witE`/`witHw`/`witHL`/`witSigma`/`witSL`/`witVal`/`witHT`/`witM`/`witA`
  witness family from `SourceMemory`.
- G side: `zugriffe`, `SchreibG`, `LiestG`, `ZugriffG`, `TraegerGleich`,
  `brueckenG`, `brueckenRahmen`.
- Target side: `schritt`, `realisiert_store64_fuss`, `realisiert_load64_gefunden`,
  `zugriff_store64_acht`, `Zugriffe.zugriff` (`.schreiben`/`.speicherWert`),
  `effAddr`, `slotAddr`, `laengeOk`, `write64`/`read64`/`lesbar8`,
  `zeugeReg`/`zeugeFlags`/`zeugeSpeicher`, `ausgerichtet8`, `OhneUmbruch`, `Disjunkt`, `Fuss`.
- Handoff vocabulary `BrueckenProfil`/`WortGuard` exists and is reused by name in
  CUTS, never redefined. No new names collide with the existing tree.

## Semantic findings

- `fragmentDelta_voll`: genuine new connection — actual `execStmt` assignSlot trace
  delta proved equal to `fragmentListe` via `take_neuAppend` + `filterMap_leseEv`.
  Not a restatement of `AccessList.zugriffG_voll` (which the report correctly cites
  as the generic counterpart); the new content is the enumeration computed from
  actual `i.orte ++ e.orte` data.
- `blattFragment_voll`: genuine — G access list equality plus the recorded write,
  footprint-carrier reads, and slot ownership where the changed-memory disjunct for
  every other carrier is discharged via `schreibSlot_fremd_tab` (tables) and
  by-construction glob equality. All machine premises (`hM`, `hM'`, both memory
  links) are used.
- `fragmentStore_passt` / `fragmentLoad_passt`: genuine consumer-side connections,
  not wrappers — the new links are `hAddr`/`hReg`/`hSlot` tying one realised
  `schritt` to the source slot and value. Every one of the ~40 premises of
  `fragmentStore_passt` is consumed (checked by reading the proof term flow).
- `regelOk_nur`: proved by casing on the actual statement with the catch-all
  discharged by `simp [regelOk]` — a real refusal of every non-assignSlot form.
  `IstAssignSlot` as a classifier family is justified (statement-index equation
  would be ill-typed).
- No conflation found: integer bounds travel with `repOk`/`zahlWort_wortZahl`
  (`0 <= lo`, `hi < 2^64` in the load path); no FP, no fault model, no atomicity
  claim — footprints stay sequential and CUTS explicitly leave per-access TSO
  refinement, `valX86_sound`, hardware, OS/loader and int->ptr with the open side.
- No unreachable claims: all `decide` steps kernel-evaluate; spot-checked
  independently (see below).

## Witness and refusal spot checks

- Joint non-degeneracy holds: witnesses build on `rep_schritt_bleibt_zeuge`
  (one table its function writes, source slot `0 -> 42`, changed target bytes)
  and add reached realised steps with observable changes
  (store bytes `0 -> 42` both sides; load destination sentinel `7 -> 0`, memory
  unchanged). `blattFragment_voll_zeuge` lines a real G frame over `brueckenG`.
- Independent `#eval` probes through the queued wrapper (same elaboration):
  `repOk (.opt 5) … = false`, `repOk (.int 0 100) … = true`,
  `fragmentZielOk 4096 1 = false`, `fragmentZielOk 4096 0 = true`,
  `fragmentListe () [] = [(Sum.inl (), true)]`. Planted refusals fire, positives hold.

## Notes for the merger (non-blocking)

- The umbrella context drifted: the author base ends `Grammatik.lean` with
  `VectorCodec`, my HEAD ends with `FloatSourceObservations`. Re-add
  `import Grammatik.X86.SourceAccessCompleteness` at the then-current end;
  expect the standard import-union step, no semantic conflict.
- `MUSE-REPORT-630.md` claims were checked against the file: 733 lines, theorem
  names, axiom statement, commit list shape — all accurate. The "no ~70-rule
  assertion" scope is respected throughout; full source-to-final-bytes remains
  OPEN as stated.
- Nothing in the owner task text was found wrong.
