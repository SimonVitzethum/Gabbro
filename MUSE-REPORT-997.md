# MUSE-REPORT-997: Exact review of author 847 — mapping-permission closing

CANDIDATE: 847 ae8b2acd4e135ee4f4098183c66161b53e07e578

VERDICT: ACCEPT

(Bounded acceptance, §7. One candidate, one verdict, per the lane task.)

## 1. Pin, ownership, and method

- Snapshot pin: author 847, HEAD `ae8b2acd4e135ee4f4098183c66161b53e07e578`,
  base `e7c75908456285d1e37c18dc32d4f9c0e10d1fa4`, `clean: true`
  (`.tmp/review/SNAPSHOT.json`).
- Files in the candidate (PATCH confirms exactly these three, nothing else):
  `MUSE-REPORT-847.md` (new), `grammatik/Grammatik.lean` (one added import
  line, `import Grammatik.X86.ComposeMapPerms`), and
  `grammatik/Grammatik/X86/ComposeMapPerms.lean` (new, 456 lines).
- No diagnostic/gift/example/CLI numbers, no `MARKE_*` changes, no
  source/checker/`Spec`/goal/emitter edits, no friend-reserved optimiser
  files. The diff touches no file outside the lane's owned set.
- Reviewer clone/branch verified: `/home/simon/Dokumente/gabbro-muse/a997`,
  `muse/997`. I own only this report; no source or live controls touched.
- Method: full read of the snapshot file (all 456 lines), the PATCH, the
  owner task, and the build-evidence trail; cross-checked every reused
  producer name and signature against the producer modules in my own clone
  (`ValidatorSkeleton.lean`, `Byteschritt.lean`, `Zugriffe.lean`); consulted
  the local hardware-reference metadata (`REFERENCES.json`, Intel combined
  volumes edition 325462-093US, September 2026). No network, no provider,
  no other clones, no keys.

## 2. What the candidate does (accurately described)

New interface `zugriffLesbar` / `zugriffSchreibbar` (snapshot lines 26/31:
`lesen.all lesbar`, `schreiben.all schreibbar` over one extracted
`Zugriff`), two eight-byte permission lemmas (`read64_lesbar8`,
`write64_schreibbar8`, lines 36-52, proved by unfolding `read64`/`write64`
and case-splitting the permission guard), two footprint-wide lifts
(`fuss_all_lesbar`, `fuss_all_schreibbar`, lines 55-72), the generic closing
step `ComposeMapPerms_verbindung` (lines 87-265, case analysis over all 14
pilot forms), the joint companion `ComposeMapPerms_verbindung_zeuge`
(lines 351-387) on a two-section witness, four `by decide` observations,
and three planted refusals (lines 396-414). The author report matches the
file exactly; no claim inflation found.

## 3. Architecture review (byte forms through canonical execution)

- Byte forms: the witness builds code bytes with the canonical `encode`
  (`store [rsp], rax`), never hand bytes. Decode coverage is part of the
  consumed admission (`valX86 = wohlgeformt && bildDeckung`), and fetch
  re-checks consumed-length/remaining-suffix consistency plus `laengeOk`
  (`fetchDekodiert`, `Byteschritt.lean` lines 49-56). No parallel decoder,
  no trusted hint.
- REX/register/width/flag semantics: inherited from the accepted `schritt`
  and `Codec` by name; nothing re-proved, nothing shadowed. The closing
  step adds no execution semantics of its own (the only new `def`s are Bool
  predicates over an extracted `Zugriff` plus witness vocabulary), so there
  is no duplicated interpreter or executor.
- R/W/X per address: R/W come from successful `read64`/`write64` carrying
  their eight-byte checks, lifted to footprint-wide `List.all` facts; X
  comes from the X-gated fetch correspondence
  (`fetchDekodiert_entspricht`) rewritten into the loaded mapping via `hmem`.
  The conclusion's X leg is stated over `geladen bild bias`, i.e. the
  mapping↔permission composition the task asked for — not X over an
  unrelated memory.
- Fetch gating pins X against R: data is readable-but-not-executable in
  both the lane-319 precedent (`ketteDaten`) and this witness, and the
  fetch-from-data refusal (§5) shows readability never substitutes for
  executability.
- Pre-fault effects: permission failure is absence of transition (`none`
  through the `schritt_*_verweigert` chain reused by the
  `zugriff_*_versagt_kein_erfolg` lemmas); the candidate never claims a
  partial state update. No invented determinism: the only determinism
  stated is the observed witness step (`zeugenSchritt847`, `by decide`).
- Memory order / TSO / atomicity: correctly NOT claimed. Footprints are
  per-byte sets (`Fuss`), and the file's CUTS say so explicitly; the
  per-access target-to-W/GX simulation is left with the bridge owners.
- Feature/MXCSR/interrupt gates: no SIMD/FPU/interrupt forms exist in the
  14-pilot scope; extended forms are CUT, not assumed. Correct boundary.
- W^X: enforced at admission (`wohlgeformt` via `valX86_wohlgeformt`) and
  pinned by a planted refusal (§5), mirroring the accepted `valWx`
  precedent.

## 4. Premise-use and HARD-RULES audit

- All four premises of `ComposeMapPerms_verbindung` are used: `hval` via
  `valX86_wohlgeformt` (line 102), `hmem` for the loaded-mapping X rewrite
  (lines 104-106), `hf` via `fetchDekodiert_entspricht` (line 103), `hs`
  in every case branch. The generalized equation `h` and the fetch fact
  `hok` are consumed in each of the 14 branches. No `intro _`, no
  unused `have`, no `Prop`-typed premise.
- No conclusion-is-premise: the 8-conjunct conclusion (mapping admission,
  loaded X prefix, R/W footprint checks, three map preservations, write
  containment) is derived through named producer lemmas in every branch.
- No contract quantification, no fake semantics, no banned tactics: the
  full-file read shows no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
  (only the `#print axioms` commands, lines 416-417). Comment prose
  contains "admitted"/"admission" exactly as the already-merged
  `Byteschritt.lean` ("admitted instruction") does — gate-compatible.
- Every reused name verified to exist with a matching signature in my
  clone: `valX86_wohlgeformt` (`ValidatorSkeleton.lean` 54-58),
  `fetchDekodiert_entspricht` 4-tuple (`Byteschritt.lean` 157-181),
  `zugriff_*` footprint equations (`Zugriffe.lean` 63-163),
  `erfolg_*_ohne_speicher` (`Zugriffe.lean` 176-291),
  `schritt_pop64_speicher` (used at 279, defined alongside 271-280),
  `erfolg_store64/push64/call32_im_fuss` 5-tuples
  (`Zugriffe.lean` 361-462, matching the author's
  `obtain ⟨hframe, hpl, hpw, hpx, _⟩`), and all six
  `zugriff_*_versagt_kein_erfolg` lemmas (`Zugriffe.lean` 467-526).

## 5. Witness audit (joint, non-degenerate, memory-changing, reached)

- Shape: two-section accepted image (code R+X, 8 bytes; data R+W, 8 bytes
  with nonzero base byte 9), entry `rip` in code, `rax = 42`,
  `rsp = data base`, memory definitionally `geladen zeugenBild847 0`.
- Reached run: `fetchDekodiert` on the loaded state returns the store
  (`zeugenFetch847`), and `schritt` runs it (`zeugenSchritt847`:
  `rip = 0x1008`, base byte `42`), so the 9→42 change is a reached,
  memory-changing step, with the before-byte pinned (`zeugenAlt847`).
- Jointness: the companion feeds acceptance, `rfl`-mapping, fetch, and step
  into the main theorem and extracts changed-byte ∈ write-footprint via
  `hframe`. The inequality direction is correct (`Ne.symm hchg` matches
  `hframe`'s `s'.bytes x ≠ s.bytes x` hypothesis; the existential's
  `s.bytes ≠ s'.bytes` is `hchg` directly). No weakening, no detour around
  the composed step.

## 6. Refusal audit (all three genuine, no confound)

- Store-into-code (`zeugenSpeicherCode847_verweigert`): `store [rbx], rax`
  with `rbx = 0x1000` (R+X, non-writable) has no transition. The `laenge 7`
  is the canonical length for an rbx-based store — the lane-319 precedent
  documents `store [rbx], rax` (7) as an executable program form
  (`Byteschritt.lean` ketteProg), versus 8 for the SIB-carrying rsp-based
  witness store — so the refusal isolates permission, not a length check.
- Fetch-from-data (`zeugenFetchDaten847_verweigert`): `byteschritt` at the
  readable-but-non-executable data base refuses (`ausgangRip = none`).
- W^X image (`zeugenWx847_verweigert`): making the code section writable
  refuses `valX86`. Mirrors the accepted `valWx` precedent.
- No mutation or guarantee was weakened to make these pass; each refusal
  exercises a distinct gate (write permission, execute permission,
  admission).

## 7. Bounded acceptance and precise CUTS

ACCEPT covers exactly: the `zugriffLesbar`/`zugriffSchreibbar` interface,
the success-carries-permission and footprint-lift lemmas, the generic
closing step over arbitrary admitted images/biases/states/fetches/steps
(all 14 pilot forms, every premise used), the joint companion, and the
three refusals — all over the actual accepted vocabulary
(`valX86`+`wohlgeformt`+decode coverage, `geladen`+per-section
permissions, X-gated `fetchDekodiert`, `zugriff` footprints,
permission-checked `schritt`).

NOT covered (explicit CUTS in the file, never assumed): source
correspondence and duties; the per-access target-to-W/GX simulation;
silicon/caches/TLBs/store-buffers/interrupts/timing beyond decoded
refusal; extended forms past the 14 pilot constructors; standalone
arbitrary-input decoder length soundness (reused only through the runtime
checks of `fetchDekodiert`/`decodeFuel`); entry/budget-stop/relocation
beyond mapping admission, entry containment, and decode coverage.

Note (not a repair): the CUTS name missing-leg owners by role and wave
("bridge owners of the connection wave", "decoder owner") rather than by
numeric lane ID. Given the snapshot carries no other-lane registry, and no
missing leg is consumed as a premise anywhere, role-naming is sufficient
and honest.

## 8. Evidence and verification trail

- Author's queued-wrapper trail (`.tmp/review/author-847/BUILD-EVIDENCE.json`):
  final `./lean-probe` 0 errors; final `./lean-bau` green
  (`Build completed successfully (509 jobs)`); axioms for both
  `ComposeMapPerms_verbindung` and `_zeuge` are `[propext, Quot.sound]`, a
  subset of the standard `gabbro_ziel` set. The trail also shows genuine
  development (intermediate unsolved-goal, constructor-arity, and
  `sorryAx` errors, each fixed before the pinned commit) — not a
  single-shot green.
- My independent checks (read-only, inside my own clone): banned-token
  scan of the full 456-line file clean; all reused producer names and
  tuple shapes cross-checked with line references (§4); PATCH file set
  matches the owned set with no side edits; witness/refusal logic
  re-derived by hand (§§5-6), including the laenge-7-canonical analysis.
- Not re-run here: the candidate file is not part of my tree (my X86
  directory holds 145 modules, none of them `ComposeMapPerms`), so a local
  `./lean-probe`/`./lean-bau` run could only measure my base, not the
  candidate; no suspicious case survived analysis (§6), so no wrapper
  reproduction was warranted. The build green is the author's
  queued-wrapper evidence above, corroborated by the static checks in §§4-6.

## 9. Remarks on the task

Nothing in the owner task was wrong. The target statement
(`ComposeMapPerms_verbindung` + `_zeuge`) is proved as specified, with no
added premises and no weakened conclusion. No follow-up repairs requested.
The next composition steps (source correspondence, W/GX bridge, extended
forms) belong to their wave owners per the CUTS.
