# MUSE-REPORT-661: Exact review of author 660 (coherent multicore architectural execution)

Clone: `/home/simon/Dokumente/gabbro-muse/a661`, branch `muse/661` (verified).
Own only this file. No source touched (`git status` clean before and after;
read-only inspection plus `git show` of base objects; scratch only in `$TMPDIR`).

## CANDIDATE and VERDICT

CANDIDATE: 660 1298b05ebcedb35f436355774109df94a8e3442b

VERDICT: ACCEPT

Scope of this ACCEPT (substantive verdict unchanged): bounded skeleton with
integration conditions F1-F3 below; no hardware-model-completion claim.

## What was reviewed

Exact pinned snapshot as delivered in `.tmp/review/author-660/`:
`PATCH.diff` (1033 lines, exactly 3 files: `MUSE-REPORT-660.md`,
`grammatik/Grammatik.lean` one additive import line,
`grammatik/Grammatik/X86/HardwareExecution.lean` 902 lines),
`OWNER-TASK.md`, `MUSE-REPORT-660.md`, `BUILD-EVIDENCE.json`,
`SNAPSHOT.json` (author 660, head above, base `1d087115`, clean).
The commit object itself is not fetchable from this clone (author branches
stay local; no remote), so the review rests on these exact snapshot copies.
The base commit `1d087115` exists in local history and every dependency below
was verified against it, not just against drifted master.

## Verification performed

1. Ownership: PATCH touches exactly the 3 files the lane owns. No source,
   checker, Spec, goal, emitter, or friend-reserved files touched.
2. Hygiene of the 902-line module: no `sorry`/`admit`/`axiom`/`native_decide`/
   `unsafe` tokens (only English words "admitted"/"admits"); no `intro _` or
   `have _ :=`; no premise typed `Prop` itself; every premise of every theorem
   is used by its proof (checked theorem by theorem, including shadowing-safe
   `cases h with | gibAus ...` in `hwGibAus_kein_speicher` and the `b`-using
   `hwPilot_kein_halt`).
3. Base-exact API check at `1d087115` (all 9 imports present; every cited
   signature byte-identical there): `stepExt_pilot`, `stepExt_pilot_verweigert`,
   `stepExt_muldiv_halt`, `stepExt_vec_verweigert`, `stepVector_profil_verweigert`
   (VectorCodec, needs `vecEintritt b = false`, discharged via `osXmm`),
   `load_nach_issue`, `flush_schreibt_kopf`, `issue_haengt_an`,
   `issue_kein_speicher`, `merkmalZugelassen_heisst_beide`,
   `WortGruppe`/`FremdFrei` shape (destructuring `⟨hbufl,_⟩`/`⟨_,hff⟩` and the
   `(hff d hne e hmem) hfuss : False` application both match),
   `gruppe_verweigert_lock`, `laufAlt` definition shape (`unfold`+`rw` valid),
   `fetchExt`/`stepExt`/`ExtInstr` (exactly 8 constructors, matching the
   report's "8 families")/`ExtAusgang` shapes, `fpSchritt : ... -> Option`,
   `SperrBefehl.xadd64`, `basisHw`/`basisBereit`, `vecEintritt`.
   No call invents or reinterprets an accepted equation; argument orders match.
4. Build evidence in snapshot: final `./lean-probe` 0 errors, full `./lean-bau`
   green (460 jobs), `#print axioms` show `propext` / `propext, Quot.sound`
   only — within the `gabbro_ziel` standard. Intermediate red probes in the
   evidence log are normal incremental development, all repaired in-file.
5. Witness genuineness: core 0 fetches real bytes
   (`encodeNarrow (.mov32rr .rax .rcx)` 3 bytes ++ `fpEncodeMovsdRR` 4 bytes at
   4096) through accepted `decodeExt`/`stepExt`; closed `decide` facts pin
   RIP 4096->4099->4103, rax 5->9 (32-bit zero-extend of rcx=9, consistent),
   xmm0-low ->7, buffers empty; TSO stage issues byte 42 at 8192, observes own
   forwarding (42), foreign staleness (0, i.e. no foreign forwarding), then
   drains through accepted `flushKern` so shared memory changes 0->42,
   observed from both cores. Non-degenerate and memory-changing. Planted
   refusals proved: fetch on non-executable core 1 (`rfl`), code load/issue
   (`decide`), packed-int without OS vector state (accepted refusal lifted),
   LOCK (`= none`), foreign-footprint overlap and 2-of-8 tearing (group
   refusals). No SC word effect is ever substituted for a buffered access:
   `hwWortAusgabe` is eight `issueByte`s with proved memory silence.
6. Manual provenance: local `.tmp/HARDWARE-REFERENCES/` SDM PDF+TXT present;
   cited headings verified present in the extract (scalar MOVSD x2, LOCK prefix
   section, memory-ordering TOC 10.4.6, SETCC). The report's REFERENCES.json
   hash prefix differs from the local untracked file (local sha256 starts
   `9aed69388c9e`); the file is untracked so this is base drift or a local
   refresh, and the claim is provenance-only either way. Offsets not
   byte-verified; no finding, since no hardware correspondence is claimed.
7. No guarantee weakening, no desired-simulation premise: embeddings cite
   accepted selection lemmas with exact admissibility; divide halt is carried
   as `halt`, never hidden; unsupported encodings refuse; CUTS disclaim silicon
   correspondence, LOCK path, fence wiring, TSO->W/GX, interrupts and timing,
   and state plainly that the skeleton does NOT complete the hardware model.
   The coverage table marks every unstepped row as missing.

## Findings (integration conditions, not REPAIR)

F1. No closed inhabitant of `HwSchritt` exists: register steps keep the
    `hmem : t'.kern.speicher = m.mem` gate as a premise, and at the pinned
    base there is no accepted per-form memory-silence lemma to discharge it
    with. Worse, `Speicher` equality for computed successors needs function
    extensionality, outside the `gabbro_ziel` axiom standard, so the gate as
    stated is likely undischargable in closed form. The author's choice to
    leave it a premise is therefore correct, but one report sentence
    overstates it ("only the two witness forms discharge it end-to-end (via
    accepted memory-silence lemmas)"): nothing discharges it, and no such
    accepted lemmas exist at base. The Lean artifact and CUTS make no such
    claim. Correction: one sentence in MUSE-REPORT-660.md on re-integration;
    producers 666/668 should reformulate the gate pointwise/byte-wise over the
    footprint instead of `Speicher` equality.
F2. `hwByteschrittReg`, `adapterInteger666` and `adapterFp668` re-embed core
    data unconditionally, silently dropping any memory effect a
    memory-changing form would compute; a load form through the `reg` path
    would additionally read `m.mem` and bypass TSO forwarding (stale reads).
    No theorem claims general correctness of these computations and the
    discipline (memory forms via §3/§6 issue events, per-form silence
    obligation) is documented in §7/§11, so this is a documented footgun, not
    a false claim. Condition: producers 666/668 must discharge per-form
    silence or route memory forms through issue/load events; never widen the
    register path without the gate.
F3. `hwWit_o1_mem_still` / `hwWit_o2_mem_still` hold by construction
    (`setKernVonFp` keeps `m.mem`) and are observations, not silence evidence.
    Read that way they are fine; they must not be cited as silence proofs.

None of F1-F3 is invented determinism, a weakened guarantee, or fake closure,
and each is bounded by precise CUTS. Hence ACCEPT as a skeleton with the above
producer conditions, not REPAIR.

## Bounded acceptance scope

Accepted: one coherent selected composition (single shared canonical memory
proved coherent by construction, per-core TSO buffers, checked profiles with
step preservation), exact-condition embeddings of pilot/extended evaluation
including halt and refusal, byte-issue word discipline with tearing/overlap/
LOCK refusals, a reached two-core fetched-byte + TSO-drain run, refused
defaults for locked662/fault670/interrupt672 and register-path plugs for
integer666/fp668, sequential producer order 666->668->662->670->672.
Not accepted (still OPEN, per the candidate's own CUTS): hardware
correspondence, LOCK RMW, fence-step wiring, per-access TSO->W/GX simulation,
source/IR/ABI/loader/entry/budget links, interrupts/async, timing, and every
success row beyond the two witness forms.
