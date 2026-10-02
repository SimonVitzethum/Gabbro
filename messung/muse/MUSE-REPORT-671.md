# MUSE-REPORT-671: Exact review of author 670 (fault and exception transitions)

CANDIDATE: 670 3f55ce05c03dc64a5471d1e33606874434cdf8f0

VERDICT: ACCEPT

## Candidate detail

Files (from pinned snapshot bundle): `MUSE-REPORT-670.md`,
`grammatik/Grammatik.lean` (+1 additive import), `grammatik/Grammatik/X86/HardwareFaults.lean` (530 lines).
Note: the pinned commit object is not present in this reviewer's clone, so the
exact review was conducted against the pinned snapshot bundle
(`.tmp/review/author-670/`, PATCH.diff 621 lines, byte-identical 530-line module
copy) plus the author's BUILD-EVIDENCE.json and independent reproduction below.
No source or live-control change is made by this lane; this report is the only
owned deliverable.

## Substantive verdict (bounded acceptance)

Bounded acceptance: the candidate proves what it claims over the reused
canonical dispatchers, with honest CUTS boundaries. No repair required.

## Evidence

- Reproduction: the exact snapshot module was copied into this reviewer's tree
  (newer base fbd0c965), umbrella import appended, `./lean-probe
  grammatik/Grammatik/X86/HardwareFaults.lean` => `== 0 error(s) ... exit 0`.
  Tree restored clean afterwards (`git status --short` empty). Axiom lines from
  that run: every classifier/observation at most `[propext, Quot.sound]`, several
  with no axioms -- a subset of the `gabbro_ziel` standard
  (`propext, Classical.choice, Quot.sound`). Author's own BUILD-EVIDENCE shows
  `./lean-bau` green at 460 jobs on the exact base.
- Hygiene: no `sorry/admit/axiom/native_decide/unsafe`, no `intro _` or
  `have _ :=` discard, no premise of type `Prop` itself (machine-checked grep
  over the snapshot file; only hits are prose mentions inside comments). Every
  theorem's premises are used. No quantification over source syntax, so rule 13
  needs no per-theorem `_zeuge`; the joint witness `fehler_zeuge_gemeinsam`
  ties a reached two-cell memory-changing store run (8192 and 8200 hold 42 from
  a zero start, via accepted `extWit_zwei_schritte_speichern` /
  `extWit_anfang_null`) to a #DE divide, a truncated-fetch refusal with no
  fault, and an in-class dark-store refusal. Non-degenerate: yes.
- Reference resolution: every external name used by the candidate exists with a
  matching signature in the accepted tree (`fehler_div_null/ueberlauf/idiv_null_haelt`,
  `fehler_cmov_mem_untaken_haelt` (conjunction, correctly destructured),
  `stepExt_muldiv_halt`, `extWit_vec_ohne_os_verweigert`,
  `fehler_div_null_haelt_zeuge`, `fehler_idiv_oben_haelt_zeuge`,
  `extWit_zwei_schritte_speichern`, `mdZustandNull`, `dfZustandIdivMin`,
  `witDunkel`, `write64_verweigert`, `gegenbeispielC_verweigert`,
  `pin_ext_nichts_unbekannt`, `extWitBereit/Start/Unbereit`).
- Architecture checks:
  - `ExtAusgang` has exactly three constructors (`weiter/halt/verweigert`); the
    only `.halt` producer in `stepExt` is the `.muldiv` arm on
    `mulDivSchritt = .hardwareHalt`, so `klassifiziereExt .halt = some .de` is
    sound inside the model (halt iff divide trap). Refusal (`none` /
    `.verweigert`) is never classified as a fault on any arm -- the
    admission-vs-hardware distinction the task demands.
  - Divide #DE facts go through real execution (`mulDivSchritt`, incl. through
    `stepExt`), reusing accepted trap lemmas; RAX/RDX destinations correctly
    carry no claim (undefined per the manual entries).
  - `untaken_kein_stiller_erfolg` correctly derives `False` from the accepted
    `fehler_cmov_mem_untaken_haelt` equation -- no silent fault-free untaken
    operand, no desired-simulation premise.
  - Fetch facts (`0xFF` illegal, truncated `jump32` 0xE9, execute-denied `ret`)
    are `rfl` computations on actual bytes through `extByteschritt`; the `0xFF`
    case is proved refusal-only with #UD membership explicitly OPEN (no silent
    #UD equation -- correct, since refusal may be illegal OR unmodelled).
  - Control-state refusal (packed-integer without OS vector state) stays a
    refusal with no fault claim (would-be #NM OPEN); unaligned access at 8193
    reads/writes with no alignment check (matches silicon absent flag setup;
    flag-gated #AC OPEN); overlap refusal reused, not restated.
  - Manual provenance verified against the local snapshot: Table 6-1 vectors
    (#DE 0, #UD 6, #NM 7, #SS 12, #GP 13, #PF 14, #AC 17, #XM 19) and Vol.1
    §3.3.7.1 canonical addressing incl. the 48-bit implementation note and the
    stack-vs-other (#SS vs #GP) rule. DIV/IDIV entries exist in the reference;
    trap semantics are inherited from accepted `MulDiv` lemmas, stated as such.
  - Scope boundary with lane 672 respected: observations are pre-state
    (fault RIP + unchanged memory), no handler call, no RIP advance, no IDT /
    stack-switch / error-code model. CUTS names fault priority, #GP-vs-#PF
    disambiguation (no paging in the model), privilege, #UD membership,
    unmasked #XM, flag-gated #AC, CR0-gated #NM, TSO/GX bridge, silicon
    verification and source stop-class transfer as OPEN.
- Negative mutations present: illegal/truncated/execute-denied fetches,
  control-state refusal, dark-store refusal, overlap refusal, untaken-CMOV
  refusal -- all computed refusals, not vacuous.

## Observations (not repairs)

- `leseKlasse`/`schreibKlasse` pin a refused access to `some .pf` while the
  permitted set is `[#SS|#GP,#PF]`; the proved theorems claim only set
  membership of the pinned witness, and CUTS forbids relying on the pinned
  member. Acceptable as a bounded modelling pin with no downstream consumer
  (adapter660 uses only `klassifiziereExt`), but a future consumer must use the
  set, not the pinned value.
- `storeVerweigert_erhaelt`'s first conjunct is near-trivial given its premise;
  it is packaging for the joint witness, not a rule 4(a) violation in
  substance (the second conjunct adds the class).
- The 48-bit canonical width is hardcoded per the manual's first-implementation
  note; any future profile with 5-level paging must revisit `istKanonisch`.
  Documented in CUTS-adjacent comments; fine for the admitted profile.

## Remaining open (per candidate CUTS, endorsed)

Fault priority, #GP-vs-#PF disambiguation, privilege/stack-switch and all
delivery detail (lane 672); #UD membership of refused bytes; unmasked #XM,
flag-gated #AC, CR0-gated #NM; TSO/GX bridge; silicon verification; source
stop-class transfer. No completion claim is made or granted.
