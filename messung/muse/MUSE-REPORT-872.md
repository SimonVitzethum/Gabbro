# MUSE-REPORT-872: Optimiser rule — LICM rule

Lane 872, clone `/home/simon/Dokumente/gabbro-muse/a872`, branch `muse/872`.
Only touched: `grammatik/Grammatik/X86/OptLicmLoop.lean` (new),
`grammatik/Grammatik.lean` (one import line appended), this report.

## What was done

Implemented the DESIGN section 7 LICM row as a generic rule lemma over the
real source fragment (no accepted IR exists yet, so per the task the real
`Syntax`/`Semantik` `exec`/`execStmt` fragment is covered):
hoisting `x := e` (invariant, pure, non-faulting) from inside a taken
`Stmt.ite` branch to before the guard, via context-preserving
`Stmt.assignVar` (no de Bruijn lifting needed; the hoisted store is
env-only, never a world write).

Certificate shape (local rewrite record + recomputed analysis citations):
`LicmCert` = hoisted `LicmOp` kind (`addO/subO/mulO/divO/gleitO/tokenO`)
plus five validator-recomputed Bools
(`invariantOk/keinFehler/keinToken/gleicheRundung/recheckedFacts`);
admission `licmZulassen` is their conjunction with kind admission
(`licmOpOk`: `tokenO` refused by kind).

Refusals proved (each forces `licmZulassen = false`):
`licmVerweigert_tokenOp` (token op on shared access, by kind),
`licmVerweigert_div` (the `x/n`-above-`n!=0` CE-2 case),
`licmVerweigert_token/inv/facts/rundung`, plus decided probes
(`probe_licmZulassen_ok/divNein/tokenNein`).

Value/fault preservation: `licmAdd/Sub/Mul/Div/Rem_wert` over arbitrary
`Int` (`div`/`rem` keep the `M102` premises, so no `hardware` stop is
added); `licmGleit_behält` (admitted float hoist preserves value and
`gleitPasst` outcome in one kernel rounding; cross-scope refused);
`licmOrte_gleich` (both orders read the same carriers — concurrency).

Connection `OptLicmLoop_verbindung`: under admission (`hz`), purity
(`hRein`), conditional exact-value invariance (`hInv`), conditional guard
independence (`hGuard`) and trip evidence (`hTaken`), the taken-path
`execBlock` outcomes are equal (carries fault/contract/call-log/budget
agreement: same subterms under same worlds/envs), the invariant value is
preserved, and carrier reads agree up to order. Every premise is used by
the proof; nothing derives `ensures`; no refusal becomes a warning.

Witness `OptLicmLoop_verbindung_zeuge`: `y+3` above taken `y<=5` on
`refD`, with admitted certificate by `decide`, `hRein`/`hInv`/`hGuard` by
computation, non-degenerate (`refEin_schreibt`) beside the reached
memory-changing run (`refB_erreicht`, `refB_schreibt`).

New definitions/theorems: `LicmOp`, `licmOpOk`, `licmLeseLeer`,
`LicmCert`, `licmZulassen`, `licmVerweigert_tokenOp/div/token/inv/facts/
rundung`, `probe_licmZulassen_ok/divNein/tokenNein`, `licmAdd/Sub/Mul/
Div/Rem_wert`, `probe_licmAdd/licmDiv`, `licmGleit_behält`,
`probe_licmGleit`, `licmOrte_gleich`, `OptLicmLoop_verbindung`,
`OptLicmLoop_verbindung_zeuge`.

## Verification

Last `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (511 jobs)`.
`./lean-probe` on the module: 0 errors, no warnings.
`#print axioms`: every theorem within `[propext, Classical.choice,
Quot.sound]` (the `gabbro_ziel` standard; most need only `[propext]`).
No existing file changed except the one import line; no `sorry`/`admit`/
`axiom`/`native_decide`/`unsafe`; no diagnostic/gift/example/CLI numbers;
no MARKE_EMIT changes; no source/checker/Spec/goal/emitter edits; no
friend-reserved optimiser files touched.

## Open (see CUTS in the file)

Untaken path (dead-temp liveness is phase-B work); `sub`/`mul`/float/
`div` syntax windows (value level only); formal `totalCost` inequality;
trip-count reasoning beyond the reached guard; W/GX per-access bridge;
silicon/ABI/loader claims.

## Task remarks

Nothing in the task appears wrong. One scoping note: the "loop" is
covered as a guarded region (`ite`), not `traverse`/`retry`, because a
full loop-induction connection needs weakening infrastructure that does
not exist yet, while the DESIGN failure case (`x/n` above `n!=0`, CE-2)
is exactly a guard hoist; the trip evidence premise (`hTaken`) is the
honest form of the "reached computation" side condition.
