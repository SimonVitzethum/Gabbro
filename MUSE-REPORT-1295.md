# MUSE-REPORT-1295: Capstone — every classified union step projects to the TSO store-buffer model

## What was done

New file `grammatik/Grammatik/X86/HwKapsteinTso.lean` (~560 lines) plus one
`import Grammatik.X86.HwKapsteinTso` line appended to `grammatik/Grammatik.lean`.
No other existing file touched. Every accepted definition is reused unchanged
(lifted, never redefined); no `sorry`, `admit`, `axiom`, `native_decide`,
`unsafe`.

**Definition:**
- `kapTso` — projection of `HwMaschine` to the TSO-only machine:
  `tsoAnsicht m` (shared canonical memory plus per-core store buffers).

**Theorems:**
- `kapTso_setKernDaten`, `kapTso_setTso`, `kapTso_setKernVonFp` — projection
  equations (core-data updates are silent, memory/buffer updates project to
  the successor).
- `kap_basis_tso_klass` — exact base classification with the footprint named:
  register and fault steps are silent, loads observe with forwarding
  (`loadByte`), issues are single `issueByte` events, drains are single
  `flushKern` events with the buffer head named.
- `kapTso_erreichbar_trans`, `kapTso_schritt_erreichbar`,
  `kapTso_issueListe_erreichbar` — reachability induction over folded issue
  lists (word stores are eight byte issues, chained single `TSOSchritt`s).
- `kapTso_wortAusgabe_erreichbar`, `kap_wort_tso`, `kap_drain_tso`,
  `kap_fwd_tso`, `kap_stapelPush_erreichbar`, `kap_stapelCall_erreichbar`,
  `kap_stapel_tso` — word/drain/forwarding/stack adapters reach through the
  projection (stores buffer, drains flush, foreign issues issue, observations
  are silent with `m' = m`).
- `kap_basis_reichbar`, `kap_union_basis_tso`, `kap_union_wort_tso`,
  `kap_union_drain_tso`, `kap_union_fwd_tso`, `kap_union_stapel_tso`,
  `kap_fuenf_tso` — union lifts for the five classified tags (basis, wort,
  drain, fwd, stapel) plus the joint summary conjunction.
- `kapTso_basis_beob`, `kapTso_zeuge` — joint witness: four exhibited union
  steps (wort, stapel, drain, fwd from the families' own reached witnesses)
  reach through the projection, the exhibited base observation reads zero
  through it, and the two-core non-degeneracy holds on the same TSO model
  (owner forwards 42, foreign core reads stale 0, drain installs 42).
- CUTS block plus `#print axioms` for every theorem: all depend only on
  `[propext]` or `[propext, Quot.sound]` (subset of the goal standard; several
  are axiom-free).

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s)`, `Build completed successfully
(677 jobs)`. `./lean-probe grammatik/Grammatik/X86/HwKapsteinTso.lean`:
`== 0 error(s)`.
(Note: three `./lean-bau` attempts before the final one failed on the root
`Grammatik.lean` aggregation step only — `std::bad_alloc`, `failed to create
thread`, then unreadable toolchain `.olean.private` files — while the new
module itself compiled every time (probe 0 errors, built as dependency
[676/677]). Failure modes varied run to run and cleared without any source
change: resource/toolchain contention with other lanes' concurrent builds,
not a proof error.)

## What remains open (see CUTS)

- The remaining 16 union tags (lockRmw, isa, addr, muldiv, lockFetch, uc,
  port, fp, fehler, tor, vec, nested, int, system, bild, instanzen) are NOT
  classified here — these are the FINDINGs. In particular: lockRmw writes
  shared memory directly (`einbettenLock` takes the locked successor memory,
  not a flush) and needs the drained-own-buffer guard as a separate locked-RMW
  leg; the system plug installs memory directly (`sysSnapSchritt` ok-case);
  isa/addr need their own `concIssue` fold lemmas; uc/port take device paths;
  fp/fehler/tor/vec/nested/int/bild/instanzen need their control-state or
  register-path lemmas. No silent TSO bypass was found among them; each needs
  its producer file's equations.
- No W/GX bridge (target-only reachability); no whole-word atomicity beyond
  the guarded drains; no source/checker/contract/entry/budget claim; no
  hardware correspondence beyond self-consistency.

## What I believe is wrong in the task

1. "Every union step … is exactly one accepted TSO event (issue, flush,
   forward-read, locked RMW …)" is false as a single-step claim even for the
   classified families: a word store (`wortAusgabe`, `stapelPush`,
   drain/fwd `speichere`) is EIGHT byte issues, i.e. `TSOErreichbar` in up to
   eight steps, not one `TSOSchritt`. The file proves the honest multi-step
   form and keeps single-step exactness only where it holds (base issue,
   single drains/flushes, silent observations).
2. The full 21-tag single theorem is not dischargeable in one lane without
   re-proving producer internals: lockRmw and system steps change shared
   memory through non-TSO paths BY CONSTRUCTION, so they belong to a
   separate locked-RMW/direct-install leg, recorded as FINDINGs rather than
   forced into a TSO shape.
3. The MECHANISM paragraph describes connecting ONE family via a new
   `HwAdapter`, which does not match the TASK (capstone projection over the
   already-composed union); the file follows the TASK and reuses the
   `HwKapstein` union directly.
