# MUSE-REPORT-1030: Exact review of author 880 (copy coalescing rule)

CANDIDATE: 880 5bce2fe69be57860f7b28e8b74f375c1140be07f
VERDICT: REPAIR

## Scope verified

- Snapshot: `.tmp/review/SNAPSHOT.json` pins author 880, head
  `5bce2fe69be57860f7b28e8b74f375c1140be07f`, base `b040b155` (matches this
  clone's master), files `MUSE-REPORT-880.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/OptCoalesceMove.lean`, clean tree.
- PATCH scope confirmed: one import line appended to `grammatik/Grammatik.lean`
  plus the new 291-line file plus the report. No MARKE_EMIT, numbers,
  source/checker/Spec/goal/emitter, or friend-reserved optimiser files touched.
- DESIGN citation confirmed: `DIRECT-COMPILER-DESIGN.md` §7 example 1 (copy
  folding, premise avail + dominance + width, redefinition counterexample) and
  the section 7 "Layout / allocation" row failure case (address-taken spill via
  call arg). The stated premises match the row.
- Hygiene confirmed by inspection: no `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe` in the candidate file; every premise is consumed by its proof (no
  `intro _` discard); CUTS block and `#print axioms` for every main theorem
  present; witness uses the non-degenerate `ReferenzB` backbone
  (`refEin_schreibt`, `refB_erreicht`, `refB_schreibt`: table-writing contract,
  reached run with memory-changing step), same as accepted sibling lane 860
  (`OptFoldConst.lean`, in master).
- Build evidence relied on: `.tmp/review/author-880/BUILD-EVIDENCE.json`
  (`./lean-bau` exit 0, 511 jobs, `Built Grammatik.X86.OptCoalesceMove`,
  axioms within `[propext, Classical.choice, Quot.sound]`). No source changes
  are owned by this review, so no build was re-run here.

## What is genuinely proved (kept, not disputed)

- Section 1 refusal lemmas (`coalVerweigert_avail`, `_dominiert`, `_weite`,
  `_adressGenommen`, `_callArg`) plus three `decide` probes: real negative
  mutations of the decided Bool, including the exact DESIGN failure case.
- `coalWort` (+ probe): real word round-trip proof under the validator-decided
  range fact `hW`.
- The witness `OptCoalesceMove_verbindung_zeuge` jointly inhabits all premises
  on a non-degenerate program with a memory-changing reached run.

## Findings (repair drivers)

F1. Connection conclusion restates its own premises (HARD RULES 4a).
`OptCoalesceMove_verbindung` concludes, jointly: (C1) value equality at one
world, which is `congrArg (·.n) (hWert w0 w0)` — a direct instance of premise
`hWert : ∀ w w', eval w eKopie w' ρ = eval w eOrig w' ρ`; (C3) the word image,
which is `coalWort _ hW` — premise `hW` fed to a helper; (C2) `execEnd`
equality, closed by `simp only [execEnd, ho, hv]` from assumed `hv`/`ho`. The
rule's core — that the copy carries the source value — is assumed (`hWert`),
not proved. Only C2 adds content (bind-window outcome determined by
eval+orte), which is a property of the canonical semantics, not a justification
of the optimisation. Accepted sibling 860 proves its integer connection by
`rfl` from fixed syntax; 880 has no computed value fact for the integer core.

F2. The DESIGN side-condition certificate is formally unlinked from the
rewrite. `CoalRewrite`/`CoalAnalyse` never mention `eOrig`/`eKopie`; `hz :
coalZulassen rw an = true` is consumed solely as the antecedent guard of the
assumed implication `hOrte : hz → orte-equality`. No theorem connects admission
to any semantic fact, so a Bool-only validator cannot discharge `hWert`/`hOrte`
from recomputed avail/dominance, and a validator strong enough to prove them
per site needs no Bools. The witness confirms the gap: its `hWert`/`hOrte`
discharges are `fun _ _ => rfl` / `fun _ => rfl`, which hold independently of
`hz` — the certificate is not exercised even there.

F3. Claim boundary overstates the link. The section-3 doc comment presents
`hWert` as "the validator-recomputed avail fact", and the author report claims
"value preservation" proved, but no recomputation link is stated or proved,
and CUTS omits this gap (it lists float window, chains, machine-work, silicon/
TSO/ABI, memory-copy — all fine — but not the missing admission⇒semantics
bridge). Float `coalGleit_behält`'s conditional `hEq` matches accepted 860
practice and is NOT a repair driver on its own.

## Minimal repairs (any one of R1/R2, plus R3)

- R1 (preferred): tie the certificate to the expressions. `Syntax.Expr` HAS a
  `var` constructor (`Syntax.lean:346`), so state the rule over a concrete copy
  shape (e.g. `eKopie` a variable read of the just-bound slot at the
  `Endblock.bind eOrig rest` window), where eval equality is computed from the
  bind semantics instead of assumed for arbitrary expressions, and derive at
  least the orte equality from the admitted side conditions + syntax. Then the
  avail/dominance/width/spill/call-arg Bools do real work.
- R2 (alternative): keep semantic premises, but prove at least one instance of
  the admission⇒semantics bridge and record in CUTS that per-site discharge of
  `hWert`/`hOrte` from recomputed avail/dominance is an explicit open
  obligation owned by a named validator/lowering lane, with the witness's
  hz-independent `rfl` discharges explicitly NOT counting as such discharge.
- R3 (wording, required either way): stop presenting `hWert` as "the
  validator-recomputed avail fact" in the section-3 doc comment and the
  "proves value preservation" sentence in the author report; state exactly
  which equalities are assumed and which are proved.

## Bounded acceptance (explicitly NOT granted)

No byte-level, REX/width/flag, TSO/atomicity, MXCSR/interrupt-gate, or silicon
claim is made — correctly out of scope per CUTS (correspondence stops at
canonical words and `gleitPasst` values). That boundary is precise and is not
part of the repair.

## Last build result

No build owned by this lane (report-only review; no source files owned).
Upstream evidence cited above: `./lean-bau` exit 0, 511 jobs, standard
`gabbro_ziel` axiom set.

## What remains open

- Author-880 resubmission addressing F1–F3 (R1+R3 or R2+R3), then exact
  re-review against the new pinned HEAD.
- Full source-to-final-bytes validation and the per-access target-to-W/GX
  bridge remain OPEN at program level (unchanged by this review).

## Task feedback

Nothing in the review task is believed wrong. One calibration note: the
conditional-recomputation premise shape (`hEq`-style, validator recomputes the
equation) is accepted series practice for floats (lane 860); the repair above
targets only the integer core, where the accepted bar is a computed value fact
and 880 instead assumes it.
