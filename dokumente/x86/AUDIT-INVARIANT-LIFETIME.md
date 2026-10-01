# Audit: INVARIANT-LIFETIME — what `InvariantenOpt` / `AufrufOpt` actually prove

*Owner: lane 409. Owns only this file plus `MUSE-REPORT-409.md`.
Method: read the two accepted modules line by line against the actual
goal-leg definitions in `grammatik/Grammatik/Zielsatz/Spec.lean`
(`InvTraeger` 1922, `InvZu` 1929, `InvRuheG` 1939, `InvSichtG` 1946,
`SperrWechselG` 1956, `SperrSichtG` 1970, `Ziel` 1983-2000) and against
the consumer claims in `grammatik/OPTIMIZER.md`. Two Lean probes
reproduced below (`.tmp/probe409_a.lean`, `.tmp/probe409_b.lean`,
both `./lean-probe` 0 errors). No Lean file added or changed, no Rust
touched, no friend path touched. This document proves nothing and
closes no chain; it records what the helpers establish, where the
lifetime discipline is prose-only, and what each consumer must still
prove. It does not repeat the bridge-fragment review
(`REVIEW-QUELLE-INVARIANTEN.md`); §6 links to it instead of
re-deriving it.*

## 0. Files actually read (anchors)

- `grammatik/Grammatik/X86/InvariantenOpt.lean` (full, 550 lines).
- `grammatik/Grammatik/X86/AufrufOpt.lean` (full, 288 lines).
- `grammatik/Grammatik/Zielsatz/Spec.lean` 1915-2000 (invariant legs),
  2157-2230 (GX lock-leg variants).
- `grammatik/OPTIMIZER.md` rows C1/C3/S1/I1 (114-115, 212-214, 231,
  363, 496, 658, 935, 950, 1029-1030) — checked for overclaim, §6.
- Consumer check: `grep` over `grammatik/` + `bruecke/` for
  `InvariantenOpt|AufrufOpt|InvScope|slot_read_stabil|exec_pruefung_inv|
  geistPaar|InlinePflicht` finds exactly one hit outside the two
  modules: the umbrella imports in `grammatik/Grammatik.lean` (383,
  387). **There is no in-tree consumer of any helper below.** Every
  "consumer gap" in this audit is therefore a proof obligation on a
  future certificate layer, not a bug in a live call site.

## 1. Verdicts up front

**Correct within their stated claims (no repair to the theorems):**

- V1. `isWahrAll` + `isWahrAll_sound` (InvariantenOpt 46-52, 140-180):
  a genuine soundness lemma over real `eval`. The missing `nicht` arm
  is a documented, correct refusal (completeness would be false).
- V2. `alsLitOpt_lit`, `eval_alsLit`, `litLeBool_sound`,
  `litEqBool_sound` (68-131): genuine bridges from the computable
  checker to `eval`.
- V3. `eval_foldAddLit`, `eval_weiter_n` (192-203): genuine value
  preservation over `eval` (the latter is `rfl`, honestly so).
- V4. `exec_pruefung_wahr`, `exec_ite_wahr` (215-235): genuine
  single-thread elimination with exact trace transfer — the
  condition's `lese` events are retained via the post-read world.
- V5. `exec_pruefung_inv` (261-268): a correct conditional transfer
  lemma — *given* truth `h`, the rewrite preserves `execBlock`.
- V6. `slot_read_stabil` (277-285): a correct conditional equality —
  *given* index stability and slot-content stability, the re-read
  agrees.
- V7. `geistPaar_laenge`, `geistRekon_folge[_grund]`,
  `rufSchrittG_logSchritt`, `rufAt_ok_vorOk` (AufrufOpt 40-42, 57-84,
  99-113, 149-174): all correct; §4 grades their strength.
- V8. Witnesses: `wit_elim`/`wit_step` (InvOpt 410-423) run a
  table-writing program with a memory-changing step (`slots () 0 ()`
  reads `5`); `geistRekon_zeuge` (AufrufOpt 191-253) exhibits ghost
  pair + contract value + memory change + order leg on a reached
  5-step run. Both non-degenerate.

**Gaps that are prose-only discipline, not proved facts (prioritised
in §5):** the `InvScope` tag discharges nothing (F1); the
atomics/MMIO/shared-memory refusals on `slot_read_stabil` live only
in its doc comment, not its statement (F2); there is no
write-invalidation lemma (F3); there is no effect-derived rewrite
permission — no lemma derives a rewrite from a footprint (F4); the
reason channel has ghost form but no inline obligation (F5); the
reconstruction lemmas repackage their conclusions' fields as premises
(F6, strength grading, not a bug). None of these is a false theorem;
each is a place where a future consumer that reads the prose as a
guarantee would be unsound. The CUTS blocks of both files (InvOpt
517-539, AufrufOpt 255-279) already mark the cost/call-log/fault/
concurrency/TSO halves OPEN — this audit endorses those markings and
adds the six items the CUTS do not state sharply.

## 2. Holder / quiescent / entry / exit: what evidence exists at each site

| Site | Goal leg | What the modules provide |
|---|---|---|
| Function entry | `preExpr` ranges (bridge, not here) | Nothing. Neither module imports `Zielsatz` (InvOpt imports: `Semantik` only, line 12). No entry predicate is stated. |
| Return of a writer | `invRueck`/`invGrund` | Nothing. No `InvHaelt`, no `schuldet`, no `InvTraeger` appears in either file. |
| Quiescent machine | `invRuhe` (`InvZu`: no unfinished thread inside a writer) | Nothing but a name: `InvScope.ruhe` (InvOpt 250-253) cites `invRuhe`/`InvRuheG` in prose. No formal link — see F1. |
| Holder observation | `invSicht` (holder + no writer frame) | Same: `InvScope.sicht` is a name with prose. |
| Lock move | `sperrWechsel`/`sperrSicht` | Same: `InvScope.wechsel` is a name with prose. |
| Inside a running writer / held section | NOT CLAIMED (Spec 1383-1391) | Correctly provided nowhere; both files' CUTS refuse these sites. |

Net: **the modules contain zero invariant facts** — no invariant is
stated, let alone proved, about any program. What they contain is
(i) a computable truth checker with soundness, (ii) pure value
rewrites, (iii) two elimination transfer lemmas parametrised by an
*assumed* truth `h`, and (iv) a stability-gated load rule
parametrised by *assumed* stability. A reader who expects
"invariant evidence" from a file named `InvariantenOpt` should reset
that expectation: the invariant content is exactly one hypothesis
`h` plus one decorative tag `s`.

## 3. Findings on `InvariantenOpt`

**F1 (sharpest): the `InvScope` tag is proof-irrelevant.**
`exec_pruefung_inv` (261-268) takes `(s : InvScope)` and proves the
conclusion by `cases s <;> simp [execBlock, h]` — the tag contributes
nothing; the work is done entirely by `h`. Any caller can discharge
any scope with the same `h`. The doc comment (255-260) says "the
elimination proof consumes it by cases — a use without a named scope
does not typecheck", which is true only in the syntactic sense that
the argument must be supplied. Semantically the scope discharge
(which leg, at which program point, with `InvTraeger` + `InvZu` /
holder evidence) is entirely OPEN, as the file's own CUTS admits
(529-530). A certificate layer that treats "tag present" as "leg
discharged" would accept an `invRuhe` justification inside a running
writer. Priority P0 repair is on the consumer side (§5, R1), not on
this theorem — but the comment should stop saying the proof
"consumes" the tag.

**F2: the stability rule's carrier restrictions are prose-only.**
`slot_read_stabil` (277-285) quantifies over *any* `t : D.Tab`,
`f : D.Feld t`. Reproduced type (probe B `#check` output):

```
slot_read_stabil : ... →
  (eval σ₀ i σ' ρ').n = (eval σ₀ i σ ρ).n →
  σ'.slots t (eval σ₀ i σ ρ).n f = σ.slots t (eval σ₀ i σ ρ).n f →
  eval σ₀ (Expr.slot t f i hL) σ' ρ' = eval σ₀ (Expr.slot t f i hL) σ ρ
```

The doc comment (270-276) says "never across publication, fences or
acquire/release edges, and never for atomics, MMIO or
foreign-observable memory" — none of which appears in the statement.
Under GX, shared-atomic reads are answered by the weak memory, so the
`hinhalt` premise about `World.slots` is not even the right
stability notion for atomics; and for MMIO `slots` equality is
meaningless. The theorem is true as stated (it is a pure equality
conditional); the hazard is a consumer applying it to a shared atomic
or MMIO read while citing the file as authority. Priority P1 (§5,
R2): either restrict the statement or give the consumer a decided
refusal predicate; at minimum the comment must say the restriction
is unenforced.

**F3: invalidation by writes or foreign transitions has no lemma.**
There is no theorem of the shape "a store to `(t, n, f)` (or a step
of another thread, a fence, a release/acquire edge) discharges
`hinhalt`". The only inhabitation, `slot_read_stabil_zeuge`
(505-515), uses the *same world twice* (`σ' := σ`, stability by
`rfl`) — the degenerate case the gate permits but which exhibits no
real reuse across a program step. The file is honest that the
stability premise is "the EXPLICIT separate obligation" (278-279);
what is missing is any positive example of discharging it across a
write to a *different* carrier (the ownership/disjointness case) or
any refusal lemma for a write to the *same* carrier. Priority P1
(§5, R3).

**F4: no effect-derived rewrite permission exists.**
The task asks about "effect-derived rewrite permissions"; the
answer is that the module has none. `foldAddLit`/`eval_weiter_n`
derive from literal values, not from write sets; nothing in the file
reads `schreibt`, `haelt`, `darf`, footprints, extents, or lock
coverage to permit a rewrite. The ownership / held-lock / immutability
discharges named in the `slot_read_stabil` comment have no
corresponding definitions. This is legitimately incomplete (the
exports do not exist yet — cf. REVIEW-QUELLE-INVARIANTEN §8), not a
bug. Priority P2 (§5, R5): book as a dependency on the effect-export
work, do not grow ad-hoc footprint premises here.

**F5 (minor): observation retention is exact but single-threaded.**
V4 keeps the condition's `lese` events — good. But there is no
statement about the *removed* branch's observations under
concurrency (the refused `else` may contain token ops whose removal
changes interleavings), no fault transfer beyond unreachability, no
cost transfer. All marked OPEN in CUTS (532-538); endorsed, no
action except keeping the markings when the certificate layer is
built (R6).

## 4. Findings on `AufrufOpt`

**F6 (strength grading, not a bug): the order lemmas are
repackagings.** `geistRekon_folge` (57-69) concludes
`FolgeLog Φ (rueck :: eintritt :: rest)` from `hrest : FolgeLog Φ
rest` plus `hord1`, `hord2` which are *literally the two new fields*
of the conclusion structure. The proof is the constructor
`⟨hord2, hord1, hrest⟩`. Correct, and the file never claims more —
but a consumer still has to prove the armed side conditions
(`Pflichtig`/`Armiert` over the extended log) per instance, which is
the actual work. The joint witness (§1, V8) does discharge them once
(on `Φ50` with value `true`), so the conditions are not vacuous.
No repair to the lemma; the certificate layer must not treat
"ghost pair spliced" as "order preserved" without the armed checks
(§5, R4).

**F7: only the entry duty is derived; the return duty is carried.**
`rufAt_ok_vorOk` (149-174) genuinely extracts `vorOk` (requires over
actual `ρ`) from a successful `rufAt`. `InlinePflicht.nachOk`
(139-144, ensures over the actual result between entry/return
worlds) has no such derivation — the CUTS block says so explicitly
(263-266). Endorsed as honest. Consequence: no inlining certificate
can be closed today even for direct calls (R4).

**F8: the reason channel has ghost form but no obligation form.**
`geistPaar`/`geistRekon_folge_grund` cover `grund`, yet
`InlinePflicht` demands `hr : D.gruende g = 0` (129) — inlining a
function that can return through a reason has no stated duty at all.
Since the struct already refuses that case, this is a completeness
gap rather than unsoundness, but any I1 consumer that splices a
`grund` ghost pair for a fallible callee cites a lemma with no
matching obligation. Priority P2 (§5, R4).

**F9: genuine contributions to keep.** `rufSchrittG_logSchritt`
(99-113) is a real classification over all `RufSchrittG` rules:
silent steps contribute no log event, so an inlined body needs
exactly the ghost pair — this correctly bounds the reconstruction
obligation. `InlinePflicht.hp` carries the *same* `RufPasst`
lock/resource discipline the call would have needed (128), and the
contract fields are over actual `rho`/`val`/`s0`/`s1`, not
quantified away (130-144) — both are the right shape against the
HARD-RULES failure modes. The `callInd`/`bindCallInd` exclusion is
marked OPEN (273); endorsed.

## 5. Prioritised repair / bridge tasks (consumer side unless noted)

- **R1 (P0): scope-discharge rule.** A certificate-layer theorem that
  takes `(s : InvScope)` *plus* the matching leg evidence —
  `InvTraeger` + `InvZu` + `InvHaelt` at `M0` for `ruhe`;
  holder-lock + no-writer-frame for `sicht`; the acquiring/releasing
  step shape for `wechsel` — at the exact use-site machine, and
  yields the `h` that `exec_pruefung_inv` needs. Until it exists,
  every invariant-derived elimination is refused (on the bridged
  fragment this coincides with REVIEW-QUELLE-INVARIANTEN §5: `S =
  leer` means there is nothing to discharge). Companion fix in this
  file's comment (F1): reword "consumes it by cases" to "records the
  claimed scope; discharge is the certificate layer's".
- **R2 (P1): enforce or export the carrier refusal for load reuse.**
  Either a decided predicate `darfWiederverwenden t f` (refusing
  shared/atomics/MMIO/foreign-observable carriers) that the reuse
  rule takes as a premise, or a statement-level restriction of
  `slot_read_stabil`. F2 is the audit's one case where prose is
  currently citable as licence.
- **R3 (P1): invalidation lemmas.** At least: same-carrier store
  kills `hinhalt` (refusal direction), and different-carrier store
  preserves it (permission direction, needing the footprint/
  disjointness export of F4/R5); plus the concurrent-step version
  over `RufSchrittG` (another thread's write kills stability unless
  the holder discipline of `SperrSichtG` is exhibited). A
  non-degenerate `_zeuge` must show reuse across a real step, not
  `σ' = σ`.
- **R4 (P1): close the inline obligation.** Derive `nachOk` from a
  successful `rufAt` (mirror of `rufAt_ok_vorOk`); state the
  fallible-callee obligation (F8) or keep refusing it by `hr`;
  prove the armed side-condition discharge generically (beyond the
  single `Φ50` witness) before any I1 consumer claims order
  preservation.
- **R5 (P2): effect exports first, rewrite permissions after.**
  `writes`/`haelt`/floor per-site exports from `UProg`/`P` as Lean
  computations (REVIEW-QUELLE-INVARIANTEN §8 owners); only then
  derive rewrite permissions from them. No ad-hoc footprint premise
  should be added to these two modules in the meantime.
- **R6 (standing): keep the OPEN markings attached.** Cost/call-log/
  fault/interleaving/TSO halves are marked OPEN in both CUTS blocks;
  the certificate layer and OPTIMIZER rows that cite these helpers
  must carry the same markings until R1-R5 land (verified: OPTIMIZER
  C1/C3/S1 say ACCEPTED-HELPER only for the truth-checker direction,
  I1 says PROPOSED — no overclaim found).

## 6. Non-duplication note and claim ledger

Source-side evidence on the bridged fragment (entry-only ranges,
whole-function write sets, vacuous `S = leer` invariants, absent
SCFG exports) is reviewed in REVIEW-QUELLE-INVARIANTEN §§2/5/8 and
is not re-derived here. This audit's distinct contribution is the
implementation-level reading: the two accepted modules contain no
invariant facts and no effect facts, their tags and carrier
restrictions are unenforced, and their reconstruction lemmas push
the real obligations (scope discharge, stability discharge, armed
order conditions, return duty) to a certificate layer that does not
exist yet.

May be said: §1 verdicts V1-V8 with the cited lines; F1-F9 with the
cited lines and the two reproduced probes; the no-consumer grep
result (§0); R1-R6 as prioritised follow-ups.
May NOT be said: that any invariant-derived optimisation is
justified today; that any scope, stability, or order obligation is
discharged beyond the single witnessed instances; that any helper
covers atomics, MMIO, foreign-observable memory, concurrency,
cost, faults beyond unreachability, or target bytes; that the
OPTIMIZER rows citing these helpers are closed (they say helper /
proposed, and so do we).

*CUTS: docs-only audit. No Lean theorem proved or checked by build;
mechanical checks are the §0 grep (one in-tree hit: umbrella
imports only) and the two `./lean-probe` runs below, both 0 errors.
All definition claims are by reading the cited lines; line drift
after this commit invalidates the anchors. Follow-up belongs to the
certificate-layer owner per R1-R6; this audit pre-empts no proof.*
