# MUSE-REPORT-54 — CSL resource invariant, attempt C (model finding)

Branch: `muse/54`. New file: `grammatik/Grammatik/CSLInvarianteC.lean`
(wired via `import Grammatik.CSLInvarianteC` at the end of
`grammatik/Grammatik.lean`). No existing theorem modified or weakened.

## What was done (reviewer restart procedure, one step per probe)

1. `git show ref-csl:grammatik/Grammatik/CSLInvarianteB.lean > grammatik/Grammatik/CSLInvarianteC.lean`.
2. Renamed the one `B`-suffixed declaration to `csl_ressourceninvarianteC`
   (the only `theorem`/`def` name carrying the suffix; helpers have no
   suffix and do not collide since the B file is not in this tree), plus
   header/CUTS/`#print axioms` references. Added the import.
   Probe: 0 errors, only the 4 known `sorry` warnings. No elaboration
   breaks from master (committed as `a641d05`).
3. Closed sorry #1 (same-carrier `schreibBytes`, old line 358) with a new
   separate lemma stated above the leaf lemma and used at the use site:
   `schreibBytes_gleich_samma_traeger` — case split on the byte list.
   Empty list: `World.schreibBytes` is the identity, slots ride on
   `lese_slots_gleich`. Cons case: `schreibBytes_spur_eq` plus the
   definitional `lese` trace equation give
   `replicate ++ reads = neu` by `List.append_cancel_right`; the head
   event is `zugriff t true`, ruled out by the no-write core.
   After this fix `blatt_slots_t_gleich` is sorry-free
   (committed as `d95a3d1`).
4. Sorry #2 (leaf-case wiring of the main induction) is UNCLOSABLE:
   see Finding below. Per the reviewer procedure I stopped, cut the
   sorry-dependent theorem, listed it in CUTS, and committed no `sorry`
   (committed as `ab18053`).

## Exact names of new/renamed definitions and theorems

- `schreibBytes_gleich_samma_traeger` (NEW in C, green): same-carrier
  byte-write slot preservation from a no-write-event hypothesis.
- `blatt_slots_t_gleich` (ported from B, CLOSED in C): firing non-oracle
  leaf of a thread not holding `L` preserves every slot of the
  `L`-guarded carrier. Axioms: `[propext, Classical.choice, Quot.sound]`.
- `zugriff_darf_aus_gut`, `held_in_Λ_aus_offen` (unused, kept as a named
  utterance of the tie), `kein_schreibzugriff_ohne_sperre`, all frame
  lemmas (`lese_slots_gleich`, `storeSlot_fremd_traeger`,
  `storeSlot_fremd_slot`, `storeSlot_fremd_feld`,
  `storeGlob_slots_gleich`, `schreibBytes_fremd_traeger`): ported green.
- `csl_ressourceninvarianteC`: CUT, not present in the file (see Finding).

## Finding (model finding, not a failure): the target is false for `axiomCall`

Exact constructor: `Stmt.axiomCall` (`grammatik/Grammatik/Syntax.lean`,
fired at `grammatik/Grammatik/Semantik.lean:617-621`).

Mechanism: `axiomCall` answers with the oracle world
(`axiomAntwort O a σ … = (O.wirkt a σ ρ, …)`), which may differ from `σ`
on `t`'s slots while recording NO `zugriff` event at all — the trace may
even be unchanged. `GutO` (`Satz.lean`) constrains the oracle only to the
declared frame (`Rahmen (D.aschreibt a) …`), the held locks, and the
trace — not to the guard. An axiom declared with `D.aschreibt a t = true`
may therefore flip a slot of the `L`-guarded carrier `t` while `L` stays
free everywhere. The main induction's leaf branch owes `hax`
(non-oracle shape) for the fired statement; it is underivable for
`axiomCall`, and slot preservation is genuinely false there — no proof
repair exists without changing the statement.

Premises are jointly satisfiable (so this is falsity, not vacuity):
take a `BlattGegenbeispiel.D1`-shaped declaration plus one lock `L`
with `D.braucht t = [Sum.inl L]`, one axiom with `aerg = none` and
`aschreibt a t = true`, and an oracle that flips one slot while keeping
the spur; run one `PCSchritt.leaf` firing `axiomCall` from `GenStart`
(empty traces, `Λ = []`). Then `hGuard`, `hLokal` (invariant reads one
slot), `hStart`, and `hRelease` (vacuous — no `nimmt` event ever fires,
so `L` is never held) all hold, `L` is free at the reached machine, and
`inv` fails. This sketch is prose, not a formalized counterexample.

## What remains open

1. Rule-12 variant: `csl_ressourceninvarianteC` plus an added no-oracle
   premise (fired leaves are never `axiomCall`), in a separately named
   theorem, with a rule-13 `_zeuge`. The leaf-wiring, same-`L` release
   (`List` erase unfolding), and holder-persistence (`Brav` haelt
   equality) branches are all closable there; only the `axiomCall` shape
   was fatal.
2. Formalizing the prose counterexample above as a proved negation.

## What in the task I believe is wrong

Nothing material. Two notes: (a) the task's suspect list
("`axiomCall`, `uebergang`, `schreibBytes`, register writes") resolves to
exactly one fatal constructor — `axiomCall`. `uebergang`/`schreibBytes`
write through `schreibSlot`/`schreibBytes` and record the guard-carrying
event (closed); register writes never touch table slots (closed by
`rfl`/`lese`). (b) The B report's remark that the §17 characterization
lacks the per-event `haelt` equation is confirmed but harmless here: the
per-shape `rfl` spur equations already fix each event's held list.

## Last build result

`./lean-bau` last line: `Build completed successfully (37 jobs).`
`./lean-probe grammatik/Grammatik/CSLInvarianteC.lean` first line:
`== 0 error(s) in the COMPLETE output` (no `sorry` warnings remain).
