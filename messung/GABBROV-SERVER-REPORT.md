# GabbroV server report — the user's logic proofs over the Lean model (2026-09-29)

Lane `gabbrov` (`ubuntu@simon.jocraft.cc`, tree `~/gabbro-v`, branch `lane/gabbrov`). Scope as
corrected by Simon on 2026-09-29 16:00: the CHANNEL for any Gabbro program, nothing of the
firewall. Every number below was measured in this tree; the command stands beside it.
**Isabelle is not installed on this machine, so `abnahme.py --voll` was NOT run.**

## 1. V1 — the pipeline is honest and usable end to end

| gate | what it catches | probe | measured |
|---|---|---|---|
| fail-closed `gabbro prove` | a Lean that did not run (no toolchain, no receipt) | `crates/gabbro-cli/tests/beweismessung.rs` (3 cases, network lane) | `cargo test --no-fail-fast`: 1440 passed, 0 failed |
| the axiom gate file | a `sorry`, an `axiom`, `native_decide`, a proof of another statement, a renamed theorem, a missing file, a broken toolchain, `emit --proved` with a red proof | `instrumente/pruefe-beweis-tor.sh` (10 probes) | `poison probes not caught: 0` |
| the heartbeat budget | a proof file that starts from Lean's default 200 000 and dies in `gabbro_pipeline` on any sizeable call chain (found on `beispiele/126`) | `gabbro prove --template` now writes `set_option maxHeartbeats 11300000` | template of 126 compiles to the goals, not to a timeout |

**Testbed moved.** The gate script's testbed, `beispiele/121`, was CLOSED BY THE GENERATOR by this
session's changes (§3) and no longer owed a proof — the poison probes then reported GREEN for every
poison, which is the right verdict for a unit that owes nothing and the wrong testbed. The script
now uses `messung/proben/probe-tagged-wird-gebaut.gab`, whose one duty the generator does not close.
`Proofs/Duty121TaggedStaticInit.lean` (a hand proof of a statement nobody owes any more) was deleted.

**Time per unit** (`.claude/muse-arbeit/kratz/v/messe.sh`, one `gabbro prove` per corpus file, 219
files): 1233 s before the second pass of §3.3, 1547 s after (including one new file); the slowest
units are `beispiele/55` (190 s), `F01` (160 s) and `01` (87 s). `gabbro_pipeline` is the cost: a duty file with sixty-odd
`simp`s (the firewall unit that started this lane) takes six minutes — not in the corpus.

## 2. V2 — the corpus units that owe duties

`gabbro prove` over `beispiele/`, `messung/fragmente|caprock|proben/probe-*|netz/*` (219 files, 14 owe
nothing): **192 GREEN, 13 OWED (12 real + the poison probe of §3.1 that must stay OWED), 0 RED** at the end of this session (start of the lane: 182 / 22;
start of this session: 188 / 16). Of the 192, **188 are closed by the generator alone** and **4 carry a
hand proof** (`120`, `124`, `151`, `probe-tagged-wird-gebaut`).

| unit | before | now | how |
|---|---|---|---|
| `beispiele/56-auftragsring` | OWED | GREEN | **specification fixed**: `einreihen` promised distinct orders without requiring `i` to be new (`forall j in queue r : r.plaetze[j] != i`); the duty said so, the obligation is untouched |
| `beispiele/157-worker-pool` | OWED | GREEN | the lock invariant (§3.1), by the generator |
| `beispiele/124-two-threads-private` | OWED | GREEN | the lock invariant (§3.1) + one frame-chain line for `hauptA` |
| `messung/proben/probe-tagged-wird-gebaut` | OWED | GREEN | a person's proof (the tagged-construction closer) |
| `120`, `121`, `151`, `167`, `169`, `96` | OWED | GREEN | earlier this lane (proofs / two generator gaps) |

**The 12 real ones that stay OWED, each with its written reason:**

| unit | owed | reason |
|---|---|---|
| `beispiele/01-tabelle`, `messung/fragmente/F01`, `messung/caprock/kapraum`, `beispiele/55-kindkette` | 4 + 4 + 2 + 1 (F01, kapraum and 09 each lost one duty to the generator this session) | the person's argument: a `reaches`-invariant of a linked structure across a relink (PLAN.md §5.1). **Looked at in `55`, not proved.** (1) The specification of `kind_einhaengen` looks false as written: nothing says `k` is not already a member of another parent's chain, and then `k.elter = Some(p)` breaks that parent's `kind_zeigt_zurueck` (a chain member has `elter == Some(_)`, so `requires c.slots[k].elter == None, k != p` is the natural repair). I did NOT verify the falsity in Lean and reverted the edit of the example: it would add a requires to a unit I cannot close. (2) With the repair, 74 goals remain (`chase` over `store` into the chain field); what is missing is a small library of `chase` lemmas (a store into `naechstes_geschwister` of a node not on the chain leaves the chain; a store into the head prepends), which belongs in `Body.lean` next to `allBelow`/`chase`. Compile of the template: 16 s. |
| `beispiele/09-ohne-zeiger` | 2 | `einsammeln` calls `blatt_loeschen(opfer)`, whose `requires` is `benutzt(opfer)`, for every descendant. What makes a descendant used is "a slot with a parent is used" (the contrapositive of `frei_ohne_elter`) **and** "a descendant has a parent" — the second is nowhere in the source: the `tree { parent … child … sibling … }` declaration would have to supply it. **Specification incomplete, and the fix is a language decision (does `tree` imply parent consistency?), not an edit of the example.** A second, MODEL gap sits under it, the same as in `57`: a loop over `descendants of s by consuming` is modelled with the index in the table's range (`RunsLoopN`), not with "this index is a descendant of `s` in the state of this pass" — so even with the tree invariant, `opfer` could be any slot. The repair is a domain-membership premise in the run assumption (sound for `consuming` and `unvisited`), a change of `Body.lean`'s `RunsLoop*` family and of the exporter; the same premise closes `57`'s "which slot does pass `i` see". Same reason for `01-tabelle` and `messung/caprock/kapraum` (their `einsammeln` is `09`'s). |
| `beispiele/57-faedenhalt` | 1 | `ensures forall t in slots of Faden : zustand != LAEUFT` after `traverse … by unvisited`. The model knows a traversal runs AT MOST `count` passes (`RunsLoopN`) and nothing says it visits EVERY slot, or which slot pass `i` visits; with `passes` alone the invariant "slots below `passes` are stopped" needs `pass i = slot i`. **A model gap** (a visited-set, or "a traversal without `leave` covers the domain") that needs a language surface decision. A `invariant … passes` edit of the example was tried and reverted: it changes nothing without the model. |
| `beispiele/126-vergleichssortierung` | 1 | a sorting network over a function pointer. The specification is too weak (`ordne` promises nothing), and strengthening it (a comparator: ordered pair, others unchanged, pair kept or swapped) makes the pipeline split 94 goals at five minutes per compile, each with a growing context, and the leaves are not linear (the facts about the callee's world are `Value`-level equations, not `Int` ones). Not proved; the strengthened specification was reverted, since it would only have added an owed duty. **Finding: disjunctive callee posts multiply the pipeline's case splits.** |
| `beispiele/147-ftp-alg-control`, `148-ftp-alg-daten` | 1 + 1 | `tick_runde`: 64 sequential calls of `fenster_schritt`; the second pass closes `fnv` (a chain of five) but not this one. Extra passes and raising the round cap of `gabbro_calls` from 12 to 100 change nothing (measured); the calls stay uninstantiated. |
| `beispiele/161-zeichenkette` | 2 | **the duty is false as LOWERED, not as written.** `haenge_an` (`a + b`) and `kleiner` (`a < b`) over `string max N` are exported as `.bin .add` / `.bin .lt` over `.name "a"`, `.name "b"` — names of parameters that have no shape (the model has no string value), so `eval` is `none`, the body is stuck and `∃ s', …` cannot hold. The exporter should REFUSE a string operator with a tag (or the model get a string value); until then two duties are owed that no proof can discharge. Not fixed this session (a new `LeanReason` touches the register, the sentences and their guardians). |
| `messung/fragmente/F06` | 2 | **false as written.** `unberuehrt` returns `i * 8` with `ensures result <= s.len`, and nothing relates the words scanned to `s.len` (`len` may be 0 with a full stack of eichmuster words). `result <= STACK_MAX` would be provable. F06 is one of the kernel excerpts under `messung/fragmente/`, which AGENTS.md treats as frozen (lane 184 was rejected for breaking the F04 excerpt), so the specification is NOT edited here without Simon's word; the reason stands instead. |
| `messung/proben/probe-neun-domaenen` | 5 | the syntax probe's empty bodies with an `ensures` — false as written (PLAN.md §5.1). Specification of a probe, not touched |

## 3. V3 — the plumbing gaps a proof still meets

### 3.1 The lock invariant was neither rely nor guarantee (general; blocked 124 and 157)

`locks L { … }` was transparent in the duty channel (`.locked` = its body), so in
`beispiele/157` `arbeiter` calls `setze` (whose `requires` is the lock invariant) and the invariant
was nowhere to be found: the goals were `False`. The section is now, for a lock that declares an
`invariant`: `.call lock_acquire_L` — an ASSUMED contract (`Contract`/`Frame` in `Assumed`, like
a foreign routine): the protected carriers arrive with the invariant holding; the body;
`.call lock_release_L` — precondition = the invariant, so a body that leaves it false is stuck.
No `Body.lean` change was needed for the encoding (`lean.rs`: `Unit::lock_invs`, the arm
`StmtArt::Sperrt`). **The assumption is new and named**: "the environment hands over the protected
carriers with the invariant holding at every acquire" — it is exactly `HavocOk` of premise (b).
The checker refuses a body that breaks the invariant at the release already (`N511`), so the release
duty is redundant with the checker except where a callee's promise is what the checker read.

Second half of the same gap: after `gabbro_cases` splits on a condition that reads a call's answer
(the acquire's invariant), the failing branch has the goal `False` and NO call in it — the contract
that refutes the condition was never instantiated. `gabbro_calls` now collects the calls of the
`hcase` hypotheses in a `False` goal, and only there.

Measured: corpus 188 GREEN / 16 OWED → 192 / 12, no unit changes the other way.
`instrumente/pruefe-sperre-beweis.sh`: 157 and 124 GREEN; `messung/proben/probe-sperre-bricht-invariante.gab`
(`verlaesst_sich` promises more than the invariant gives) stays OWED. *The probe cannot show a body
that breaks the invariant, because the checker refuses it (N511) before the duties exist.*

### 3.2 `--template` lacked the heartbeat budget — closed (§1).

### 3.3 The second pass (`gabbro_auto2`)

A call chain of five (`147` `fnv`) is deeper than one round of `gabbro_pipeline` instantiates;
the second pass closes it. The generated closer is `gabbro_auto2 [list] [list without hall/hpass]`,
the template spells both passes out. A pass over no goals is free; a unit the first pass closes pays
nothing. No unit changed status (`147` still owes `tick_runde`), but `fnv` is no longer a person's
duty, and `121` closed. Cost: +25 % on the corpus run (the owed units run twice).

### 3.4 Not done

The general gaps from the firewall draft (`~/claude-lane/kratz/v/uncommitted-general-gaps.diff`, ~390
lines: expression arguments in inlined spec-fn calls, `requires` on parameters inside loops, a loop
rule that keeps the parameters) were REVERTED, because no corpus unit or probe demonstrates them
(the rule of the hand-over); the patch is kept outside the tree.

## 4. V5 — the connection to the goal theorem

**Not proved. The gap, exactly.** Premise (b) of `gabbro_ziel` is `NutzerPflicht E` /
`NutzerPflichtA E` over the G model (`Programm D`, `execEndH`, `Umwelt`); the duty files are
`X_meets_statement` over `programmlogik/Gabbro/Body.lean` (`Stmt`, `exec`, `Env`). The two
models are separate Lean projects (`grammatik/` and `programmlogik/`), the exporters that read the
Rust AST into them are separate (`lean_g.rs`, `lean.rs`), and **nothing relates the statements**.
Part by part:

| part of (b) | what the duty files say | covered? |
|---|---|---|
| `KoerperGutS`: the body triple at every budget, with the caller's duty | `meets_statement`: from `requires` (and well-formedness), the body runs to an end and the `ensures` holds at value exits; callee contracts are hypotheses (`Contract`/`Frame`) | in the SEQUENTIAL Body model only; termination is a premise `Runs ρ f body`, not a budget quantifier |
| `InvGutS`/`InvGutGrund`: owed invariants at value AND reason exits | `maintains` invariants are conjuncts of the post; reason exits carry the `result` clause (commit `ed83412c`) | value exits: yes; reason exits: the grounds are declared (`ed83412c`), the invariant at a reason exit was not separately measured |
| `HavocOk` (the lock rely) | the acquire contract of §3.1 | **yes since this session**, for locks with an invariant |
| shared atomics (`NutzerPflichtA`, `LogikPflichtA`: the rely over every value a shared atomic read may return) | `Exchange`/`AwaitLoad` are refused by the exporter | **no** |
| `SperrInvLokal`, `AxEnsLokal` (an invariant/ensures reads only its carriers) | checked by the Rust passes (`N275`/`N276`), not a duty | no duty; not needed |
| `StartPflicht` (lock invariants and start `requires` at the initial memory) | `Initially` is an ASSUMPTION of the duty channel (`Assumed`), never an obligation | **no** — the user proves nothing about the initial memory in this channel |
| `AxVertragO Q` (axiom ensures) | the assumed contracts of foreign routines | assumed, as in (c) |

What a theorem would need: (1) a semantic-preservation statement between `exec` (Body) and
`execEndH` (G) for the fragment the duty files cover — translation validation of the two exporters,
not begun; (2) the missing rows above. **A statement of the form "all duties GREEN ⇒ (b) for the
covered fragment" is therefore not provable today**, and the README's "the user proves only their
logic" remains a sentence about the goal theorem's premise (b), not about the duty files.

## 5. V6 — proof lines per line of user code

`instrumente/miss-beweis-verhaeltnis.py`; the counting rule is in its header (code line: non-empty,
not a `--` comment line; proof line: non-empty, not a comment, not `import/open/set_option/namespace/end`,
not the generated `Duty/` file). Measured at the end of the session:

| unit | source | code | library | duty proof | ratio (all/code) | ratio (duty/code) |
|---|---|--:|--:|--:|--:|--:|
| `Duty120TaggedConstruction` | `beispiele/120-tagged-construction.gab` | 23 | 0 | 21 | 0.91 | 0.91 |
| `Duty124TwoThreadsPrivate` | `beispiele/124-two-threads-private.gab` | 62 | 0 | 8 | 0.13 | 0.13 |
| `Duty151WordPoolDiscipline` | `beispiele/151-word-pool-discipline.gab` | 38 | 0 | 19 | 0.50 | 0.50 |
| `DutyProbeTaggedWirdGebaut` | `messung/proben/probe-tagged-wird-gebaut.gab` | 13 | 0 | 9 | 0.69 | 0.69 |
| **total** | | 136 | 0 | 57 | 0.42 | 0.42 |

**Reading it.** 188 of 192 GREEN units (7404 code lines) needed no proof at all. The 4 units with
a proof are the four where the pipeline leaves something: 57 proof lines against 136 code lines,
**0.42**. The number is not a sample of "what proving costs": the units that would cost the most
(§2: linked-structure invariants, the sorting network) are exactly the ones NOT proved. It says what
the channel costs where it works, and how much of the corpus it works for.

## 6. What is not done

V2 for the 12 owed units above (five of them are the person's linked-structure arguments); the
V5 theorem (needs translation validation between the two models, §4); the disjunction blow-up (`126`);
the 64-call chain (`147`); the `by unvisited` coverage model (`57`); the tree-consistency invariant (`09`).
