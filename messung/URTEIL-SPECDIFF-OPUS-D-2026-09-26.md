# Verdict — the Spec diff of Opus agent D (invariants beyond the returns, `N496`)

*Independent adversarial review, 2026-09-26. Branch `worktree-agent-a2927f48bcf280903`, commits
`61da807a` (Rust `N496`, gifts 1231–1234), `65a5b1b0` (Lean legs), `37b96297` (records) on base
`38777111`; report `messung/OPUS-D-INVARIANTEN.md`. Measured in the worktree through the queued
wrappers only (`./lean-bau`, `./lean-probe`). One text fix committed separately (`f9c29c15`,
Spec.lean header). Nothing merged into master, nothing pushed.*

## 0. Verdicts at a glance

| Change | Verdict |
|---|---|
| Premises of `GabbroZiel` | **unchanged** — the diff of `Spec.lean` removes only three comment lines and the `Ziel` docstring; `Einheit`, `AkzeptiertSpec`, `NutzerPflicht`, `HardwareAnnahmen`, `Laufzeit`, `GabbroZiel` are byte-identical |
| Old `Ziel`/`ZielF` a projection of the new | **yes** — fields only added; `ziel_aus`/`zielF_aus` prove every old field by the same term (`mainAt M hr` is the old `main`) |
| Leg `sperrSicht` | **SOUND, contentful** — stronger than `RennfreiBis` (below) |
| Leg `sperrWechsel` | **SOUND** — a corollary of `sperrInv` at `M` and `M'` plus exclusivity; little new content, honestly stated |
| Leg `invRuhe` | **SOUND, OVERCLAIMED in wording** ("at every entry") — reach much narrower than the header suggested (F1); fixed in `f9c29c15` |
| Leg `invSicht` | **SOUND but NOMINAL** — in the model it says nothing `invRuhe` does not (F2); now stated in the header |
| `ZielF.spawnSicht` | **SOUND** — a repackaging (`K'.m = K.m`, then `sperrInv`/`invRuhe` at `K.m`) |
| Header "WHAT A GREEN BUILD COVERS" and `Inv := Empty` | **missing there** (it stood only in the invariant block) — added in `f9c29c15` (F3) |
| Witnesses (`InvariantenZeuge.lean`) | **SOUND** — real multi-step runs, the broken state computed, the legs applied through the same lemmas `ziel_aus` uses |
| `N496` (Rust) | **SOUND** — sentence, four gifts, positive probe; exemption for `table … ops` named |
| Example 09 rewrite | **a legitimate correction, not a weakening** (§4) |
| Agent's open claim "a guarded table invariant is never written in the model" | **confirmed by argument at the declaration level, not proved in Lean** (§5) |

**Safe to merge: yes** (with `f9c29c15`). No Lean soundness gap was found.

## 1. Build and axiom evidence (measured, before the merge)

| Measurement | Result |
|---|---|
| `./lean-bau` | **exit 0, 0 error lines in the complete output, 318 jobs** (`free -g`: 13 GB available) |
| `#print axioms gabbro_ziel` (via `./lean-probe`, `import Grammatik`) | **`[propext, Classical.choice, Quot.sound]`** |
| the same for `invRuhe_erreichbar`, `inv_erwerb_und_eintritt`, `lock_gebrochen_unsichtbar` | the same three |
| `sorry` / `admit` / `native_decide` / `axiom` in `Invarianten.lean`, `InvariantenZeuge.lean` | **none** (grep exit 1) |

## 2. The legs, one by one

**`invRuhe`.** Hypotheses: `InvTraeger` (the predicate reads only declared carriers), the invariant
at `M0`'s memory (the start memory `sp` of `GabbroZiel`), and `InvZu M i`. The start hypothesis is
neither trivially true nor trivially false: it is a closed Boolean over the start memory,
decidable per unit, and the witness discharges it by `rfl`. Declaring it a hypothesis of the leg
rather than a (b) duty is honestly argued in the header (a (b) duty would drop programs the old
legs covered) and named in NOT CLAIMED ("one that is false in the start memory"). Fine.

**`invSicht`.** See F2: nominal in the model.

**`sperrWechsel`.** The acquire half is `sperrInv` at `M` (the lock is free for everyone by
exclusivity at `M'`) plus "an acquire moves no protected carrier" (`schritt_traeger`); the release
half is `sperrInv` at `M'`. So it adds little beyond `sperrInv`; the header's phrasing ("every
acquire really starts from it, every release really leaves it") is accurate.

**`sperrSicht`.** Two halves: (i) every access (read, write or change) to a carrier `c ∈ S.orte L`
is by a thread holding `L` (`zugriff_haelt`); (ii) while `t` holds `L`, no other thread's step
changes `c` (`relyG`). Against `RennfreiBis`: that leg only orders CONFLICTING pairs of accesses
by different threads, by SOME guard `L` of `c`. `sperrSicht` names the lock of the lock invariant,
covers single accesses and reads, and is false for a program that touches `c` outside `L` even
without a racing partner. Contentful. Both halves are pre-existing lemmas, now in the statement.

**`spawnSicht`.** `faden_spawn_m` (a spawn is `start`/`kind`, which keep `K.m`), then the fields of
`hG`. Correct and cheap; its content is `invRuhe`/`sperrInv` at that machine.

## 3. Findings, ranked

### F1 — MEDIUM: `invRuhe`'s "at every entry" reaches much less than it reads

`schuldet f i` is `(D.traeger i).any (D.schreibt f)` over the SIGNATURE write set, and
`RufPasst.hw` makes every callee's writes its caller's. So every frame below a writer — down to
the thread's start function — is itself a writer. A thread that ever writes a carrier of `i` has
`i` open (`¬ InvZu`) for its entire life, dormant slots included (their frames are in `K.m`).
Hence `invRuhe` says: the invariant holds at the start, and at every machine where every thread
that writes it has FINISHED (or in a program where no running thread writes it). The witness
shows exactly this shape — `privA`'s only writer is `hauptA`, thread 0's start, and the leg is
applied only after thread 0 finished. "In particular at every entry reached outside every writer"
is true, but the entries it covers are those of threads that never write `i`, after the writers
are done. Beyond the old legs this adds the frame argument (nothing else moves the carriers
between the last writer's end and `M`) — real, but modest. **Fixed in `f9c29c15`**: the header's
AT ENTRY paragraph now says so.

### F2 — MEDIUM: `invSicht` is nominal in the model

Its hypothesis requires `t` to hold a guard `L` of a carrier of `i`. By the declaration field
`invarianten_gehalten` (pre-existing), every function that writes a carrier of `i` holds every
guard of every carrier BY SIGNATURE (`L ∈ (sig f).haelt`). Every start is lock-free
(`wurzeln : D.haelt w = []`; `Ruhig` starts write no carrier at all). With `RufPasst.hw`, a
reachable writer frame would make its thread's start a writer, which would then need `L` in an
empty `haelt`. So an invariant with a guarded carrier has no reachable writer (§5), is frozen at
its start value, and `InvZu` holds for it everywhere: `invSicht` follows from `invRuhe` without
its lock hypothesis. Not unsound, not vacuous (the conclusion is not trivial), but it does not
describe "a lock-protected table invariant that writers break and restore" — no accepted model
program has one. **Fixed in `f9c29c15`** (header sentence); the report's "invSicht: a thread
holding a guard sees `i` intact, whatever the others do" should be read with it.

### F3 — LOW: `Inv := Empty` was not in "WHAT A GREEN BUILD COVERS"

The exporter writes `Inv := Empty` and refuses `maintains` (`LG001`), so for all 23 certified
programs `invRuhe`/`invSicht` are vacuous. The invariant block and the report said it; the
section that says per real program what a green build covers did not. **Fixed in `f9c29c15`**.
The residue (table invariants in the exporter) is in TODO.

### F4 — LOW: `sperrWechsel` and `spawnSicht` are corollaries

Both follow in a few lines from `sperrInv`/`invRuhe` and exclusivity. The header does not claim
more; recorded so that nobody counts them as independent guarantees.

## 4. Example 09 — plain judgement for Simon

**The rewrite is a legitimate correction of a false invariant, not a weakening to make `N496`
pass.** The old predicate, `forall s : Kappenraum.slots[s].benutzt` ("every slot is in use"),
was false at the zeroed start table and is falsified on purpose by `blatt_loeschen`, whose own
`ensures` is `!benutzt`. It guaranteed nothing because it was never true; it was accepted only
because nobody owed it — O11 exactly. Its NAME, `wurzel_ohne_vorgaenger`, comes from the Caprock
fragment F01 (`parent == None => prev_sibling == None`), which 09's slot cannot state (it has no
`prev_sibling`); the 09 predicate was a placeholder that did not match its name. The replacement
`frei_ohne_elter` (`!benutzt => elter == None`) is kept by `blatt_loeschen` (it clears both
fields together) and by `einsammeln` (only through `blatt_loeschen`), and plausibly by the zeroed
start. Nothing in the tree depended on the old invariant (grep: no other user in `beispiele/`).
What is lost is not a guarantee but a name: F01's intent is not restored in 09 — that stays with
`beispiele/01` and F01, which carry the original predicate. The `maintains` duty the rewrite
books is an `E` obligation; the Rust checker does not prove it (as the sentence's `vorbehalt`
says). Example 17's added `maintains` is a pure booking; its body was not changed.

## 5. The agent's open claim: guarded table invariants are never written in the model

Checked at the level of the declaration and the call typing (not proved in Lean):

1. `Deklaration.invarianten_gehalten`: `(traeger i).any (sigNr n).schreibt → ∀ t ∈ traeger i,
   ∀ L, inl L ∈ braucht t → L ∈ (sigNr n).haelt` — guards held BY SIGNATURE;
2. `RufPasst.hw`: a callee's `schreibt` is contained in the caller's contract;
3. `AkzeptiertSpec.wurzeln`: every declared start has `haelt = []`; `Ruhig` starts reach no
   carrier writer; `Laufzeit` admits no other start.

A reachable frame writing a guarded carrier would, by 2 along its stack, make the start a writer,
and by 1 the start would hold `L` by signature, contradicting 3. **So the claim holds, provided
every way a frame is pushed goes through a call typed by `RufPasst`** (direct calls, fn-pointer
calls, `traverse` bodies, spawns) — the one point I did not trace through the 70 rules. The Rust
checker is the other way round: `U003` (gruppe.rs) counts `locks` in the BODY, and explicitly
does not count `requires Held(X)`. Example 09 itself (`blatt_loeschen` writes the KAPPEN-guarded
`Kappenraum` with `locks KAPPEN`) is a Rust-accepted program of the kind the model's accepted
class cannot contain. This is a coverage gap between the checkers, not a soundness gap of the
goal. **Recommended follow-up (OFFEN/TODO):** prove `inv_bewacht_eingefroren` in Lean, and then
either relax `invarianten_gehalten` to "held at every write" (then `invSicht` gains content) or
record that guarded table invariants must be lock invariants in the model.

## 6. `N496`

`invarianten_buchen` (m1.rs) refuses a bodied function whose declared `effects` (or derived hull)
write, publish or consume a carrier of a `table`/`group` invariant without `maintains`.
Sentence `m1.invariante_gebucht` with a `vorbehalt` that says the rule books the duty and does not
discharge it. Gifts 1231–1234 cover table, group carrier, `consumes`, and write-through-callee;
`tests/invarianten_buchung.rs` pins both directions over snippets. The `table … ops` exemption is
named in the sentence and in OFFEN O11 (codes N497–N500 and gifts 1235–1240 reserved). The corpus
diff (four files) matches what I see in the branch diff. The rule tightens (no guarantee is
weakened): it only adds a refusal.
