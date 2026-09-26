# Opus agent G — OFFEN O1: the four obligations "the semantics cannot state"

*2026-09-26, branch of Opus agent G (worktree `agent-ade28fb3665aaaee9`), on master `342f6ace`
(Merge Opus F). Everything local; one Lean build at a time through `./lean-bau`/`./lean-probe`,
cargo through `./cargo-pruef`. `free -g` at the start: 31 GB total, 15 GB available; before the
full build 18 GB available.*

## 1. The answer, up front

**OFFEN O1's diagnosis is right for `programmlogik/Gabbro/Body.lean` and wrong for the goal
theorem.** `GabbroZiel` does not stand on the big-step `exec`: its runs are those of machine G
(`RufMaschineG.lean`), which is SMALL-STEP -- every leaf, unfold, push and pop is one step --
and whose threads carry an access trace (`spur`) and a CALL LOG (`log`: `eintritt`, `rueck`,
`grund`, newest first). All four obligations are statable there. What was missing were the
predicates and, for two of them, the claim.

| row | now | where |
|---|---|---|
| **L24** `caller`/`reply_owner` never half set | literal reading FALSE in any small-step semantics (two statements, two steps); its content -- no OTHER thread sees the pair half set -- is CLAIMED by the invariant legs of Opus agent D | `invSicht`, `sperrSicht`, `sperrWechsel` |
| **L34** the invariant fails between the two assignments | an EXISTENCE statement about one program, witnessed; the "wrong-but-existing invariant" of `GABBROV.md` §3 is now REFUSED by the checker | `tabelle_gebrochen`; Rust `N531`, `N532` |
| **L50** flush completed before the reply | CLAIMED by the new leg `folge` of `Ziel` | `FolgeG`, `folgeG_erreichbar`, `folge50_zeuge` |
| **L52** the reply goes out before the service ends | CLAIMED by the same leg | `FolgeG`, `folge52_zeuge` |

## 2. The Spec diff (review target)

**Premises: before = after.** `GabbroZiel` and `GabbroZielVerbund` are textually unchanged
(`Einheit`, `AkzeptiertSpec`, `NutzerPflicht`, `HardwareAnnahmen`, `Laufzeit`,
`SchnittstelleSpec`, `NutzerTeil`).

**Conclusion: `Ziel` gains ONE field**, nothing else changes:

```lean
structure Ziel … where
  …
  zeit : ZeitAb P O passes M
  -- the order of effects (Opus agent G, 2026-09-26, OFFEN O1: L50, L52)
  folge : FolgeG P M
```

with (Folge.lean)

```lean
def FolgeG (P : Programm D) (M : RufMaschineG D) : Prop :=
  ∀ Φ : Folge D, FolgeOk P Φ → ∀ t,
    FolgeLog Φ (M.faeden t).log ∧
    ((M.faeden t).stapel = [] → (M.faeden t).kopf.rest.2.2.2.2.anRueck = true →
      Φ.ende (M.faeden t).kopf.f = true → Armiert Φ (M.faeden t).log = true)
```

* `Folge D` = `vor`, `ruf`, `ende : D.Fn → Bool`, `ind : Nat → Bool`.
* `FolgeLog Φ log`: every event of the log except the oldest (the thread's start entry) that is
  an entry of a `ruf` function or a return (value or reason) of an `ende` function has as its
  DIRECT predecessor a (normal) return of a `vor` function.
* `FolgeOk P Φ`: every body passes a linear scan with one armed bit (`fS`/`fB`/`fE`): a direct
  call of `g` leaves the bit `vor g`; a leaf (assignment, axiom call, register access, binding)
  keeps it; a compound statement, an indirect call and every sub-block start unarmed; a call of a
  `ruf` function (direct, or indirect through a signature in `ind`) and a return of an `ende`
  function demand it. Plus `∀ g, ruf g → ind (D.sig g)` (no entry escapes through a pointer).

**The header** carries the diff as the "order block" (between the linking and the invariant
blocks), the conclusion-definitions list names the new definitions, the NOT CLAIMED list gains
the "order hunk", and the `Ziel` docstring names the fifth group.

**Embedding.** No premise moved, so every previously accepted unit keeps its verdict; `Ziel`
gains a conjunct and loses none, and every earlier leg is proved by the same term in `ziel_aus`
(`Zielsatz/Beweis.lean`, one new line: `folge := folgeG_erreichbar sp init hr`). Hence
`gabbro_ziel_g`, `gabbro_ziel_vor` (the statement of before, verbatim), `gabbro_ziel_verbund` and
every certificate hold unchanged in their old conclusion; the old `Ziel` is a projection of the
new. No Rust exporter change: `gabbro obligations --g` output unchanged, certificates untouched.

**Axioms** (measured with `./lean-probe` over a file printing them):

```
'Gabbro.Grammatik.Zielsatz.gabbro_ziel'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.Zielsatz.gabbro_ziel_verbund' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.Zielsatz.gabbro_ziel_vor'    depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `axiom` or `native_decide` in any new file.

## 3. What carries the leg

`FolgeBeweis.lean`, premise-free: `folgeG_erreichbar (sp) (init) (hr : RufErreichbarG …) :
FolgeG P M`.

* **The thread invariant** `FolgeInvG Φ z`: the head frame's residue passes the check at the bit
  read off the log (`Armiert`); every suspended caller passes it at `vor g` of the callee `g`
  above it (`FolgeStapel`) -- exactly the bit it resumes with when `g` pops; the log is ordered.
* **`folgeInvG_schritt`: every rule of G keeps it** (all 70 constructors of `RufSchrittG`, by
  cases). Head-local steps log nothing and move the residue along the checked text (a leaf
  keeps the bit, `fNach_blatt`; an unfold starts a sub-block unarmed, allowed because the check
  is monotone in the bit, `fB_mono`/`fE_mono`/`fR_mono`; arm selection and `else` blocks keep it,
  `fB_armWahlG`, `fB_grundWahlG`, `fB_alsBlock`). A push logs the callee's entry, which the
  residue demanded armed if the callee is ordered, and suspends the caller at `vor g`. A pop logs
  the head function's return, which the residue demanded armed if it is ordered, and resumes the
  caller at exactly the bit its suspended residue was checked at (a reason return logs `grund`,
  which disarms; the `else` branch was checked unarmed).
* **The finished thread**: a head standing at a return demands the bit (`fR_anRueck`).
* **Not the conjunction**: `folgeLog_nicht_schwach` -- a log with the ordered event and a `vor`
  return both present but not adjacent is not ordered.

## 4. Witnesses (non-degenerate, memory-changing, multi-step)

`FolgeZeuge.lean`, on the sequential fixture `eP` of `ZielOrtEinfadenZeuge.lean`
(`setze`: `konto[0] = 5`; `pruefe`: requires `konto[0] == 5`; `haupt`: `setze(); pruefe();
return`), with `Φ50` (`vor = setze`, `ruf = pruefe`) and `Φ52` (`vor = pruefe`, `ende = haupt`),
both passing the check (`eP_folge50`, `eP_folge52`):

* **`folge50_zeuge`**: a reached machine after four steps (call `setze`, its write of `5` into the
  table the start left at `0`, its return, call `pruefe`) whose newest log event is the entry of
  `pruefe` and the next the return of `setze`; the entry world carries `konto[0] = 5` (by the
  contract leg); the order leg holds there. The ordered event OCCURS.
* **`folge52_zeuge`**: one step further (`pruefe` returns) thread 0 is FINISHED in `haupt`, and by
  the leg its log ends directly behind the return of `pruefe`.
* **`eP2_folge50_falsch`, `folge50_gegen`**: `haupt` with the calls swapped. The check refuses
  it, and a reached run of five steps has an entry of `pruefe` AND a return of `setze` in its
  log -- the conjunction `flush ∧ reply` -- while `FolgeLog` fails. The premise is needed, and
  the conjunction is strictly weaker.

For L24/L34 the witnesses are Opus agent D's (`Zielsatz/InvariantenZeuge.lean`):
`tabelle_gebrochen` (two writes of `privA`, the table invariant false at a reached machine
between them, open there -- L34's shape), `lock_gebrochen_unsichtbar` (a lock invariant broken
inside a section and, by the leg, untouchable by the other thread -- L24's content).

## 5. The Rust side: the site `GABBROV.md` §3 names

`D013` checked that `breaking I` names something and said in its own sentence: *"A `breaking` on
the wrong-but-existing invariant still passes."* Two rules in `kbedingung.rs`, codes from the
reserved block N531-N535, gifts from 1291-1300:

| code | sentence | rule | poison | positive |
|---|---|---|---|---|
| `N531` | `kbedingung.breaking-rests-here` | a `breaking I` block that calls no declared function (and no pointer) and writes no carrier of `I` -- a table `I` stands over, by name or through a parameter pointing at it -- is named for the wrong invariant | `beispiele/gift/1291-breaking-am-falschen-traeger.gab` (example 53 with the name swapped) | examples 53, 55; `tests/breaking_region.rs::n531_richtiger_name_ist_sauber` |
| `N532` | `kbedingung.breaking-blocks-maintainers` | inside `breaking I` no direct call of a function whose `maintains` names `I` (SPRACHE.md §8.3) | `beispiele/gift/1292-breaking-ruft-pflegende.gab` | `tests/breaking_region.rs::n532_pflegende_nach_dem_block_ist_sauber` |

`D013`'s sentence was updated to point at the two. Neither rule is a premise of the goal
theorem (the model ignores the name of `breaking`); both hold the SOURCE to the language
document. `N531` is conservative: any call of a declared function inside the block exempts it
(a callee's writes are not resolved there); `Some(x)` and tag constructors are not calls.
`N532` does not resolve `requires I` as a predicate word nor indirect calls.

## 6. Decisions, and their reasons

1. **Target semantics = machine G, not `Body.lean`.** G is the goal's semantics; `Body.lean`'s
   big-step character carries the Isabelle proofs (`AUFTRAG-GABBROV.md` §9 stop-list). The
   `AUSNAHMEN.md` rows stay -- they are exceptions of GabbroV's fragment -- with a note naming
   their scope.
2. **L24 is read observationally.** The literal reading is vacuous big-step and false
   small-step; the observational one is what the source comment means for everyone but the
   writer, and it is claimed.
3. **L34 is a witness, not a leg.** "Fails inside every `breaking`" is false in general; "fails
   inside this one" is a fact about one program.
4. **The name of `breaking` is not threaded through G.** A marker in the residue changes the rule
   `dannBreaking`, on which every rule-by-rule theorem of the tree cases; the syntactic half of
   §8.3 went to the checker (`N531`, `N532`), the semantic half (restoration at the block's end)
   is named open.
5. **L50/L52 mean "DIRECTLY behind" in the call log.** "Sometime before" is the weakening V1
   warned about; at log granularity "the flush completed before the reply" is "the reply's entry
   stands right behind the flush's normal return".
6. **The check is conservative** (sub-blocks start unarmed; compound statements, indirect calls,
   lock blocks between the two ends are refused for that `Φ`). It never accepts where the claim
   would fail.
7. **`Φ` is quantified inside the leg; no field in `Einheit`.** No premise change, no exporter
   change, no certificate change.
8. **`N531` exempts every block with a call** -- refuse only where the answer is certain.

## 7. What stays open, per obligation (also in the Spec header and OFFEN O1)

* **L24**: for every CERTIFIED program the exporter writes `Inv := Empty` and refuses
  `maintains` (`LG001`), so the table-invariant form reaches no certified program;
  `beispiele/53-zwei-orte.gab`, the L24/L34 site, is UNCERTIFIED (`LG001`, its option-index
  fields). Closing it is exporter work (table invariants and `option index` fields).
* **L34**: the name-bound promises of `breaking` (the region is where `I` rests; the block
  restores `I` at its end) have no subject in G, which unfolds the block without its name;
  restoration is claimed at writer returns. `requires I` as a predicate word is not checked by
  `N532`. Closing: a name layer in G's residue (with the re-proof of every rule-by-rule theorem)
  and a block-level restoration duty in (b).
* **L50**: effects that are not calls of Gabbro functions (axiom or register effects -- if
  Caprock's `reply4` is a foreign call, a wrapper function puts it in the log); orders across a
  compound statement, an indirect call or a lock block (refused, not claimed); the `Φ` a source
  program means is not in `Einheit` (the exporter emits none).
* **L52**: the check is per function, not per return site -- a service with a second return path
  that does not reply is refused for that `Φ`; the path-sensitive form ("the `Stop` arm's
  return") is open.

## 8. Files

* `grammatik/Grammatik/Folge.lean` (definitions), `FolgeBeweis.lean` (the leg), `FolgeZeuge.lean`
  (witnesses), `Zielsatz/Spec.lean` (the diff above), `Zielsatz/Beweis.lean` (one line),
  `Grammatik.lean` (imports).
* `crates/gabbro-check/src/kbedingung.rs` (`N531`, `N532`), `saetze.rs` (two sentences, `D013`'s
  updated), `crates/gabbro-check/tests/breaking_region.rs`, gifts 1291, 1292.
* `dokumente/OFFEN.md` O1, `dokumente/AUSNAHMEN.md` (scope note), `dokumente/SATZKARTE.md` §55,
  `AGENTS.md` (§2 leg list, §7 ledger row).

## 9. Measured

* `./lean-bau`: green, 327 jobs (after the Spec diff).
* `./cargo-pruef`: see the final line of this section, filled in at the end of the run.
