# PORT-SYNTAX.md — port analysis of the `wip/maschine-pflicht-2026-09-11` SYNTAX.md rewrite

**Measured 2026-09-11, worktree `lane-111` (base `58d6b83`). Read-only: no builds, no runs.**

Source: `git diff master...wip/maschine-pflicht-2026-09-11 -- dokumente/SYNTAX.md`
— 824 changed lines (263 insertions, 561 deletions), single WIP commit `85cb4f4`.
The merge-base is `58d6b83`, i.e. current master here, so the diff is exactly that
one commit's edit. All line references below are diff-hunk positions unless noted.

## Why the WIP looks the way it does (per its own commit message)

1. **Stale base, branched on purpose.** Written against the 2026-09-09 night state
   (`52837ae`); against master (`be49250`-era) `Wettlauf.lean` alone is 12+/198-.
   Branched so it would not silently revert two days of master. Consequence: every
   master-side addition of 2026-09-10/11 is absent from the WIP, and shows up in the
   diff as a *deletion*. Those deletions are collateral, not decisions.
2. **Genuine redesign (worth keeping, per the message):** `Maschine.lean`
   (threads started, interleaved over the grammar; W1/W2/W4 derived, W3 stays as the
   scheduler rule), `Pflicht.lean` (obligation register, proven complete),
   `shared` withdrawn (every carrier guarded: `braucht_alle`/`gbraucht_alle`; W5
   gone; W4 restricted to ownership marks), new forms (`forallRange`/`existsRange`,
   `falte`, `behauptung`, `geist`/`ggeist` with G001).
3. **Known unmergeable as is:** removes 17 theories from the `Grammatik.lean` index.
4. **Known reversal:** `Logik.vorzustand` renamed back to `uebergang`, reversing the
   B26 decision recorded at that constructor.

Port rule used below: **KEEP** = port the WIP text onto master; **DROP** = do not
port (master's newer §§19–21 and subsections, or implemented checker/emitter work,
supersede it — this includes *reverting* the WIP's stale-base deletions);
**MERGE** = manual reconciliation needed, neither side applies cleanly.

Global caveat (the WIP says it itself): the guardians never ran on the WIP side
("Not run on 2026-09-09 ... numbers counted by hand"). No count, rule total, or
word total below may be ported as a number — every figure needs a recount on master.

## Section table

| § / site | WIP change class | Verdict | Reason |
|---|---|---|---|
| Preamble: night-pass paragraph («SG-21» withdrawn, «SG-22»–«SG-24» new) | rewritten (new) | KEEP | Genuine design record; additive prose, conflicts with nothing. |
| State table: `161 rules` → `132 + 7`; `221 + 4 Sonderformen` → `226`; formalised row adds Maschine/Pflicht, drops Ziel | rewritten | MERGE | Rule/word counts are hand counts on the stale base (caveat above) — recount on master. The Lean row must *add* Maschine/Pflicht, not drop `Ziel.lean` (master's lowering contract, §18/§21 depend on it). |
| State table: guardian note "Partly run" → "Not run" | rewritten | DROP | True of the WIP workstation, false of master; porting it would un-record master's 09-09 guardian runs. |
| Vocabulary: `assert lemma fold with` new («SG-22»), `ghost` second position («SG-24»), `deadline`/`concurrent` rows gone, `shared` position withdrawn | rewritten | MERGE | KEEP the four new words + ghost move (genuine SG-22/24). DROP the `deadline`/`concurrent` removals: both name implemented, measured work (`1af516a`, `beispiele/71`, K011/K012/N056; lane C W001–W003) the WIP never saw. |
| Keyword arms: 17-of-226, `owner/assert/lemma/fold/with` join the nameable | updated | KEEP | Principle unchanged; recount the 17/209 figures on master (hand-count caveat). |
| §1 `static`: `ghost static` added; `concurrentdecl` gone from `item` | rewritten (part) | MERGE | KEEP `ghost static` (genuine SG-24). DROP the `concurrentdecl` deletion (declared-concurrency implementation postdates the WIP base). |
| §2: `option` («SG-26») and variable-tail («SG-27») comments removed | deleted | MERGE | Do not silently drop: re-anchor the two idiom pointers with a `fold`-era reference instead. |
| §3 subsection "User memory — seventh side and validated copy" | deleted | DROP | Stale-base collateral: the whole TOCTOU/Adressraum work (`c7dcd69`, `messung/TOCTOU-ADRESSRAUM.md`) postdates the WIP base. Master keeps it. |
| §4: `countexpr` replaced by `foldexpr` (`fold…with`, `Expr.falte`) + type-table row | rewritten | MERGE | KEEP `fold` (genuine SG-22, primitive recursion of `spec fn`). DROP the `count` deletion: `count` is implemented in checker and emitter (`D025`, `beispiele/71` lowers, `cc` accepts). Both forms coexist. |
| §5: `range` arm of `domain` («SG-22»), nine-domains prose, price paragraph rewritten, `forallRange` table row | rewritten | KEEP | Additive SG-22 surface; conflicts with nothing on master. |
| §6: `deadline` clause removed, `costs` demoted to emitter-only, `spec fn` may recurse as `fold` | rewritten | MERGE | KEEP `spec`-as-`fold` (genuine). DROP the `deadline` removal and the `costs` demotion: budget-in-the-logic is implemented and measured (`Budget.lean` `runOps_within`, no axioms; `Fristlauf.lean`; `sonde_tick.c`; §18 «SG-22» time split). |
| §7: `assertstmt` (`assert`/`lemma`, `logik (behauptung n)`, manifest entry) + ghost-assignment row | rewritten (new) | KEEP | Genuine SG-22 core; the emitter-drop theorem (`exec_rahmen`) and manifest wiring are additive. |
| §7: `logik vorzustand` → `logik uebergang` (prose, table, §16.1 row) | updated | MERGE | Reverses the recorded B26 decision (WIP message flags it). Manual decision with `PFLICHTEN.md` on the table; do not port silently either way. |
| §7: SG-25 `leave`-value comment removed | deleted | MERGE | Same treatment as §2 SG-26/27: keep the idiom pointer, update it — do not drop silently. |
| §7 subsection "Linear marks at run time: the stand" | deleted | MERGE | The WIP never addresses the stand model; its scheduler paragraph lives in §11. Reconcile stand vs `Maschine.lean` manually — the deletion alone proves nothing. |
| §9: `ghost table`, «SG-21» withdrawn (`braucht_alle`, every carrier guarded), owner-D026 poison note dropped | rewritten | MERGE | KEEP `ghost` (genuine SG-24 + G001). The `shared` withdrawal is the branch's core conflict: KEEPing it as text needs the Lean port (no `geteilt`, 17 theories carried to the new `Deklaration`) per the WIP message's own integration note; DROPping it discards the branch's point. Manual, biggest item. The D026-note drop follows whichever way the producer story goes (master open item still books it). |
| §11: scheduler paragraph (`Maschine.lean`, `faeden_gesittet`, W3-only `kein_wettlauf`) replaces `concurrent` row | rewritten | KEEP | Additive run-model content; the W3-only table edit is the genuine SG-23 claim. Land as an addition, not as a replacement. |
| §11: `concurrentdecl` production + `Nebeneinander`/`GemeinsamerLauf` row deleted | deleted | DROP | Implemented design (lane C `58f943e`, `InterferenzAllgemein.lean` `AllgemeinStabil`) postdates the base. |
| §11 subsections "Per-form atomicity" and "`concurrent`, `effects`, `shared`" | deleted | DROP | Measured 09-10/11 work (three corpus units × two opt levels; `Extraktion.lean` wiring) postdates the base. Master keeps both. |
| §11: awaits-then-act gap sentence trimmed | updated | DROP | Trims a pointer to §16.2 item 10, which the WIP also deletes (collateral on collateral). Keep master's sentence. |
| §15 "does not exist" list: fold/assert/ghost/guard rows | updated | KEEP | Accurate delta of the new surface; rebase onto master's list on port. |
| §16.1 theorem paragraph (Maschine/Pflicht), 13th → 14th row, `behauptung` row, `Pflicht.lean` completeness note | rewritten/updated | KEEP | Genuine §18-linked content; additive except the `uebergang` cell, which follows the MERGE verdict above. |
| §16.1 closing ("no shared carrier without a guard" → "carrier without a guard", ghost-reading row) | updated | KEEP | Follows the SG-21/SG-24 redesign; rebase wording onto master. |
| §16.2 items 1 (W3-only), 3 (devices), 7 (cost/emitter), 8 (parser) | rewritten | MERGE | KEEP the W3-only premise cut (item 1, genuine SG-23). DROP the rest: item 3 discards the proved device order (`ce5d2db`, `Geraet.lean` `kette_ohne_wettlauf`); item 7 discards the implemented budget/deadline split; item 8 discards the parser mapping (`messung/SYNTAX-PARSER-ENTWURF.md`, 161/161). |
| §16.2 items 10, 11, 12 + "Check-then-use register" table | deleted | DROP | All postdate the base (M147 taint/expiry discipline, H018/H102, `Adressraum.lean`). Master keeps them. |
| §16.2 closing ("twelve rows" → "thirteen", W3-only premise) | updated | MERGE | Arithmetic follows the surviving rows; recompute on port after the above verdicts land. |
| §17 corpus moves: unguarded-table refusal, assert/fold/ghost no-site bullets | rewritten | KEEP | Genuine new-surface consequences; recount "to be counted" against the corpus on port. |
| §17: `shared`-H013, `count`, `deadline`/`beispiele/71`, `owner`-D026, SG-25–27 bullets | deleted | DROP | Each names implemented/measured 09-10/11 work (`H013`, `D025`, K011/K012/N056, poison gifts 693–697). Master keeps them. |
| §18 full replacement (fourth version → verification surface 18.1–18.4, `Pflicht.lean`) | rewritten | MERGE | KEEP the manifest content (18.1–18.4) as new subsections — it documents a new file and four new theorems. DROP the *replacement*: the fourth-version table documents implemented work (time split, payload order, counting, first-match/option/tail idioms). Both §18s must coexist; restructure manually. |
| Open items: scheduler/manifest/logic-surface done, ghost-erasure open | updated | KEEP | Genuine night-pass record; rebase onto master's list on port. |
| Open items: K-deadline/D-count green + `beispiele/71`, owner producer, B26 rename note | deleted | DROP | Each records done 09-10/11 work or an open decision the WIP reverses without discussion. Master keeps them. |
| §§19–21 (composition, fault outcomes, producer contract §§21.1–21.7) | deleted | DROP | The entire `e30b046` design (lanes 81–97: `Komposition`/`Fehler`/`Erhaltung`/`Zeugnis` shapes) postdates the base; the WIP never saw it. |
| §18 "Expiry shapes" + `beispiele/71` mention in §17 intro | deleted | DROP | Same class: `Fristlauf.lean`/sample-probe work postdates the base. |

## Port order (cheapest genuine content first)

1. Additive prose with no conflicts: preamble paragraph, §5 range surface, §7
   `assert`/`behauptung`, §15 list, §16.1 additions, §17 new bullets, open-item
   additions, §18.1–18.4 as new subsections alongside the fourth-version table.
2. Recounts on master (never port a WIP figure): State-table rules/words, keyword
   arms, §17 "to be counted" bullets.
3. Manual reconciliations: `shared` withdrawal vs `Geteilt.lean`/`Extraktion.lean`
   (needs the Lean port, not a text port); stand vs scheduler; `vorzustand` vs
   `uebergang` (B26); `count` + `fold` coexistence; `deadline`/`costs` staying
   logic-side; §16.2 item rewrites; §16.2 closing arithmetic.
4. Explicitly not ported: §§19–21 deletion, §3 user memory, §11 subsections,
   check-then-use register, items 10–12, `beispiele/71` and poison-gift bullets,
   guardian "Not run" note.

## What this analysis did NOT do

No builds, no guardian runs, no Lean. The WIP's hand counts were not rechecked and
must not be quoted as measurements. The `shared`-withdrawal verdict is a text-port
verdict only — the real decision is the Lean integration the WIP message sketches
(port the core with no `geteilt`, carry the 17 theories, or port Maschine/Pflicht
onto master's core).
