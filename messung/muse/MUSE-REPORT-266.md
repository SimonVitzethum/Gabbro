# MUSE-REPORT-266 — close OFFEN O2, O4, O5, O6 (GABBROV methodology)

Lane 266, 2026-09-26. All four entries CLOSED with decisions; every decision
sits in `dokumente/OFFEN.md` (ledger) with its evidence, per the SCOPE RULE
(Simon, 2026-09-26). No Rust/Lean change; no new diagnostic code (reserved
N536–N540 unused), no gift (1301–1310 unused), MARKE_EMIT untouched.

## What was done

**O2 — G1/G5 WITHDRAWN, not thresholded (committed BEFORE any new measurement).**
Setting a number with 55 of 63 on the table would be R2. Replacements, written
2026-09-03 before the runs they judge: G1 → E1 (`|manifest lines − verdict
lines| = 0`, every run, mechanised in `gabbrov pruefe`) + E2 (every undecided
row by name in AUSNAHMEN.md, exactly 4 rows; growth without HISTORIE.md entry
fails the guardian); G5 → V2a vacuity (built) + V2b milestone (8/8 assumptions
as formal Props with a model; until then the question is not asked).

**O4 — decided as guard PLUS new home; `F01.gab` rewritten accordingly.**
`cdt_wohlgeformt` is now `forall s in slots of c : c.slots[s].used =>
c.slots[s] reaches WURZEL via parent` (no new domain: `=>` is already `pred`,
same shape as `wurzel_ohne_vorgaenger`). `unlink` drops `maintains`
(its post-state is the legitimate transient: used, detached), `delete_leaf`
and `revoke` keep it, `release_slot` gains it. The two changed excerpt lines
stand booked in `pruefe-emission.sh` (`F1_WEG`) with reasons in the file head.
New evidence: `messung/gabbrov/erzeuge-L05used.py` + `L05d`–`L05i.smt2`
(bound 8, Z3 4.16.0): L05d sat 0.03 s (livable), L05e unsat 0.02 s (not
vacuous), L05f sat 0.04 s (unlink refuted — why it drops the claim), L05g sat
0.17 s (`delete_leaf` needs sibling consistency — dangling-parent model),
L05h unsat 0.02 s (`release_slot` holds), L05i unsat 0.02 s (holds with the
no-dangling premise). `revoke` inherits the condition compositionally
(traverse not encoded — remaining step, see CUTS below).

**O5 — «B14» is a fourth demand, of a SECOND kind (DEMAND G1).** The three
recorded demands are Lean-side expressiveness; G1 is premise supply — what the
GABBRO side must DECLARE (added to the `GABBROV.md` §7 table). Re-measured:
L01 sat 0.053 s / L01b unsat 0.038 s / L01c sat 0.055 s, plus the second row
where the family is load-bearing (L05g sat → L05i unsat). Narrowed by probe:
`== Some(k)` comparisons check in `pred` today (0 errors both ways); indexing
THROUGH the option (`slots[s.next_sibling]`) stays blocked.

**O6 — buildable in ANOTHER shape, not in V1's.** `lauf-L05.sh` at the listed
bounds reproduces the entry (20/22/64 timeout at 60 s, 17 slow at 6.28 s,
rest ≤0.34 s; wall 3m08s). `ohne-schranke/lauf.sh` reproduces the seed
finding (6/6 non-default seeds answer, 0.16–3.33 s) and the rank shape with
both controls green at N=80256 in ~0.04 s at ~1.4 KB (wall 2m07s).
Unrolling to `count` is not buildable at corpus bounds; the bound-free rank
witness is — for the refutation direction. Proof direction and
L04/L09/L15/L16 unmeasured (see CUTS).

## Verification (this lane, this machine: 31 GB, Z3 4.16.0)

- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`
- `./cargo-pruef`: `== exit 0; failing tests: 0` / `== total: 1379 passed, 0 failed, 1 ignored`
- `./emission-pruef`: `== exit 0`, `ALL PASS -- 42 durchgestochen, 310 von 310 uebersetzen`
  (ASan wie immer NICHT GEFAHREN auf dieser Maschine — environmental, noted by the script)
- Fragment-level: `F01.gab` still `0 errors, 0 hints`; emitted C byte-identical
  before/after; `zeugnis` templates line unchanged; booking simulation clean;
  `pflichten` E lines now 3 (release_slot replaces unlink) with guarded text.
- Text guardians: `pruefe-ausnahmen`, `pruefe-widerruf` green. `pruefe-zahlen`
  (39 BEFUNDs) and `pruefe-todo` (16) are red in files this lane never touched
  (KENNZAHLEN, PLAN, README, …) — pre-existing drift, verified via `git status`.

## CUTS — what is not proved / remains open

1. `revoke`'s maintenance is argued compositionally (per-step `delete_leaf`
   lemma), not encoded — the `traverse by consuming` loop is the remaining step.
2. Rank-shape PROOF direction (`unsat` over the rank form) and L04/L09/L15/L16
   unmeasured; O6 claims the refutation direction only.
3. `delete_leaf`'s claim is CONDITIONAL on sibling consistency (O5/DEMAND G1);
   the premise is B14-blocked as a table invariant today.
4. `beispiele/01-tabelle.gab` (`aushaengen`/`baum_wohlgeformt`) has the same
   pre-fix shape as F01 and was deliberately left untouched (clean-corpus file,
   out of this lane's "rewrite F01" scope) — natural follow-up.

## Where the task as given was wrong

- O4's "maintained by every writer (N496 requires writers to `maintains` it)"
  is unsatisfiable as stated: under the guarded invariant `unlink` can never
  maintain it (L05f sat — it requires `used`, clears `parent`, never clears
  `used`). Decided as guard + new home instead; said plainly. (Side note:
  N496's sentence covers `table`/`group` invariants; `cdt_wohlgeformt` is a
  `spec fn` — the parenthetical is loose, the intent is met bar the documented
  transient. `F01`'s table invariant `wurzel_ohne_vorgaenger` was already
  unmaintained by `unlink` with no refusal, confirming the rule's scope.)
- O4's "or" (guard OR new home) turned out to be "and": the audit had already
  measured the guard alone failing at `unlink`; the home move is what makes the
  guard sufficient.

## Files

- Modified: `dokumente/OFFEN.md` (O2/O4/O5/O6 closed), `dokumente/GABBROV.md`
  (§7 DEMAND G1 row), `messung/fragmente/F01.gab` (guard, maintains moves,
  head decision record), `instrumente/pruefe-emission.sh` (2 booked lines in
  `F1_WEG` + dated comment; no counter touched).
- New: `messung/gabbrov/erzeuge-L05used.py`, `messung/gabbrov/L05d.smt2`,
  `L05e`, `L05f`, `L05g`, `L05h`, `L05i` (regenerated outputs committed).
- No new Lean definitions/theorems (none needed); no `#print axioms` (no Lean touched).
