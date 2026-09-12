# MUSE-REPORT-74 -- lane 74: a foreign write must hold the guard

## What was done

MODEL REPAIR (lane-54 finding): `Stmt.axiomCall` could write any table in
`D.aschreibt a` without holding that table's guard locks. Repaired as a
premise of the constructor, exactly like direct writes carry theirs.

1. `grammatik/Grammatik/Syntax.lean`: `Stmt.axiomCall` takes two new premises
   (keeping `hw`/`hg`):
   - `hd : forall t, D.aschreibt a t = true -> darf D t Λ`
   - `hgd : forall g, D.agschreibt a g = true -> gdarf D g Λ`
   (`gdarf` is the exact predicate the direct global write `assignGlob` uses.)
2. Propagated to every use site. Patterns take `_`; term builders pass proofs:
   - `Semantik.lean`: `execStmt` axiomCall arm (semantics unchanged, new fields ignored).
   - `Satz.lean`: `stmt_gut` axiomCall case.
   - `HoareRegeln.lean`: `StmtOhneRuf.axiomCall` constructor + two
     `fun a args h hw hg ...` motive cases (now `... hd hgd ...`).
   - `Maschine.lean`: `speicherfest` case split binder.
   - `MaschinenKette.lean`: one `hax_all` match (7 underscores now).
   - `Extraktion.lean`: `stmtKanten`, `stmtOrte`, `stmtTraeger`, `stmtAtome`
     matches; all `hax` matches; `False.elim hax` case binders;
     `execEreignis_aus_axiomCall` and `hmark_hcar_aus_progAus_axiomCall`
     take new `hd`/`hgd` premises and forward them (one dropped `(hΛa : Λa = Λ)`
     line was restored after it broke the build).
   - `Ziel.lean`: `pcSchritt_blatt_progAus_axiomCall`,
     `pcReach_blatt_progAus_axiomCall`, `kette_mit_zeugen_orakel` take new
     `hd`/`hgd` premises and forward them (plus two `hax` matches).
3. New file `grammatik/Grammatik/FremdSperre.lean`, imported at the end of
   `grammatik/Grammatik.lean`. See names below.

Committed in two steps: `8ee639e` (repair + propagation),
this report goes with the `FremdSperre.lean` commit.

## New definitions and theorems (`Gabbro.Grammatik` namespace)

Concrete witness scene (one guarded boolean table, one lock, one writing axiom):
`DF`, `VF`, `ΛF` (`[held ()]`), `σF` (slot `false`, trace `[nimmt () []]`),
`OF` (oracle flipping every slot to `true`, keeping locks/trace),
`argsF`, `ρF`, `σrF`, `ρrF`, `σF'`, `RF` (never consulted).

Component proofs: `hdF`, `hgdF`, `hwF`, `hgF`, `hOF : GutO OF`, `hhF`,
`hexecF` (by `rfl`), `hdiffF`, `hLmem`, `zeuge_schreibt`.

Main results:
- `axiomCall_haelt_waechter`: for a general `D`, an `axiomCall` step whose
  oracle world differs from the entry world on a slot of `t` concludes
  `L ∈ σ.haelt` for every lock guarding `t` (this IS `offen σ.spur`,
  definitionally), AND every global the axiom may write has its guards held,
  AND `Rahmen V.schreibt V.gschreibt σ σ'`. Proof: difference forces
  `D.aschreibt a t = true` through the oracle frame (`hO`), `hd` turns that
  into `darf`, `HeldGenau` (`hh`) makes it dynamic. Every Prop premise is
  applied in the proof (`h` closes the `einpassenErg = none` arm by
  rewrite; `hw`/`hg` widen the frame; `hd`/`hgd` give the guards).
  The conclusion is deliberately stronger than the tasked single leg;
  the tasked leg is the first conjunct.
- `axiomCall_ohne_sperre_nicht_ableitbar : darf DF () [] -> False`
  (lane-54 counterexample as a theorem: with `Λ = []` the guarded call is
  not derivable).
- `axiomCall_haelt_waechter_zeuge` (rule-13 companion): all premises of the
  main theorem proved jointly on the concrete scene, concluding the guard,
  the frame, and the non-degeneracy facts (`DF.schreibt () () = true` by
  `zeuge_schreibt`; the reached step flips the slot by `hdiffF`).

`#print axioms` for all three main theorems:
only `[propext, Classical.choice, Quot.sound]` -- no `sorryAx`.

## Last `./lean-bau` result line

`== 0 error line(s) in the COMPLETE output` (exit 0, full project).
The one warning in the log (`Schiebung.lean:102` unused `hw2`) is
pre-existing on the base tree. `pruefe-englisch.py` is red on the base tree
too (checker-ratchets, does not scan `grammatik/`); not mine.

## What remains open (also as `CUTS` in the file)

- F1: no dynamic global-guard leg (oracle differs on a global).
- F2: `GutO` still forces oracle spur equality (see proposal below).
- F3: `Block.bindAxiom` carries no new guard premises in this lane.

## Points where the task as written is wrong or vacuous

1. "Concrete declarations with axioms discharge it by `decide`/`simp`" is
   vacuous: every `Deklaration` literal in the tree sets `Ax` to an empty
   type (`fun e => nomatch e` / `a.elim`), so there is no axiom term to
   discharge anything for. The propagation compiled with no such steps.
2. The repair is scoped to `Stmt.axiomCall`, but `Block.bindAxiom` runs the
   same oracle over the same footprint with only `hw`/`hg`. The CSL hole
   persists there; I left it untouched per the task (F3), it should be a
   follow-up lane, not an oversight.
3. Minor: "in `offen` of the thread's trace" is proved as `L ∈ σ.haelt`;
   `World.haelt` is defined as `offen σ.spur`, so this is exact, not an
   approximation.

## Reply: must the oracle RECORD access events?

Yes -- for the `hcar` (own-state) leg, not for the guard leg proved here.
Today `execEreignis_aus_axiomCall` shows a fired `axiomCall` emits exactly
its argument reads; the foreign write itself is traceless by `GutO`
spur equality. Hence `hwit_aus_feuerung_ohne_axiomCall` must exclude
`axiomCall`, and no step-witness (`hneu_wit`) can ever fire for a carrier
written only by the oracle. Guards hold (this lane); the write is still
invisible.

Smallest `GutO` change (NOT made): keep the frame/haelt conjuncts, but let
the oracle *declare* what it touched and have the call site stamp the
events. Concretely, extend the oracle with a footprint report, e.g.
`wirkt` additionally returns `List (D.Tab + D.Glob)` of touched carriers,
`GutO` requires every reported carrier inside `aschreibt`/`agschreibt`
(else the frame conjunct already fails) and `execStmt`'s `axiomCall` arm
appends `.zugriff t true Λ σ.haelt` / `.gzugriff g true Λ σ.haelt` events
for exactly those carriers. Do NOT pass `Λ` into `wirkt` (signature churn
for no reason) and do NOT let the oracle invent `Λ`-stamped events (it
cannot prove `darf` for them -- only the call site holds `hd`). With the
site stamping, the new `hd`/`hgd` premises make the recorded events `gut`
by the same `gut_merke` step direct writes use, and the `hcar` exclusion
of `axiomCall` can close. Enumerating `aschreibt` inside `execStmt` is the
one awkward point (`execStmt` has no carrier-domain parameter); the
oracle-returned list sidesteps it.
