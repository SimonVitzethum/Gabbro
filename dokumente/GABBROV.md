# GabbroV

GabbroV is the bootstrap program logic of Gabbro, written in Lean. It states, for the unit Stage 0
compiles, exactly premise (b) of the goal theorem, and nothing beside the program's own logic is left
to the user. Its earlier channels (the Body language, the per-form bridge, the printed duty files) are
deleted; their history is in git.

## The one theorem

The model's certificate (`grammatik/Grammatik/Logik/WP/HA/Zertifikat.lean`) names every logic duty of a
unit; `logikPflichten_iff` proves that together they are exactly premise (b), `NutzerPflichtA E`, for
every program. GabbroV states that certificate over the very program Stage 0 lowers
(`programmlogik/bruecke/Bruecke/Zertifikat/`):

| Theorem | Says |
|---|---|
| `nutzerA_aus_compiled_logik` | For every compilation `c` and every language form: every function's logic (`LogikFn`), the foreign bodies' locality and Stage 0's decision of the data parts give `NutzerPflichtA` of Stage 0's judged unit over `c.program` -- the premise of the image theorems. |
| `logik_aus_nutzerA` | Conversely: the duties are not stronger than (b). |
| `entschieden_sound` | Stage 0's own decisions (`checkUnitLock`, `checkStartRequires`) are the certificate's lock and start duties. |
| `nutzerA_aus_ziele` | The same from the duties of the unit given as data (`ZielF`, one per function) and the run facts `c.unit = u` and `altVon c.expanded = alt` (the source postconditions that read `old` of a static, by function). |
| `programm_von` | The lowered program has at every function the postcondition, body and precondition of that function's lowering. |
| `nutzerA_aus_ziele_erfuellbar` | The premises hold jointly; the lowering accepts the instance; its duty is proved over its lowered body. |

No form is special: every form Stage 0 lowers is covered by the same theorem.

## What the user owes

Only the program's logic: from `requires`, every return meets `ensures` and the owed invariants, and no
call stops on a precondition or a logic stop, at every budget, under every call meaning, oracle and
environment move the goal theorem quantifies (`LogikFn`). The locality of foreign bodies' declared
`ensures` is part of the environment contract the user names. Lock invariants and the starts'
`requires` are decided by Stage 0's checker.

## The boundary

The source text enters only through Stage 0's run (2026-11-22; Stage 0 gets its own correctness
proofs). The generated `Pruefung` module checks the run facts by running Stage 0's front end; no theorem
imports it.

## The generator

`lake build gabbrov` in `programmlogik/bruecke`, then `gabbrov Proofs.Lexer lexer.gab out/` writes, under
`out/Proofs/Lexer/`: `Quelle` (the text), `Daten/S<k>` and `Daten` (the unit `u` as data, 16 functions per
module), `Pflicht/F<i>` (the duty `ziel<i> : ZielF u alt i`, over the program with the `old(global)` postconditions restored as Stage 0 restores them: `restored`), `Beweis/F<i>` (your proof; written once, never
replaced), `Sammlung/S<k>`, `Lexer.lean` with `nutzerBild` (exactly the image theorems' premise (b)) and
`Pruefung`. Exit 0: (b) is stated; 2: wrong arguments, or Stage 0 refuses the source or its lowering.

**A Lake package per unit.** `gabbrov` also writes `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` (kept when present): `lean_lib MODULE` on top of GabbroV (`bruecke`, by path), with the packages shared with `grammatik/.lake/packages`, so no second Mathlib is fetched. `lake build` in the output directory checks the unit; after a change of one body it builds again only that body, that function's logic and proof, the source text, the collection and the root.

**One function, one duty, independently.** Every body is its own module `Rumpf/F<i>` with the definitions `rumpf<i>`/`rueck<i>` NOT exposed; the unit `u` (`Daten`) refers to them by name. The contracts of callees are read off their contract lowering alone (`requires_vertrag`, `ensures_vertrag` in `Zertifikat/Vertrag.lean`), so the duty of a function needs no other body; `Logik/F<i>` alone reads its own body (`import all`). A change of one body changes only the private part of its `Rumpf` module: every other module keeps its interface, and Lake checks only that function's duty again. A duty that needed another body would not reduce in the kernel and fail, visibly.

**The logic is output.** For every function `gabbrov` writes `Logik/F<i>` with the command
`gabbrov_logik logik<i> : ziel<i>`, which is regenerated on every run. The command runs the
automation below on the duty and states what it leaves: each remaining goal, closed over the variables
and hypotheses it depends on, is one conjunct of `logik<i> : Prop`, and `True` when nothing remains.
It proves `logik<i>.genuegt : logik<i> → ziel<i>` with the automation's own proof, checked by the
kernel. Your file `Beweis/F<i>` is `theorem beweis<i> : ziel<i> := logik<i>.genuegt (by trivial)`:
`trivial` closes it when nothing remains; otherwise `#print logik<i>` shows the program's logic you
prove there, for example `∀ ρ, x ≤ 100 → 0 ≤ x → x + x = x + x + 1` for a wrong `ensures`.

The automation (`gabbrov_beweis`) does four things:

1. It opens the duty at the function's own lowering (`pflicht_oeffnen`) and puts the lowered body
   into the kernel's normal form.
2. It executes the body symbolically by the model's exact weakest-precondition rules (`gabbrov_wp`):
   - sequences, bindings, assignments and writes;
   - branches, matches and reasons, with a symbolic value split into its finitely many cases;
   - `narrow`, checks and lock releases;
   - bounded `retry` and `traverse`, unrolled pass by pass;
   - calls, split on the callee's outcome, with the callee's precondition read off its own lowering;
   - foreign calls, split on the oracle's answer;
   - every other form by one step of the semantics' own equation lemmas, a split of the `match` it
     leaves on a symbolic value, and reading a remaining sub-block as its weakest precondition again
     (`Generisch.lean`); no form needs a rule of its own.
3. It closes the return obligation (`gabbrov_fertig`).
4. It turns what is left over symbolic values into integer arithmetic (`gabbrov_arith`). The kernel
   checks that this arithmetic is the evaluation, and `omega` then tries to close it.

Every rule is an equivalence. Every step is checked by the kernel, and no tactic is a trust point.
Whatever remains in the file is the program's own logic, stated readably. When a program violates its
contract, the violated condition is what remains, for example `x + x = x + x + 1` for a wrong
`ensures`.

Measured on 110 Stage-0 probes (172 functions), 148 duties are proved by `gabbrov_beweis` alone. Of
the 24 that remain:

- 10 are refusal probes, which keep exactly their violation.
- 14 are still open:
  - fallible and block-level indirect calls, and a function pointer whose value is only known at
    run time;
  - `shift`;
  - invariants and quantifiers over tables;
  - `count` over arrays;
  - 4 timeouts of the elaborator's `whnf` in nested locks inside loops.

## Open

- Rules for the forms just listed.

The guardian is `instrumente/pruefe-gabbrov.py`.
