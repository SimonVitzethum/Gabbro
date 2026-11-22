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
| `nutzerA_aus_ziele` | The same from the duties of the unit given as data (`ZielF`, one per function) and the run facts `c.unit = u`, `ohneAltGlobalB c.expanded`. |
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

The source text enters only through Stage 0's run (owner, 2026-11-22; Stage 0 gets its own correctness
proofs). The generated `Pruefung` module checks the run facts by running Stage 0's front end; no theorem
imports it.

## The generator

`lake build gabbrov` in `programmlogik/bruecke`, then `gabbrov Proofs.Lexer lexer.gab out/` writes, under
`out/Proofs/Lexer/`: `Quelle` (the text), `Daten/S<k>` and `Daten` (the unit `u` as data, 16 functions per
module), `Pflicht/F<i>` (the duty `ziel<i> : ZielF u i`), `Beweis/F<i>` (your proof; written once, never
replaced), `Sammlung/S<k>`, `Lexer.lean` with `nutzerBild` (exactly the image theorems' premise (b)) and
`Pruefung`. Exit 0: (b) is stated; 1: a named refusal (a postcondition reading `old` of a static); 2:
wrong arguments, or Stage 0 refuses the source or its lowering.

A proof opens with `pflicht_oeffnen` (the function's body and postcondition are those of its own lowering)
and `logikFn_aus`; the tactic `gabbrov_wp` applies the model's exact weakest-precondition rules.

## Open

- Normalising the lowered body of large functions inside proofs, so that `gabbrov_wp` applies step by
  step without evaluating whole functions.
- Units whose postconditions read `old` of a static: the duty over the restored program.

The guardian is `instrumente/pruefe-gabbrov.py`.
