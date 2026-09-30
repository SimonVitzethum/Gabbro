# Parser lane -- report (running; `~/claude-lane/AUFTRAG-P.md`, tree `~/gabbro-v`, branch `lane/parser`)

**Where it stands (2026-09-30, session 2):** sieve (a) **5 of 148** (was 2 of 146; 104, 108, 130, 69, 73); the trust path of
the GabbroV bridge is now a GENERIC theorem over every source text (P6); the program-specific
`Cert104` printer is gone from `crates/`. Chain count 2, bridge count 2, end to end 2 -- unchanged
(the widening so far is elaborator + lowering; the bridge refuses the new forms by name; the chain
instances for 130/69/73 are P4 work).

## P6 -- the principle, built

*"Nothing in the compiler or the checker may be there for particular programs. It shall only be
formally proved that GabbroV is ALWAYS right."* (Simon, 2026-09-30)

1. **No program-specific code in `crates/`.** Measured: every string literal of non-test code in
   `crates/*/src/*.rs` (text before `#[cfg(test)]`, comment lines skipped) compared against the names
   of every `fn`/`table`/`type`/`lock`/`const`/`reason`/`arena`/`record`/`enum`/`struct`/`module`/`unit`
   declared in `beispiele/*.gab`. One real hit: `corrlean.rs`, the "104-cut" section (rows only for
   functions named `einzahlen` and `lies`, an assembled `Cert104` literal, "outside the 104
   certificate"). **Removed** (`BodyCert`, `UnitCert`, `funktion`, `zertifiziere`, `zeige_body`,
   `als_param`, `als_slot`, 7 tests); `gabbro corr-lean` prints the general `GRow` section and the
   generic `KCert` section, both used by `zaehle-kette.py`. The remaining hits were language keywords
   and the suffixes of names the checker derives for language constructs (`{Walk}_ist_blatt`,
   `{Accumulates}_lies`, ...), which belong to the language, not to a program.
   Command: the script in this report's history (`python3` over the two sets), `cargo test -p
   gabbro-check corrlean` -> 9 passed.
2. **The duties are stated by Lean from the source.** `bruecke/Bruecke/Quelle.lean`:
   * `Pflichten src : Prop` -- *computed*: `uOf src` (the Lean front end `uebersetzeAllg`), the Bool
     checks of the unit's shape (`nullB`, `stimmigB`, `rangB`) and `meetsU` of every function (the
     statement a person proves). Nothing printed by Rust is in it.
   * `nutzer_aus_quelle : Pflichten src → uebersetzeAllg src = .ok ⟨u, P, fs⟩ → ∃ hn, NutzerPflicht
     (einheitAllg u P hn)` and `nutzerA_aus_quelle` (atomic rely) -- **the generic theorem, over
     every `src`**; `#print axioms`: `propext, Classical.choice, Quot.sound`.
   * `einheitAllg`: the parsed program, no lock invariant, trivial axiom ensures, no declared start,
     the zero memory (`nullSp`; `nullB` refuses a field whose range excludes 0, by name).
   * Witnesses (kept apart from the statement, `Instanz104.lean`/`Instanz108.lean`,
     `BRIDGE-GENERIC` blocks): `pflichten_104`, `pflichten_108`, `nutzer_generisch`.
3. **`gabbro prove --template --source [--bridge <dir>] <file.gab>`** prints the person's file
   *pinned to the source text*: `bruecke/Bruecke/Vorlage.lean` (`vorlage`) runs the Lean front end
   and writes the source as `.toList` pieces, the stage outputs (`toks`, `items`, `u`) as untrusted
   HINTS that the kernel checks (`lex_ok` by `decide +kernel`, `parse_ok`/`elab_ok` by `rfl`, `low_ok`),
   the Bool checks and one computed duty per function (`sorry` to fill), `pflichten` and the generic
   `nutzer`. Rust only quotes the file (`beweis::vorlage_quelle`); 2 CLI tests
   (`beweismessung.rs`): the driver carries the file's bytes exactly, and a missing bridge is SETUP.
   The generated file for 104 compiles with exactly the two owed `sorry`s (4.2 GB, 20 s).
   `lean.rs`'s duty printer stays as an untrusted convenience: the duty proofs of the corpus
   (`programmlogik/Proofs/`) are still stated over its printout, and the instance files convert with
   `rfl` -- a wrong printer makes a build fail, never a false theorem.
4. **Planted defects of the template** (`./instrumente/mutiere-vorlage.py`): a changed count in `u`, a
   changed literal in the pinned text, a dropped token, a changed literal in `items`, a duty stated
   with another function index, a duty weakened to `True`. Result: see the end of this file.
5. **Fragment premises of the generic theorem** (each with its removal plan) are in `STAND-P.md`:
   no lock invariants, no axiom ensures, no declared starts, no atomics, `requires` lowered to `true`
   (P3), `ensures` forms `== < <=`/`and`/`or`/`not`, zero memory only, no arithmetic in the bridge
   (refused by name since wall 1: `sideExpr` is `none`, so `zuBody` is `none` and the duty is FALSE,
   never weaker).

## P1 -- sieve (a), measured (`LEAN_NUM_THREADS=4 python3 instrumente/zaehle-kette.py --lean`, 13 s)

After wall 1: **passes (a): 3 of 148.** First stopping stage of the other 145:

| stage | count |
|---|---|
| `elab: Gegenstand ohne G-Form` (an item kind without a G form) | 81 |
| `parse: wanted (` | 11 |
| `parse: reserved head forall` | 10 |
| `elab: Typ unbekannt: bool` | 10 |
| `parse: wanted ;` | 5 |
| `parse: wanted )` | 4 |
| `elab: Wert ohne G-Form` | 3 |
| `parse`: `wanted {` 2, `@version expected` 2, `fn without body` 2, `expression expected` 2, `wanted of` 1, `assignment or call expected` 1 | 10 |
| `elab`: `Requires-Klausel ohne G-Form` 2, `Funktion nicht impl` 2, `Typ unbekannt: S` / `f64` / `ohne G-Form`, three `Tabelle unbekannt`, `locks ohne requires Held` (1 each) | 10 |

The 81 item stops, by the item kinds that carry them (`Gegenstand.lean` scratch script over the
parse; a program can have several kinds). Number of programs whose ONLY offending kind is:
`static` 13, `device` 8, `proto` 8, nested `module` 5, `translator` 5, `atomic` 4, `arena` 4,
`entry` 3, `format` 2, ... and 27 programs have NO offending item and stop deeper (`bool` 10, ...).
By total programs the kinds rank: `static` 42, `proto` 20, `atomic` 19, `assume` 11, `device` 10.

## P2 -- widening

* **Wall 1** (commit 349ffcb9): a unit without a table (12 programs stopped there in lane 199's
  measurement), `+ - *` in values (range computed as `Expr.add/sub/mul` carry it), the built-in
  `uN`/`iN` widths, an omitted `effects` read as the empty set (a table write is then refused by the
  lowering, planted defect `schreibt1`). Witnesses/defects: `Parser/UebersetzeProben.lean`, 7 theorems,
  `decide +kernel`. Sieve (a) 2 -> 3 (`beispiele/130` reaches OK).
  *Second-wall note:* the first refusal count moved much more than the gain: programs that lost
  "Einheit ohne Tabelle" now stop at `Wert ohne G-Form`, `Typ unbekannt: bool`, `Requires-Klausel`.

* **Wall 2** (commit c5a9da1f): conversions `T(e)` (`Expr.weiter`, refused when the operand does not fit),
  limit words `T::max`/`T::min`, named `const`s inlined at their use, `&`, `|`, `^` over non-negative
  ranges (`Expr.band/bor/bxor`, narrowest width). Sieve (a) **3 -> 5** (69 and 73), measured
  `LEAN_NUM_THREADS=2 python3 instrumente/zaehle-kette.py --lean --allow-stale`: `(a) 5 (b) 22 (c) 16
  (d) 63 (e) 2 of 148`, first stops of the rest `elab` 103, `parse` 40. 9 witnesses/planted defects in
  `Parser/UebersetzeProben.lean` (16 theorems in all). **The probes found a parser defect:**
  `istZuckerBreite` made the kernel decode a String (`u13::max` > 4 GB); repaired.
  *Second wall:* 130, 69 and 73 pass (a), but no chain instance exists (`(e) 3` -- the KCert prints, nobody
  pastes it) and the bridge cannot state their duties: arithmetic, conversions and bit operations have no
  bridge form (`NEEDS OPUS` in `STAND-P.md`).

## Lessons (measured)

* Plain `decide` on the whole pipeline: 9.5 GB for ONE probe (killed session 1); `decide +kernel`:
  1 GB / 2 s. A FALSE `decide +kernel` on a wrong expected string can also run away -- `#eval` first.
* A failing `rfl` on a WRONG stage output (planted defect) runs for minutes; the mutation instrument
  cuts each mutated copy after the theorem it targets.
* `ulimit -v` breaks Lean (thread creation fails); watch RSS and kill by PID.
