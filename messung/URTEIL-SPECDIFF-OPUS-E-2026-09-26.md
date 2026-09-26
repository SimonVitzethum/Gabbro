# Verdict — the Spec diff of Opus agent E (linking separately compiled units, `N501`–`N505`)

*Independent adversarial review, 2026-09-26. Branch `worktree-agent-a11192d63a8d21952`, head
`62314678` (pieces `3db421d6` Lean, `a9f7670c` Rust, `98de28da` records; master `7f3b2b43`
merged in `5c0ff80e`); report `messung/OPUS-E-LINKEN.md`. Measured in the worktree through the
queued wrappers only (`./lean-bau`, `./lean-probe`) and the already built `target/debug/gabbro`
for single `check`/`link` runs. Text fixes committed separately (`cf5829c2`). Nothing merged
into master, nothing pushed.*

## 0. Verdicts at a glance

| Change | Verdict |
|---|---|
| `GabbroZiel` | **unchanged** — every hunk of the `Spec.lean` diff lies in the header comment (lines < 940) or after the end of `def GabbroZiel`; 231 insertions, 3 deletions, the 3 deleted lines are the old NOT CLAIMED phrase |
| `GabbroZielVerbund` / `gabbro_ziel_verbund` | **SOUND, contentful** (§2) |
| Link check `SchnittstelleSpec` / `schnittstelleB` | **SOUND**; decided exactly (`schnittstelleB_iff`) |
| `E₂.Q = E₁.Q` as "same hardware assumptions" | **right formalisation** under the union declaration (§3) |
| Witnesses (`VerbundZeuge.lean`) | **SOUND, non-degenerate** (`vz_huelle_schreibt`), with one caveat (F5) |
| Replaced NOT CLAIMED line | **true, and now complete** after F1/F2 were added (`cf5829c2`) |
| Rust `gabbro link`, `N501`–`N505` | **SOUND in what it refuses, OVERCLAIMED in what its green means** — F1: a known false accept for pairs with threads on ONE side. Fixed in text (`cf5829c2`), open in code (OFFEN O28) |
| Record slip | the branch renumbered Opus D's SATZKARTE reference 53 → 54 in `TODO.md`/`OFFEN.md`; restored (`cf5829c2`) |

**Safe to merge: yes, with `cf5829c2`.** The Lean statement has no gap I could find. The Rust
tool only ADDS refusals over master (no pass file is touched), so it weakens nothing; the gap in
F1 already exists in master's `gabbro check --with`, and `gabbro link` merely failed to close it
while its documentation said it did. That is now said.

## 1. Build and axiom evidence (measured, before the merge)

| Measurement | Result |
|---|---|
| `./lean-bau` | **exit 0, 0 error lines in the complete output, 324 jobs** (`free -g`: 18 GB available) |
| `#print axioms gabbro_ziel` (`./lean-probe`, `import Grammatik`) | **`[propext, Classical.choice, Quot.sound]`** |
| `#print axioms gabbro_ziel_verbund` | **`[propext, Classical.choice, Quot.sound]`** |
| the other 11 `#print axioms` lines in `Verbund.lean`/`VerbundZeuge.lean` | subsets of the three (`verbinde_leer`, `vz_vertrag_zu_schwach`: `[propext]`; `vm_abgelehnt`: `[propext, Quot.sound]`) |
| `sorry`/`admit`/`native_decide`/`axiom` in both new files | **none** (grep exit 1) |

## 2. Is `GabbroZielVerbund` contentful, or the single-unit case in disguise?

The worry: both units live over ONE `Deklaration`, with the same contracts, table invariants,
lock invariants and initial memory — is anything left that is "separately compiled"?

**Yes, the part that matters.** What is per unit:

- **acceptance**: `C.akzeptiert E₁` and `C.akzeptiert E₂`, each over its OWN program, in which
  the other unit's functions are leaf placeholders (`Platzhalter`). Every per-body component of
  the linked program's `AkzeptiertSpec` (fragment, lock floors, answer sites, closed graphs,
  roots) is taken from the owner's verdict (`akzeptiertSpec_verbinde`); the bodies really
  differ between the units and the linked program (`verbindeP` picks by owner);
- **the user's duty**: `NutzerTeil e E₁` proves only the bodies unit 1 owns; the placeholders
  owe nothing (`nutzerPflicht_verbinde`).

What is re-decided at the link: only the three whole-program components (`lok`, `renn`,
`einzeln`), over composed hulls built from each owner's `reachB` and each function's own
footprint — per-unit summaries. The equalities in `Verbindbar` are the modelling of "one
declaration" and not a smuggled whole-program premise: they concern non-body data only.

The witness shows the difference is real: the app's own graph does NOT reach the writer
`einzahlen` (`reachB vzApp … zEin = false`), the composed hull does (`vz_huelle_schreibt`), and
`vm_abgelehnt` exhibits two units each accepted alone whose link fails — exactly the case a
per-unit proof cannot see. `verbinde_leer` shows the operation is conservative.

The proof is honest in structure: it builds the linked unit's premises and applies
`gabbro_ziel`; nothing below the goal theorem is re-proved, and the only new general lemma of
weight (`reachB_ruft`/`erreichB_stabil`, closure of the computed graph on a complete list) is a
counting argument over `fs.length` rounds, checked.

## 3. The hardware premise, and Rust `N505`

`E₂.Q = E₁.Q` states that one oracle answers both units' axioms. With the union declaration
that is exactly "the same hardware assumptions": an axiom only one unit names is still one
entry of the one `AxEns D`. Rust `N505` compares by text the `assume`/`axiom`/`device`/
`profile` items and bodiless foreign `extern fn`s that BOTH units name; items only one names
join the union. That is consistent. Not traced: a library's `requires profile` against the
partner's profile is `N217` of the per-unit check, not of `gabbro link` (a lib's own check
without a profile already falls with `N217`, so no silent path was found, but the pair was not
probed).

## 4. Findings, ranked

### F1 — HIGH (Rust): a pair with threads on ONE side links green over a real race

`verbund.rs` refuses a pair in which BOTH units start threads (`N503`) and maps `N503` to
`SchnittstelleSpec (keinRueckruf, lok, renn, einzeln)`; the report's §6 reads as if one-sided
pairs were covered by the per-unit checks. **They are not.** The importer's race check sees an
imported head's `effects` WRITES but not its READS. Reproduction (the Rust twin of
`vm_abgelehnt`):

```
-- bib.gab
module bib {
pub type Stand = u32 in 0 .. 100;
pub table konto count 2 { slot { stand : Stand, } }
pub impl fn lies() -> Stand effects { reads konto.slots } costs <= 16 ops { return konto.slots[0].stand; }
}
-- app.gab
module app {
use bib::lies;
use bib::konto;
impl fn t1() effects { reads konto.slots } costs <= 64 ops { let x = lies(); return; }
impl fn t2() effects { writes konto.slots } costs <= 64 ops { konto.slots[0].stand = 1; return; }
concurrent { t1, t2 };
}
```

- `gabbro check bib.gab`: 0 errors; `gabbro abi bib.gab > bib.gabi`;
- `gabbro check app.gab --with bib.gabi`: **0 errors**;
- `gabbro link --with bib.gabi bib.gab app.gab`: **"0 refusal(s)", exit 0**;
- the same two modules in ONE file: **`N291` + `N301`** (write-read race on `konto`);
- control: the mirror case (the head WRITES, the app thread reads) is refused per unit
  (`N291`/`N301`), and a body reading what its effects call `pure` falls with `E010` — so the
  read IS in the exported head; the importer just does not use it.

The Lean side is right (its link check refuses precisely this; `vm_abgelehnt`). The gap is
pre-existing in `gabbro check --with` (no pass file changed on this branch), so merging does not
make anything worse; but `gabbro link` green does NOT establish premise (a)'s link check.
**Fixed in text** (`cf5829c2`): `verbund.rs` "What this does NOT check", `Spec.lean` NOT
CLAIMED, OFFEN O28, TODO, report §6. **Open in code**: port `lok`/`renn` over the heads' `effects`
reads (a head read of an unguarded, non-atomic carrier that another root of the thread-starting
unit writes), or refuse such a pair. Until then the Rust linker is a stale-head detector, not the
link check.

### F2 — LOW: "the union — what `gabbro abi`/`--with` builds" overstated

`--with` gives the importer the exporter's EXPORTED part, not the union, and each Rust unit is
checked over its own view. The Lean premise is acceptance over the union; that acceptance over
the union follows from acceptance over one's own view (monotonicity in unused declarations) is
plausible but not proved — the same kind of bridge as "the checker in the statement is the Lean
Bool". Reworded in `Spec.lean` (`Verbindbar` docstring) and the report (`cf5829c2`).

### F3 — LOW: `Verbindbar` equates contracts and start memory for ALL functions and carriers

Including each unit's view of the other's PRIVATE functions and carriers. A modelling artefact:
satisfiable by construction (the placeholder carries the owner's contract), and harmless since
placeholders are leaves and owe nothing. Recorded so nobody reads it as a Rust obligation.

### F4 — LOW: record slip

`TODO.md` and `OFFEN.md` pointed Opus D's invariants at SATZKARTE §54 (Opus E's section);
restored to §53.

### F5 — INFO: the positive witness is a re-split of an existing fixture

`vz_verbinde_gleich`: the linked unit IS fix lane F10's `zPool`, with `axWahr` as `Q` and
threads on one side only. That is fine for non-degeneracy (the hull statement is real), but no
witness has threads on BOTH sides or a non-trivial `Q`. Not required by the statement.

### F6 — INFO: the Rust contract comparison

Contracts, effects and signatures compared as whitespace-normalised, order-free TEXT — refuses
more than necessary (a semantically equal rewrite falls), never less than the Lean `Verbindbar`
equality. Safe direction. `N504` (costs) has no Lean counterpart and says so.

## 5. The replaced NOT CLAIMED line

The new residue — different hardware assumptions, callbacks through an import, an importer
relying on another contract, dynamic loading, ABI-level linking of foreign C, the C-level link
step — is true of the theorem as stated. Missing were F1 (Rust does not decide the link check)
and F2 (union vs own view); both are now named.
