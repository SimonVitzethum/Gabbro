# Opus agent H — handlers in the unit, the interrupt leg carried by (a) (OFFEN O19)

*2026-09-26. Branch `worktree-agent-a75fdc081ae4ed9bf`, merged with master 1683d0f7. Machine:
laptop, local (`free -g`: 31 GB total, 17–21 GB available during the runs); every Lean run
through `./lean-bau`/`./lean-probe`, every cargo run through `./cargo-pruef`/`cargo-slot`.*

## Result

| check | measured |
|---|---|
| `./lean-bau` | exit 0, 0 error lines, 347 jobs |
| `./cargo-pruef` | 1401 passed, **0 failed**, 1 ignored |
| `#print axioms gabbro_ziel` (also `gabbro_ziel_g`, `gabbro_ziel_verbund`, `kernHaltE_aus`, `masken_zeuge`, `kernHaltE_verletzt`) | `propext, Classical.choice, Quot.sound` |
| `sorry` / `admit` / `axiom` / `native_decide` in the diff | none |
| `pruefe-akzeptiert-diff.py --selbsttest` | ok, including the new pair: 59 accepted at `masken`; 59 with `TAKT`'s mask removed (= gift 460 word for word) refused at `masken` **alone** |
| `pruefe-akzeptiert-diff.py` (full) | compared 24, findings 0, not-measured 0, construction pins K1–K6 hold; `pin: masken true on 24/24`; `beispiele/59` compared and agrees |
| Rust `H102` | `gift/460`: `[H102]` once; `beispiele/59`: 0 errors |
| certificates | regenerated through the lock (`GABBRO_ZERTIFIKATE=schreiben`): G59 gains `gP.unterbricht` (`takt_verteiler` true); 22 other certificates change by one header comment line only |

No code, no gift, no example taken (reserved N551–N555, gifts 1331–1340 stay with O19; booked in
AGENTS §7).

## The Spec diff (review target)

Delimited hunks: `-- BEGIN/END handler discipline`, `-- BEGIN/END handler leg`, `-- BEGIN/END
handler block` (header), plus one line in `Ziel`, one field in `AkzeptiertSpec`, `Verbindbar`,
`SchnittstelleSpec`, and the NOT CLAIMED paragraph.

1. **`Programm.unterbricht : D.Fn → Bool := fun _ => false`** (Syntax.lean). *Decision:* in the
   program, not in `Einheit` and not in `Deklaration`. `Ziel` reads `P`, `M0`, `M` only, so a
   field of `Einheit` would have meant a new parameter of `Ziel`/`ZielF` in ~49 files; a field of
   `Deklaration` would index every `Stmt`, so the refused variant of example 59 (same
   declaration, one handler more or one lock body different) could not reuse its bodies. `E.P` is
   in the unit, so the dispatch fact IS in the unit. `mitRuhe` carries it (idle root: none);
   `verbindeP` inherits `E₁`'s, and `Verbindbar` demands both units agree (one dispatch fact, like
   one contract).
2. **(a):** `AkzeptiertSpec.masken : MaskenDisziplin P fs` — for every `w` with
   `P.unterbricht w`, every `f` with `reachB P fs w f`, `mE (NurMaskiert D) (P.rumpf f)`.
   Component `maskenB` of `Akzeptiert`, `maskenB_iff` exact. `SchnittstelleSpec.masken` over the
   composed hull, decided in `schnittstelleB` (`schnittstelleB_iff` extended).
3. **The leg:** `keinKernHalt : KernHaltE P O passes M0 M` replaces `KernHaltG`. `HandlerVon P M0 t
   := P.unterbricht (M0.faeden t).kopf.f`. For every `kern`, every `LaufG` run from `M0` to `M`
   with `KernPlan kern (HandlerVon P M0)`, a handler `g` and another thread `f` of its core: `g`
   at `locks L` ⇒ `f` does not hold `L`. `KernPlan` is unchanged (F11) and is the named hardware
   assumption, now the ONLY premise inside the leg. `KernHaltG` moved verbatim to Masken.lean
   (it is the proof engine and the atomics files use it).

   *Decision on cores:* no core field. The leg quantifies over **every** core assignment, which is
   stronger than any fixed one; the language and runtime do not pin. "The core machine" is G
   restricted to `KernPlan`-admitted runs — every such run is a G run, so every other leg holds on
   it a fortiori; no new machine was introduced (recorded in the header).

   *Decision on (d):* `KernPlan` constrains runs, (c)/(d) constrain answers and the start, so the
   hardware schedule stays a premise of the leg, named in the header's NOT CLAIMED/assumptions
   paragraph, not a field of `Laufzeit` (which is quantified before the run).

### Why nothing is weakened, and what got stronger

* **Contentful now.** `kernHaltE_verletzt` (MaskenZeuge): on `kPv` (example 59 whose handler takes
  the unmasked `RING`), a real three-step run of the runtime start, admitted by `KernPlan` on one
  core, reaches a machine where `KernHaltE` is **false**. So `Ziel` with the new leg is not implied
  by the old `Ziel`; it is discharged from (a) (`kernHaltE_aus`), and `kPv` is exactly what (a)
  refuses (`handler_abgelehnt`), while the same bodies with no handler declared pass
  (`kPv_ohne_handler`).
* **(a) tighter only where `H102` refuses.** On a program with no handler `maskenB = true`
  (`maskenB_ohne`) and the leg holds with nothing from (a) (`kernHaltE_ohne_handler`): every unit
  of before — the field did not exist, so all of them — keeps verdict and conclusion.
  `akzeptiert_nodup_gleich` now reads `Akzeptiert = AkzeptiertVor && maskenB`; `akzeptiert_vor_neu`
  takes the `maskenB` premise; `pruefer_vor_neu` conjoins an old checker with `maskenB`.
  `AkzeptiertA`/`AkzeptiertX` (atomics, O25/O25b) keep their components; their embeddings drop
  the new conjunct (they are weaker checkers, standalone).
* (b), (c), (d) and every other leg unchanged. `folge` (Opus G) merged in without conflict in
  `Ziel`; the one textual conflict was the NOT CLAIMED paragraph, resolved as the union.

## Proof of the leg (Masken.lean §4)

`kernHaltE_aus`: `hA.abg` gives `AbgK` of each handler graph, `hA.masken` gives
`mE (NurMaskiert D)` on it; `mE_und` (new, MitRuheStatisch.lean: a body admitted by two feature
sets is admitted by their meet) and `mE_mono` give `mE (maskM …)` → `MerkAbg` (`merkAbg_maskM`);
`merkInvG_start` gives the invariant at `RufStartG`; `anSperre_start_falsch` the empty lock heads;
then `kernHaltG_gilt`. Transfer to `P.mitRuhe`: `akzeptiertSpec_mitRuhe.masken` via
`reach_mitRuhe_cases` and `rumpf_mitRuhe_mE` (`NurMaskiert`'s `mZ` is itself by `rfl`).

## Witnesses (MaskenZeuge.lean, on Korpus59.lean — which now declares `unterbricht` for `takt_verteiler`)

* `masken_zeuge` — 59, one core: thread 1 takes `RING`, the handler preempts and stands at
  `locks TAKT`; the leg of `korpus59_ziel` (now from (a)) is applied with only the run and the
  schedule — no hand-supplied call graph, feature set or discipline (those arguments are gone).
  `kM0_handler`: the handler set of the unit is exactly thread 0.
* `masken_59`, `masken_disziplin_59/460` — the component on 59 and the discipline Bool per root.
* `kPv_ohne_handler`, `handler_abgelehnt`, `kernHaltE_verletzt` — the refused gift-460 shape and
  the failing leg.

## H102 ↔ `maskenB`, measured

* Diff script: component `masken` ↔ Rust codes `{H102}` (added to the Akzeptiert code set); new
  construction pin **K6**: the export's `unterbricht` arms equal the source's `entry … via idt`
  roots. `startet_aus` now includes `entry`/`boot` dispatch roots (the exporter has carried them
  as starts since lane 198); the old PARTIAL mark that excluded every `entry` file is retired —
  `beispiele/59` is compared for the first time and agrees.
* Self-test negative: the export of 59 with `TAKT`'s mask flipped (the one-word diff of gift 460;
  the Rust side refuses 460 with `H102`, measured) is refused by the Lean Bool at `masken` and at
  no other component.
* Not measurable by the script: gift 460 itself (refused by the checker, never exported); gift 461
  likewise. The correspondence on refused files rests on the self-test flip and the gift probes.

## Exporter (`lean_g.rs`)

`Model.unterbricht` collects `entry … via idt` dispatch paths (the same test as
`Kontext::unterbricht`); `gP` gets an `unterbricht` arm per function where at least one exported
function is a handler, nothing otherwise (byte-identical `gP` for every handler-free program). The
certificate header line on `entry`/`boot` says so.

## What remains of O19 (OFFEN.md, narrowed again)

* No `cli`/`sti` in the emitted C: translation validation has nothing to relate `KernPlan` to.
* No pinning: which core a thread runs on is no fact of the unit (the leg holds for all); O17's
  "each thread its own cell" still needs it.
* Handler re-entry and handler-on-handler preemption (a handler thread runs once in G).
* A thrown entry without `via idt` (`beispiele/57`'s IPI) is no handler, as for `H102`.

## Files

`grammatik/Grammatik/{Syntax,MitRuhe,MitRuheStatisch,Korpus59}.lean`,
`Zielsatz/{Spec,Akzeptiert,Ruhe,Masken,MaskenZeuge,Beweis,PoolSym,Verbund,VerbundZeuge,AtomarAkzeptiert}.lean`,
`Speichermodell/AtomarZeuge.lean`, `Zertifikat/*` (regenerated), `GenOblig104/108.lean`
(regenerated header), `crates/gabbro-check/src/lean_g.rs`, `instrumente/pruefe-akzeptiert-diff.py`,
`dokumente/{OFFEN,SATZKARTE}.md` (§57), `TODO.md`, `AGENTS.md`.
