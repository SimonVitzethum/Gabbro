# MUSE-REPORT-840: Composition closing — flag-ledger closing

Lane 840, clone `/home/simon/Dokumente/gabbro-muse/a840`, branch `muse/840`
(verified: `.git/HEAD` = `refs/heads/muse/840`). Owned files only:
`grammatik/Grammatik/X86/ComposeFlagLedger.lean` (new),
`grammatik/Grammatik.lean` (one import line),
`MUSE-REPORT-840.md` (this file).

## What was done

Closed every ALU flag producer to its consumer with liveness in one checked
composition step, reusing the accepted modules by name and re-proving
nothing:

- Producer side (`ArchitecturalFlags`, lane 692): `AluOp` effect classes
  with defined/undefined flag rows, `liestStatus`, `verbrauchOK`, the
  `*_sicher` agreement lemmas, `divVerbrauch_verweigert`, `mulU_sf_frei`.
- Consumer side (`FlagDependencies`, lane 601): `FlagName`, `liestFlag`,
  `flagWert`, `stimmtUebberein`, the rule lemma `bedingung_stabil`,
  executed through the accepted `Ausfuehrung.schritt` (`jumpIf32`) and the
  accepted `ControlCodec` byte steps; witnesses `jccSchritt_stabil_zeuge`,
  `mov_xor_wechsel_zeuge`; refusals `jccLaenge_verweigert`,
  `jccKurz_verweigert`.
- Reached runs and memory (`Ausfuehrung`): `lauf`, `zeugeProg`,
  `zeigeZustand`, `zeuge_speicher_aendert_sich`, `probe_sprung_genommen`,
  `zeugeFlags`, `zeugeFlagsGleich`.

New definitions/theorems (all in `Grammatik.X86.ComposeFlagLedger.lean`):

- `definiertFlag : AluOp → FlagName → Bool` — conservative defined-flag
  map per producer class (add/sub/logic all true; mulU/mulS only cf/of_;
  div none; shift all but of_).
- `ledgerErlaubt (prod) (c) (leb) : Bool` — the ledger: every flag the
  consumer reads that is live is defined by the producer.
- `ledger_add_immer`, `ledger_sub_immer`, `ledger_logik_immer` — admit
  every consumer under every liveness (by simp).
- `ledger_mulU_trag` — unsigned MUL admits exactly the CF/OF consumers
  (`c = .o ∨ .no ∨ .b ∨ .ae`, the hypothesis row of `mulVerbrauch_sicher`).
- `ledger_div_verweigert`, `ledger_mulU_e_verweigert`,
  `ledger_shift_o_verweigert` — planted ledger refusals (by decide).
- `ComposeFlagLedger_verbindung` (TARGET) — closing step: ledger admission
  + live reads + producer defined-agreement give `bedingung c f =
  bedingung c g`, via the accepted rule lemma `bedingung_stabil`. Every
  premise is used (ledger per-flag extraction, liveness gate, producer
  agreement); conclusion is derived, not restated.
- `ledger_umschreibung_stabil` — dead-flag rewrite rule: preserving live
  flags keeps the consumer outcome (via `bedingung_stabil`).
- `ComposeFlagLedger_verbindung_zeuge` (TARGET companion) — joint witness:
  ADD `0x0F + 0x01` for a zero consumer under full liveness, the
  composition firing on it, the memory-changing `zeugeProg` run (rbx = 42,
  stack byte 0 → 42), both consumer pins, the executed taken `je`
  (`probe_sprung_genommen`), and both DIV refusals (ledger + execution).

## Build results

- `./lean-probe grammatik/Grammatik/X86/ComposeFlagLedger.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (final).
- `./lean-bau` (whole project): `== exit 0; 0 error line(s) in the COMPLETE
  output`, `✔ [508/509] Built Grammatik (14s)`, `Build completed
  successfully (509 jobs).`
- Axioms (`#print axioms`, from the probe output): every new theorem
  depends only on `[propext]`, except the joint witness which depends on
  `[propext, Quot.sound]` (inherited from the reused accepted witnesses) —
  both within the standard `gabbro_ziel` set
  (`propext, Classical.choice, Quot.sound`).
- `git status`: only the two owned Lean paths changed (one new file, one
  added import line). No diagnostic/gift/example/CLI numbers, no
  MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits, no
  friend-reserved optimiser files.

## What remains open (explicit CUTS, also in the file)

- No hardware correspondence is claimed (rows owned by lane 692).
- No liveness analysis is computed here: `hlive` is a premise for the
  future liveness producer; nothing selects or rewrites instructions.
- Shift OF at masked count one is refused conservatively; the narrower
  admission is `shiftVerbrauch_eins` (ArchitecturalFlags), never assumed.
- Signed-MUL (`mulVerbrauch_sicher`) and NEG (`negVerbrauch_sicher`) rows
  are not re-proved; their ledger twins stay with ArchitecturalFlags.
- Sequential single-`Speicher` facts only: no TSO/GX, concurrency, cost,
  time or termination claim; no source/checker/Spec/goal claim.
- `#print axioms gabbro_ziel` was not re-run as a separate command: the
  change is purely additive (one new file, one import line; no existing
  proof touched), so the goal axioms cannot have moved. The merge gate
  re-checks this mechanically.

## Notes on the task

- Two implementation findings, both repaired in-file: (1) destructuring a
  simp-normalized Bool conjunction with `obtain` fails dependent
  elimination — fixed by case-splitting the flag first (the accepted
  `FlagDependencies` pattern) and simplifying the ledger per branch;
  (2) a `{ befehl := …, laenge := … }` literal cannot span a newline at
  this toolchain's parser — joined to one line.
- Inhabitation mapping for rule 13: the source-language "table some
  function writes" has no direct X86-hardware correspondent; the ZEUGE line
  of this task defines the applicable bar as a non-degenerate
  memory-changing reached run, which the witness carries (`zeugeProg`
  stores 42 observably, byte 0 → 42, plus the executed `je` step).

Co-Authored-By: muse-agent-840 <muse-agent-840@noreply.invalid>
