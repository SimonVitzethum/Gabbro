# OPUS-BERICHT-CLONE — lane O-1 (clone handoff, K-1)

*Branch `opus/clone-handoff`, worktree `.claude/worktrees/opus-clone`, fisch `gabbro-opus-clone`.
2026-09-18. All builds on fisch; nothing built on the laptop.*

> **Status on master (review 2026-09-21, G11):** only the Rust half and the documents landed
> (merge `a4461b6b`). Part 4/5 below (`CloneHandoff.lean`, the Spec diff (d)/(d2) and its
> proof ripple) is NOT on master although its commits are ancestors of master; see
> SATZKARTE §39 and `messung/review-2026-09-21/G11.md`.

## 0. What K-1 asked, and what this lane delivers

K-1 (`BEFUNDE-bm5.md`, firewall tree): a `syscall` gate can declare the raw clone call,
but "the child starts on the handed stack and must never return into the caller's frame"
had no checked shape — and the emitted helper stub proved it at run time. This lane builds
the checked shape in five parts, all committed on the branch (4 commits). The binding
constraint held: **zero OS data in `crates/` or `grammatik/`** — no clone number, no flag,
no errno, no register name beyond the pre-existing machine file, in code, tests, probes
or comments. The witnesses use `nummer := 1000` and `abi linux` (the template name, 986
precedent), both documented as not-OS-data in every file that carries them.

## 1. Per part

**Part 1 — syntax** (commit `c9e8a02b`). `SyscallDecl.stapel: Vec<Ident>` collects every
`stack` clause between `regs out` and `clobbers` (E4 fixed order; repetition parses so the
second claim falls by name, never at `P001`); `StmtArt::Child(Block)` parses `child { … }`
by the head-word rule (`child = 1;` stays an assignment). No new keyword — `stack`
(`entryextra`) and `child` (`tree`/`kante`) are existing contextual words, so the
vocabulary stays 240/240 and only the rule count moves (EBNF 177 → 178, `childstmt`).
Extended, never loosened: every exhaustive `StmtArt` match gains its arm (walk-through
everywhere; `unterbloecke`/`eigene_ausdruecke`/`eigene_praedikate`/`endet_immer` extended).

**Part 2 — checker** (same commit; new file `crates/gabbro-check/src/clone.rs`, wired behind
`syscall::pass`; `syscall.rs` untouched). Reserves taken: `N446`–`N450`, gifts `1107`–`1111`,
examples `155`–`156` — all measured, none spare-kept.

| code | rule | probe | fires |
|---|---|---|---|
| `N446` | `stack r` bound in `regs in`, kept, answered (one site, four details) | 1107 | once, 0 hints |
| `N447` | second `stack` clause | 1108 | once, 0 hints |
| `N448` | no `return` in the region, no `leave`/`next` past it (marks region-wide) | 1109 | once, 0 hints |
| `N449` | no fall-through: shared `endet_immer` over the unit's `-> never` callees; the return-fault takes precedence (one fault, one refusal) | 1110 | once, 0 hints |
| `N450` | a `child` path runs behind a stack-claiming gate (a faulted gate still counts; its own fault names it) | 1111 | once, 0 hints |

One Satz (`klon.uebergabe`) in the same commit. Positives `155` (handoff) and `156`
(branched tail, both arms ending): 0 errors, 0 hints. `lean_g` refuses `child` as `LG004`
(the handed stack has no G counterpart); footprints, scans and `contains_return` walk it
(a missed child write would clear a race unseen).

**Part 3 — emitter** (commit `db2be4fa`). Outcome: **refusal, not a stub — `C185`.**
Measured reason: the stub template lowers a gate as one C function; after a
stack-switching call the child resumes inside that helper on the handed stack, and the
helper's `return` pops a return address off it. The sound lowering (inline trap, child
entered by jump) is not built; K-1's fork (a) is the C driver outside the language, fork
(b) the unchecked `asm` form. So every `child` block falls at `C185` by name (best-effort
block beside the refusal, so no `cc` verdict changes); the zeugnis books `child` as
`UNZUGEORDNET` (the breaking precedent). No `emit.rs` conflict occurred (master static at
`2cc7b4ff`, no rebase needed). Extra take, reported: `C185` + gift `1112` (`-- erwartet:
C185`, the 155 shape checker-clean) beside the reserved ranges — renumber at review if
the plan says otherwise.

**Part 4 — Lean model** (commits `2244babf`, `cde18e25`; new file
`grammatik/Grammatik/CloneHandoff.lean`, imported into `Grammatik.lean` only;
`Syntax.lean` untouched except the `klon` field). Definitions: `CloneAbi` (+`good`,
`cloneAbiGoodB`, `cloneAbiGoodB_sound`, legs `cloneStack_bound/notOut/notClobber`),
witnesses `cloneWitness[Abi]` (good/decided/sound/first leg) + `cloneBadWitness`
(`rax` handed, fails red); run level `isEntryReturn`, `ChildNoReturn` (no entry-`rueck`
in the child log), `CloneHandoff`, `CloneAssume` ((d2) over every reached run),
`CloneStart` ((d) population duty); laws `cloneHandoff_empty`/`cloneAssume_empty`/
`cloneStart_empty` + joint `cloneHandoff_start` (start machine, arbitrary gates,
reflexive run — the entry logged nothing but its `eintritt`). Axioms propext at most
throughout. CUTS in-file: no `Ziel` leg follows here (stub correspondence is §2 work);
`D.klon` filled by hand models only (exporter `LG004`, `Akzeptiert` decides nothing —
like 208's vacuous components, but with nothing to pin against); the handed stack has no
G counterpart (G is address-free).

**Part 5 — Spec diff** (commit `cde18e25`). `Deklaration.klon` (default `[]`, `mitRuhe`
maps entries to `some`); `Laufzeit.klon` (entries ≠ starts); `GabbroZiel` gains
`CloneAssume` (d2, assumed like the start, unused by the legs). Review package updated
(premise lists, NEW-here, question 2). Ripple, all gateless: `laufzeit_initRuhe`/`voll`
take the population hypothesis (`cloneStart_empty` at the four call sites);
`Schlusssatz104`'s `with` maps `klon`; `Schlusssatz124`'s `laufzeit_w` holds vacuously;
every `gabbro_ziel` application passes `cloneAssume_empty`; `schlusssatz` + the `Bruecke`
copy gain the (d2) conjunct. **`#print axioms gabbro_ziel` exactly
`[propext, Classical.choice, Quot.sound]`** (re-measured on the merged tree).

Docs: `SYNTAX.md` §12.1 + §1 rules + counts (§12.1 prose, `syscalldecl`/`stmt`/`childstmt`,
178-rule cell); `SATZKARTE.md` §39; `PLAN-SYSCALL.md` §4 note; `zaehle-gifttreffer.py`
comment (1112 joins the emitter-code class).

## 2. Last build results (fisch, exact lines)

- `lake build`: green, 281 jobs, no error, no `sorryAx`.
  `gabbro_ziel depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `cargo test --no-fail-fast`: **1176 passed, 0 failed** — zero corpus diff besides the
  8 new files (5 gifts + 1112 + 155 + 156).
- `pruefe-syntax.sh`: `EBNF: 178 Regeln definiert, 0 offen`; `Wortschatz: 240/240`;
  `SYNTAX: ALL PASS` (the trailing `Warnungen` abort is a pre-existing PATH issue:
  `cargo build --tests` exit 127 without `$HOME/.cargo/bin` on PATH).
- `pruefe-saetze.py`: exit 0 — `423 Kennungen, 175 Saetze, 55 ohne Satz, 0 erfunden`
  (MARKE 55 holds; my 6 codes covered).
- `pruefe-kennungen.py`: ALL PASS. `pruefe-grammatiktafel.py`: `0 von 240 UNGEDECKT`.
  `pruefe-konstrukte.py`: `0 ohne Probe, keine neue`.
- `zaehle-gifttreffer.py`: 729 files (669 booked + 60 drift incl. my 6 — merger re-books);
  verdeckt 41, none mine; FEHLT 5 → 6 (1112 joins 850–854, booked in the tool comment).
- Emission: all 8 new files refused at CLI level → **MARKE_EMIT / MARKE_EMIT_G unchanged**.
- `pruefe-englisch.py`: RAT broken (37 vs 26 Zubringer, 5 vs 2 Meldungen) — **pre-existing**,
  all hits in `gegenbeispiel`/`lean_g`/`main`/`lib`/`namen`/old `saetze` lines, none in my
  files (verified by grep for clone/child/C185/N44).

## 3. Open items

1. **The lowering** (inline trap, child entered by jump) + its `CForm` correspondence lemma
   instead of `C185`/`AxCorr` — translation-validation §2 work; K-1's forks (a)/(b) are the
   alternatives. Until then no checked handoff runs.
2. **The spill-read rule**: a `child` block reading caller-frame state (spilled locals) is
   unchecked — no diagnostic code left in my reserves. Next lane mints it (checker dataflow
   over `benutzte_namen` vs caller scope) or the outlining design moots it.
3. **`D.klon` from source**: the exporter refuses `child` (`LG004`); filling the gate list
   (which `Ax`, which entry `Fn`) is exporter/§1-residue work. `Akzeptiert` decides nothing.
4. **A `Ziel` leg for the child** from (d2) — needs 1 + 3 (stub correspondence).
5. Renumbering: gift `1112` + `C185` beside the reserved blocks, at review discretion.
6. `pruefe-emission.sh` full run + `abnahme.py --voll` re-measure after merge (merger);
   `MARKE_PROBEN` (669 → 729 incl. drift) and `MARKE_VERDECKT` re-book by merger.

## 4. What I believe is wrong in this brief

- **Part 3 as specified ("the clone stub") is unbuildable soundly**, and the brief's own
  escape hatch ("if emit.rs conflicts, report instead of forcing") does not cover the real
  failure mode, which is semantic, not textual: no conflict occurred (master static), but
  the helper-form stub is provably corrupt for stack-switching gates. I refused (`C185`)
  instead of emitting. If the intent was "emit the stub anyway", that trades safety for
  green and I recommend against it.
- **The reserves were one code short of the honest shape**: `N446`–`N450` cover the checker,
  but the emitter refusal needs its own code (`C185`) and its own probe (`1112`). The brief
  lists parts 2 and 3 as if the N-reserve covers both; it cannot.
- **"Extend premise (d) Laufzeit (thread creation)"** reads as if the handoff fits the
  init-level predicate; it does not (the init-statable content is vacuous except population
  disjointness). I extended the premise GROUP (d): `Laufzeit.klon` + `CloneAssume` (d2).
  If the intent was a single-field change, the run-level duty has nowhere to live.
- Minor: the fisch `programmlogik/.lake` hardlink seed worked as documented (0 extra disk);
  the `lake env lean` direct-file check creates an ignored `lake-manifest.json` on fisch —
  harmless, but `lake build` is the check that counts.

## 5. Branch state

`opus/clone-handoff`: `2cc7b4ff` + `c9e8a02b` (parts 1+2) + `2244babf` (Lean skeleton) +
`cde18e25` (parts 4+5) + `db2be4fa` (part 3) + docs/report (to commit). Never merged to
master, never force-pushed. Ready to push to origin when confirmed.
