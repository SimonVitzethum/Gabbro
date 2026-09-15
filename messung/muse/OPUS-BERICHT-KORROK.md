# The correspondence certificate `korrOk`, widened — and what that did NOT do to the chain count

*Opus lane, 2026-09-15. Branch `opus/korrok-weit`, base `cf9cb77c`. Files:
`grammatik/Grammatik/KorrespondenzAllg.lean` (the check and its soundness),
`grammatik/Grammatik/KorrespondenzWeitZeuge.lean` (new: the probes), `grammatik/Grammatik.lean`
(one import). Every Lean build and every `cargo` run on `ki-pc-fisch-101`, directory
`gabbro-opus-ko`.*

**The one sentence.** `korrOk` gained **21 expression arms and 2 statement arms**, all of them
over lemmas that were already proved; **the chain count did not move and could not have moved**,
because the binding sieve is (a), the Lean parser and elaborator, and 111 of 113 corpus programs
stop there before any certificate is asked for. *Arms added and chain count are two numbers, and
this report keeps them apart.*

---

## 1. The finding that was handed over, verified

`OPUS-BERICHT-GRAMMATIK-EMIT.md` §5.3 item 1 said: *"`exprOk` is narrower than its own lemma
stock."* **Verified, and it holds for `korrOk`'s `exOk` too, more widely than stated.** Measured
by reading `CFormenI.lean`, `CFormenM.lean` and `KorrespondenzAllg.lean` side by side on
2026-09-15:

| family | lemma, proved before today | was in `exOk`? |
|---|---|---|
| `add sub mul` | `ecorr_add`, `ecorr_sub`, `ecorr_mul` | no |
| `div rem sdiv srem` | `ecorr_div`, `ecorr_rem`, `ecorr_sdiv`, `ecorr_srem` | no |
| `band bor bxor shl shr` | `ecorr_band`, `ecorr_bor`, `ecorr_bxor`, `ecorr_shl`, `ecorr_shr` | no |
| `lt le eq` (and `>` via `Zucker.gt`) | `ecorr_lt`, `ecorr_le`, `ecorr_eq`, `ecorr_gt` | no |
| `und oder nicht` | `ecorr_und`, `ecorr_oder`, `ecorr_nicht` | no |
| `wahr falsch` | `ecorr_wahr`, `ecorr_falsch` | no |
| `glob` (plain) | `ecorr_glob` | no |
| `assignGlob` (plain) | `scorr_assignGlob` | no |
| `x += / -= / &= / |=` | `scorr_plusGleich` … `scorr_oderGleich` (all four `scorr_assignVar`) | no |

**Two corrections to the handed-over list**, both measured:

1. **`>=` is NOT the cheap `.cmp .ge` arm the note suggests, and `>` is not an arm at all.**
   Gabbro has no `gt`/`ge` constructor: `Zucker.gt a b` is `Expr.lt b a` and `Zucker.ge a b` is
   `Expr.le b a` (`Zucker.lean`:113,115). So both live INSIDE the `lt`/`le` arms as a second C
   row shape with the operands swapped — which is what this lane built. `ecorr_gt` existed;
   `ecorr_geSwap` is the ONE new lemma of this lane, and it is `ecorr_cmp` with its operator
   fact (`fun _ _ => rfl`), no new model reasoning.
2. **`!=` is NOT cheap.** `Zucker.ne a b` is `Expr.nicht (Expr.eq a b)`, so the arm would have to
   look THROUGH the negation at operands whose induction hypotheses are not available in an arm
   whose pattern is `nicht a`. It stayed out, with the reason written at the site (CUTS). The
   Rust printer refuses `!=` today anyway (`corrlean.rs:1474`), so no certificate can carry the
   row.
3. **`bnot` needs no arm, but only at one of its two C spellings.** `Zucker.bnot w h0 hw a` is
   `Expr.bxor w … a (.lit (2^w-1))` (`Zucker.lean`:122), so the new `bxor` arm covers it **when
   the C text is `a ^ (2^w-1)`**. `ecorr_bnot` proves the OTHER spelling, `(T)~(T)(x)` — a
   `CX.cast` of a `CX.cpl` — and that one needs the `cast` wrapper arm, which is item 4 of §4.
   Booked as covered-in-part, not as covered.

## 2. What was added

### 2.1 Arms — 21 expression, 2 statement

`exOk` (Gabbro `Expr` constructors newly accepted): `wahr`, `falsch`, `glob`, `add`, `sub`,
`mul`, `div`, `rem`, `sdiv`, `srem`, `band`, `bor`, `bxor`, `shl`, `shr`, `lt`, `le`, `eq`,
`und`, `oder`, `nicht` — **21**. Counted as C node shapes it is **23**, because `lt` accepts
both `.cmp .lt t ca cb` and `.cmp .gt t cb ca`, and `le` both `.cmp .le` and `.cmp .ge`.

`stOk`: `assignGlob` against `GRow.storeGlob` (**1 new statement constructor**), and `assignVar`
against the additional row `GRow.setOp` (**1 new row shape**, the four `Zucker` compound
assignments — `growRow (.setOp x τc op t ce)` is literally `.set x τc (.bin op t (.var x) ce)`,
the same C statement the `setVar` row elaborates to).

**Coverage, counted against the grammar:** `Expr` has 42 constructors; `exOk` covered 6
(`lit`, `var`, `weiter`, `slot`, `durch`, `ptrOf`) and now covers **27**. `Stmt` has 27
constructors; `stOk` covered 4 (`assignSlot`, `assignDurch`, `assignVar`, `call`) and now covers
**5** (`ret` enters through `enOk`, not `stOk`).

### 2.2 Soundness — nothing new is assumed

`korrOk_fnCorr` and `korrOk_jeder_lauf` are unchanged in statement and still hold: every new arm
of `exOk`/`stOk` gets one helper theorem next to it (`exOk_add`, `exOk_sub`, …, `exOk_glob`,
`exOk_nicht`; `randOk_sound`, `sgnMin_sound`), each of which takes **the arm's own `match` as its
hypothesis** — so the check's text and the proof's text cannot drift apart — and ends in the
existing `ecorr_*`/`scorr_*` lemma. The side conditions those lemmas carry are now DECIDED
rather than assumed:

* `randOk t l1 h1 l2 h2` — the C computation type holds BOTH operand ranges. This is the
  signed/unsigned pitfall (`-1 < 1u`) turned into a sieve, and it is also what makes C's
  conversions keep the Gabbro numbers.
* the result-range condition (`M104`) at `+`, `-`, `*` and `<<`;
* `sgnMin_sound` at `sdiv`/`srem`: the type is unsigned, or the dividend's range starts above
  the type's minimum — which is exactly what excludes `INT_MIN / -1` (C11 6.5.5p6, undefined).

**Axioms** (`#print axioms`, from the build log): `exOk_sound`, `stOk_sound`, `enOk_sound`,
`argsTo_of`, `korrOk_fnCorr`, `korrOk_jeder_lauf`, `ecorr_geSwap`: `propext`, `Classical.choice`,
`Quot.sound`. `ptrOk_sound`: `propext`, `Quot.sound`. No `sorry`, no `native_decide`, no new
`axiom`.

### 2.3 Probes — a positive AND a planted defect for every arm

`KorrespondenzWeitZeuge.lean`, a fixture `wD` (one table of four `u32` slots, a plain global `G`
and an `_Atomic` `A` at adjacent block numbers, the exporter's map `vm = [0, 1]`). 14 probe
theorems, all by `decide`, all `propext`/`Quot.sound`:

| probe | accepted | REFUSED (the planted defect) |
|---|---|---|
| `probe_wahr` | `true ↦ 1`, `false ↦ 0` | `true ↦ 0`, `false ↦ 1` |
| `probe_add` | `.bin .add u64` | `u32` (too narrow for the sum), `.bin .sub`, operands swapped |
| `probe_sub` | `.bin .sub i64` | `u64` (the difference is negative), `.bin .add` |
| `probe_mul` | `.bin .mul u64` | `u32`, `.bin .add` |
| `probe_div_rem` | `.bin .div u32`, `.bin .mod u32` | the other operator, `u8` |
| `probe_sdiv_srem` | `i64` at a dividend above `INT64_MIN` | the SAME expression at the full `i64` range (`INT_MIN / -1`), the other operator |
| `probe_bit` | `.band`, `.bor`, `.bxor` at `u32` | each against a different bitwise operator |
| `probe_shift` | `.shl`, `.shr` at `u32` | each against the other shift |
| `probe_cmp` | `<` and `>` (swapped), `<=` and `>=` (swapped), `==` | `>` / `>=` **without** the swap — the opposite comparison —, `<=` for `<`, `!=` for `==` |
| `probe_cmp_typ` | `<` at `i64` | `<` at `i32` (does not hold `u32`'s upper end) |
| `probe_bool` | `&&`, `||`, `!` | each against the wrong C connective; `!` against the bare operand and against `>=` |
| `probe_glob` | `G` at block 0, `uint32_t` | block 1, `uint16_t`, and the `_Atomic` `A` in BOTH spellings (`ld` and `ald`) |
| `probe_setOp` | `setOp 0 … .add u32` | local `1`, operator `.sub`, type `u8` |
| `probe_assignGlob` | `storeGlob 0 … (.var 0)` | block 1, `uint16_t`, the other parameter as the value, and the same statement on `_Atomic` `A` |

### 2.4 Witness (rule 13)

`ecorr_geSwap_zeuge`: the one new lemma, instantiated THROUGH `exOk_sound` on a C state whose
two locals differ, at **both** answers — the same C node `b >= a` evaluates to `1` under
`(a, b) = (5, 9)` and to `0` under `(9, 5)`. *A witness that showed only the `true` case would
not distinguish the lemma from one that always answers `1`.*

## 3. The chain count — measured, and unchanged

**Measured on `ki-pc-fisch-101`, directory `gabbro-opus-ko`, with this branch built green
(`lake build`: 241 jobs, `Kette104` 408 s, `Kette108` 284 s):**

```
instrumente/zaehle-kette.py --lean --dateien korpus.txt
  sieve totals: (a) 2  (b) 10  (c) 15  (d) 60  (e) 2 of 113
  first stopping sieve of the programs without a closed chain: (a) elab: 91, (a) parse: 20
== CHAIN COUNT: 2 of 113 programs have a CLOSED chain ==
```

**CHAIN COUNT 2, before and after.** The two closed chains are the two that were closed before:

| program | state | instance |
|---|---|---|
| `beispiele/104-referenz.gab` | `[YYYYY]` CLOSED | `kette_104` in `Kette104Satz.lean`, applied there |
| `beispiele/108-disjoint-start-locks.gab` | `[YYYYY]` CLOSED | `kette_108` in `Kette108.lean`, applied there |

**Where the other 111 stop — every one of them at sieve (a), none at (b)–(e).** Measured by
evaluating `uebersetzeAllg` in Lean over each file (`.lake/zaehle-kette/Messung.lean`, 113 lines
of answer):

| sieve | stage | programs | the reasons, counted |
|---|---|---|---|
| (a) | the Lean **elaborator** | **91** | 70 `Gegenstand ohne G-Form`, 13 `Einheit ohne Tabelle`, 7 `Typ unbekannt: bool`, 1 `Requires-Klausel ohne G-Form` |
| (a) | the Lean **parser** | **20** | 10 `reserved head forall`, 4 `wanted ;`, 2 `wanted {`, 2 `@version expected`, 1 `fn without body`, 1 `expression expected` |
| (b)–(e) | `lean-g`, `certificate`, the C-form census, the printed `KCert` | **0** | no program reaches any of them FIRST; their per-program columns stand as diagnostics only |

**Why the widening could not move the count, stated so it can be checked.** A chain is closed
only for a program with a Lean-checked instance of `schlusssatz`, and the FIRST field of a
`Kette` is parse fidelity through `uebersetzeAllg`. 111 of 113 programs never produce a `UProg`
at all, so no certificate is ever asked of them — widening what the certificate accepts changes
nothing for them. The two that do pass (a) already had checking certificates. **A new arm can
raise the chain count only after sieve (a) admits a program that uses the form** (Muse lanes 199
and 200 are widening the elaborator and the parser). *This is the multiplicative-coverage point
of PLAN §3, seen from the other side: a pillar raised alone raises nothing.*

**The population grew from 111 to 113** since PLAN §6.3 was written: `132-raum-am-zeiger.gab` and
`133-nur-gruende-und-ein-format-am-pfeil.gab` (commit `3d337c7f`, same day). Both stop at
elaboration (`Einheit ohne Tabelle`, `Gegenstand ohne G-Form`), which is why the elaborator count
reads 91 where the plan reads 89 and the table count 13 where the plan reads 12. **No figure in
this table moved for a reason that has anything to do with this branch.**

**A finding about the counter, not about the tree.** `zaehle-kette.py --lean` aborts with
*"the Lean measurement of column (a) did not answer for every program -- this run measures
nothing about (a)"* when `lake` is not on `PATH`: its `umgebung()` does not add `~/.elan/bin`, and
the message names the SYMPTOM (no answer) rather than the CAUSE (no `lake`). The run then exits
`2` and prints no sieve totals at all — *a guardian that aborts reads like one that found
something.* Run it with `export PATH=$HOME/.elan/bin:$PATH` on `ki-pc-fisch-101`. Not repaired
here: the instrument is outside this lane's diff, and a one-line `PATH` fix in a guardian
belongs in a commit that can re-measure every guardian that shares `umgebung()`.

## 4. What stays open, and why

Each of these is written at the site as well (`KorrespondenzAllg.lean`, CUTS).

1. **`if`/`else` (`GRow.ite`) and `traverse` (`GRow.forTrav`).** `scorr_ite` and
   `scorr_traverse` are proved; the arm is NOT one line, because both rows carry a ROW LIST and
   the Gabbro side is a `Block`, which this file never walks — `enOk` walks `Endblock` only. The
   obstacle is the recursion, not a missing lemma, and it must stay **structural**: `korrOk` is
   settled by `decide` in every chain instance, and a well-founded definition does not reduce in
   the kernel. **A concrete way through, found while writing this:** do not make `stOk` and a
   block check mutual (Lean's structural recursion will not take two functions over `List GRow`
   in one mutual block); stage them — `stOk0` with today's flat arms, then a self-recursive
   `blOk` over `List GRow` that handles `ite`/`forTrav` itself and delegates every other row to
   `stOk0`, then `stOk = stOk0` plus two arms through `blOk`, then `enOk` unchanged.
2. **`let x = f(…)` (`bindCall`).** `bsem_bindCall` is proved, but `bindCall` is a `Block`
   constructor and NOT an `Endblock` one, so it cannot occur in a body `korrOk` walks at all
   until item 1 exists. The Rust printer refuses it too (`corrlean.rs`: "`let … =` call: result
   type needs the callee signature").
3. **`!=`** — §1 item 2.
4. **`(T)(e)` as a C wrapper** (`CX.cast`, `ecorr_cast` proved): the recursion would shrink the C
   side while the Gabbro side stands still, which is neither argument's structural descent.
5. **`_Atomic` globals**, read and stored (`ecorr_globAtomar`, `scorr_assignGlobAtomar` proved):
   both are observations and `GRow` has no atomic row. The check REFUSES them — see
   `probe_glob` and `probe_assignGlob`.
6. **Floats** have no `ecorr_*` at all, and `CX` has no float operand a `GRow` could carry
   (`OPUS-BERICHT-GRAMMATIK-EMIT.md` §5.3 item 6). Nothing was invented here.
7. **`neg`, `leseBytes`, sums, options, reasons, quantifiers, `locks`, `forever`, `retry`,
   device and foreign forms**: no arm, and no cheap one.
8. **The printer is now NARROWER than the check.** `gcx` (`corrlean.rs`:1464) prints only
   `+ - *` and `== < <= >`; `/ % & | ^ << >>`, `&& || !`, `true`/`false`, plain globals and
   `storeGlob` have no printer path, so no certificate can exercise those arms outside the
   probes. **That is Rust work and was out of this lane's scope** (the prompt: do not touch
   `emit.rs`; `corrlean.rs` was left alone to keep the diff one-sided).

## 5. Guardians, before and after

Measured from this worktree, the guardians that read `grammatik/` (`pruefe-termidentitaet.py`,
`-gestalt`, `zaehle-pflichten`, `zaehle-absagen`, `pruefe-waechter`, `zaehle-c-formen`,
`pruefe-cformen`, `miss-grammatikdeckung`, `pruefe-praemisse`, `pruefe-deckung`,
`pruefe-grammatiktafel`, `pruefe-gleitkomma`, `zaehle-empfindlichkeit`,
`pruefe-uebersetzerfamilie`, `nachpruefer`), each run twice — once with the branch stashed, once
with it applied. **Every exit code identical.** Exactly one output moved:

* **`pruefe-gestalt.py`: 184 → 185 Lean files, 181 → 182 findings.** The new file
  `KorrespondenzWeitZeuge.lean` has no line in that instrument's ratchet. **Reason: the ratchet
  `ERWARTET` lists 25 core files and nothing else** — 161 of the 184 files were already
  unbooked before this branch, and the instrument is red on `master` for that reason. Adding one
  line for this file alone would not change the verdict and would make the ratchet look like a
  list it is not. *The figure is NOT in `messung/KENNZAHLEN.md` and `pruefe-zahlen.py` does not
  read it, so there is no ledger entry to move; it is booked here.*
* `pruefe-grammatiktafel.py` differed only in a printed wall-clock time (16.2 s vs 16.4 s) —
  not a number.

`pruefe-zahlen.py` was run twice as well (documents stashed, documents applied). Exit code 1
both times, the same 38 findings both times, all of them about Rust and corpus figures this
branch does not touch. **Two numbers moved, both because the tree gained ONE document:**

* *"Dateien, die der Widerrufwaechter liest"*: the run says **541 → 542**. `KENNZAHLEN.md` books
  it as 299, so it was a finding before this branch and is the same finding after — the booked
  figure did not move, the population did, by `messung/muse/OPUS-BERICHT-KORROK.md`.
* the unwatched surface: **812 cells in 107 files → 815 in 108**, the three bold figures of this
  report in this report. *A report that states numbers enlarges the surface it is reporting on;
  that is what that counter is for.*

`pruefe-englisch.py` is red on this branch and was red before it: it reads `crates/*/src/*.rs`
only, and this branch touches no Rust. Not this lane's finding.

## 6. A measurement note that cost real time

**`lake build` has no `-j` and the two chain files need ~72 GB EACH.** On a machine with 110 GB
where another agent and two Muse lanes were also building, the default parallelism put
`Kette104` and `Kette108` side by side and the kernel killed one of them: `Lean exited with code
137`, which reads exactly like a failed proof and is not one. *A build that dies of memory is
not a finding.* The cure used here: build `Grammatik.Kette104` and `Grammatik.Kette108` as
separate targets, in order, with retries, before the full `lake build`. Times measured in this
directory: **Kette104 451 s, Kette108 ~400 s**, both at ~72 GB resident (`OFFEN.md` O13).

## 7. Commits

| step | commit | what |
|---|---|---|
| 1 | `534bd484` | `korrOk` widened to its own lemma stock: the 21 expression arms, the 2 statement arms, their soundness helpers, `ecorr_geSwap`, the rewritten CUTS |
| 2 | `e3d30a1c` | the probes: the fixture, a positive probe and a planted defect for every arm, the witness of `ecorr_geSwap` |
| 3 | this one | PLAN §6.2/§6.5, SATZKARTE §28, this report |

Branch `opus/korrok-weit`. **Not merged, not pushed.**
