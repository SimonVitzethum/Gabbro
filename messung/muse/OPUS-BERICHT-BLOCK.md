# The correspondence certificate gets its BLOCK structure — `if`, `let` of a call, `traverse`

*Opus lane, 2026-09-15. Branch `opus/korrok-block`, base `edaca064`. Files:
`grammatik/Grammatik/KorrespondenzAllg.lean` (the staged check and its soundness),
`grammatik/Grammatik/KorrespondenzBlockZeuge.lean` (new: two fixtures and ten probes),
`grammatik/Grammatik.lean` (one import), `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §6.5/§6.7,
`dokumente/SATZKARTE.md` §30, this report. Every Lean build on `ki-pc-fisch-101`, directory
`gabbro-opus-blk`.*

**The one sentence.** `korrOk` now reads rows that carry OTHER ROWS — the C `if`/`else`, the
`traverse` header, and the call whose answer is bound — each over a lemma that was already
proved; **the chain count did not move and could not have moved**, because the binding sieve is
(a), the Lean parser and elaborator. *Arms added and chain count are two numbers, and this
report keeps them apart.*

---

## 1. The finding, verified

`OPUS-BERICHT-KORROK.md` §4 item 1 and PLAN §6.5 said: *"`scorr_ite` and `scorr_traverse` are
proved; what is missing is the recursion, not a lemma."* **Verified, and it holds for
`bsem_bindCall` too.** Measured by reading `CFormenI.lean`, `CFormenM.lean` and
`KorrespondenzAllg.lean` side by side on 2026-09-15:

| row | Gabbro side | lemma, proved before today | was in `stOk`? |
|---|---|---|---|
| `GRow.ite cc tRows eRows` | `Stmt.ite c t e` | `scorr_ite` (CFormenI:1135) | no |
| `GRow.forTrav x t hi body m'` | `Stmt.traverse tb inv body` | `scorr_traverse` (CFormenI:1879) | no |
| `GRow.call fc args (some (y, τc))` | `Block.bindCall …` | `bsem_bindCall` (CFormenM:449) | no |

All three fell through `stOk`'s `_ => false`. The obstacle was that their Gabbro side is a
`Block`, and `enOk` walks `Endblock` only.

**One correction to the handed-over note.** The note said Lean's structural recursion *"will not
take two functions over `List GRow` in one mutual block"* and proposed instead ONE
self-recursive `blOk` over `List GRow` that handles `ite`/`forTrav` itself. That shape does not
fit: in the `ite` arm `blOk` must recurse on `tRows`, which is a component of the HEAD ROW and
not a sublist, so `List.brecOn` offers no `below` for it. What does fit — and what
`Korrespondenz.lean` has done since it was written (`growRow`/`growsCS`, `rowCXs`/`rowsCXs`,
`rowFreshOk`/`rowsFresh`) — is a mutual over the NESTED pair `GRow` / `List GRow`, and Lean
takes it. **The staging the note asked for is kept in full**; only the shape of the one mutual
is different, and the reason the note gave for avoiding a mutual (the fuel) does not apply to
one that is structural.

## 2. What was added

### 2.1 The staging

    stOk0   the flat arms of before -- no recursion at all
    blOk    a `Block` against a row list, self-recursive on the ROWS
    stOk    stOk0 plus the arms whose row carries rows (`ite`, `forTrav`)
    enOk    unchanged

`stOk` and `blOk` are one `mutual`, `stOk` structural on the `GRow`, `blOk` structural on the
`List GRow`. **Nothing well-founded and no fuel enters the check.** That is not a style
preference: `korrOk` is settled by `decide` in every chain instance, a well-founded definition
does not reduce in the kernel, and O13's second pathology (`SATZKARTE` §29.6) is exactly a
mutual recursion through a FUEL argument — a mutual `Nat.brecOn`, exponential in the fuel, 112 GB
on a seven-token probe. The soundness, by contrast, runs on a plain measure
(`rowSize`/`rowsSize`): **a proof may use a measure, because a proof never reduces.**

### 2.2 The three arms, and what each DECIDES

| row | ends in | decided rather than assumed |
|---|---|---|
| `GRow.ite cc t e` | `scorr_ite` | the condition is the emitted form of the Gabbro condition, and BOTH arms are, row by row |
| `GRow.call fc args (some (y, τc))` | `bsem_bindCall` | the callee's C number is `fnum g`; `y` is fresh (`K.freshB`); the declared C type holds the Gabbro answer type (`declOk`); the callee's map in the certificate IS its C parameter list (`callMapOk`); the arguments are the emitted forms (`argsOk`); and the rows AFTER the binder are read under the pushed map |
| `GRow.forTrav x t (.lit N) rows m'` | `scorr_traverse` | `N` IS the table's count; `x` is fresh and the map well formed; the computation type holds `0 .. N`; `0 ≤ N`; and the body does not write `x` (`hw`, decided on the ELABORATED rows, as `rowsTravOk` does it in `Korrespondenz.lean`) |

**Two deliberate narrownesses, written at the site.**

* **The `traverse` bound must be a literal.** `scorr_traverse` wants `ev hiC st ρ = N` at EVERY C
  state; the only C expression this file can decide that of is `CX.lit`. A header that computes
  its bound is a refusal, not an admission.
* **The loop's budget `m'` is NOT checked.** It is the `forC` step count of the C semantics, and
  the correspondence holds at whatever it is. Saying so is cheaper than pretending to check it.

`blOk` reads four `Block` constructors — `nil`, `cons`, `bind`, `bindCall` — plus the `(void)x;`
pre-row. Everything else is `false`.

**`let x = f(…)` is checked in `blOk` and nowhere else, and that is a statement about the
MODEL**: `Endblock` has no `bindCall` constructor at all, so a function body whose TOP level
binds a call's answer is not expressible. Inside an `if` arm or a loop body it is.

### 2.3 Soundness — nothing new is assumed

`korrOk_fnCorr` and `korrOk_jeder_lauf` are **unchanged in statement** and still hold;
`stOk_sound` keeps its statement too and is now derived from `stOkBl_sound`. `enOk_sound` is
untouched — it calls `stOk_sound`, which is why the new arms are inside the theorem that was
already stated, and not beside it.

The one new proof structure is `stOkBl_sound`: both halves at the same fuel `n`, proved
asymmetrically inside the step — the STATEMENT half at `n+1` uses only the BLOCK half at `n`
(an `if` row is strictly heavier than its arms), and the block half at `n+1` then uses the
statement half at `n+1` for its head row and itself at `n` for the tail. `stOk0_sound` is the
old `stOk_sound` body, generalised over context, locals map and loop label, because `blOk`
reaches it at the contexts of the arms and bodies it descends into.

**No new lemma was needed, and none was written.** Every arm ends in `scorr_ite`,
`scorr_traverse`, `bsem_bindCall`, `scorr_*` of `stOk0_sound`, or a `BlockCorr` constructor.

**Axioms** (`#print axioms`, from the build log): `stOk0_sound`, `stOkBl_sound`, `stOk_sound`,
`blOk_sound`, `enOk_sound`, `korrOk_fnCorr`, `korrOk_jeder_lauf`, `exOk_sound`, `argsTo_of`,
`ecorr_geSwap`: `propext`, `Classical.choice`, `Quot.sound`. `ptrOk_sound`: `propext`,
`Quot.sound`. All ten probes: `propext`, `Quot.sound`. **No `sorry`, no `native_decide`, no new
`axiom`.**

### 2.4 Probes — a positive AND a planted defect for every arm

`KorrespondenzBlockZeuge.lean`, ten theorems, all by `decide`. Two fixtures: `wD` of
`KorrespondenzWeitZeuge.lean` (one table `T` of four `u32` slots, two `u32` parameters in C
locals `0` and `1`), and `cD` — the same declaration with ONE function `g(a : u32) -> u32`,
because `wD` has `Fn := Empty` and a call needs a callee.

| probe | accepted | REFUSED (the planted defect) |
|---|---|---|
| `probe_ite` | `if (a<b) { a=1; } else { a=2; }` | the two branches SWAPPED; a statement dropped from the `then` arm; a statement dropped from the `else` arm; a statement ADDED to an arm; the condition read as the opposite comparison |
| `probe_ite_fremd` | — | an `if` row against a plain assignment, and a plain row against the `if` statement |
| `probe_blOk_void` | `(void)a; a=1;`, and the empty block against `Block.nil` | `(void)` of a local that is no variable's; rows without a block; a block without rows |
| `probe_blOk_let` | `let t = a; a = t;` | the `let` bound to a parameter (not fresh); the `let` bound to a local the FOLLOWING ROW does not read; the wrong bound expression |
| `probe_bindCall` | `let y = g(a); a = y;` | the answer bound to a local the following row does not read; the answer bound to a parameter; the wrong C function number; the wrong argument; the wrong declared C type; the answer DISCARDED (`none` — a different C statement) |
| `probe_bindCall_karte` | — | a callee whose map is not its C parameter list; a callee missing from the certificate |
| `probe_forTrav` | `for (uint32_t v = 0; v < 4; v += 1) { a = 1; }` | the WRONG LOOP BOUND: `5`, `3`, and a non-constant bound; the loop variable taken from the parameters; the body one statement short; one statement too long; the body's statement replaced by a different one |
| `probe_forTrav_hygiene` | — | a loop body that WRITES the loop variable, with the row that MATCHES it — so the refusal is `scorr_traverse`'s `hw` premise and nothing else |
| `probe_forTrav_fremd` | — | a loop row against an `if` statement, and an `if` row against the loop statement |
| `probe_nested` | an `if` INSIDE a `traverse` | the branches swapped at the INNER level; a statement dropped from the inner `then` arm; the outer bound wrong |

`probe_nested` is the one that measures the recursion rather than assuming it: two levels of row
list, and the defect is planted at the inner one.

### 2.5 Coverage, counted against the grammar

| type | constructors | covered BEFORE | covered AFTER |
|---|---|---|---|
| `Stmt` | **27** | 5 (`assignSlot`, `assignDurch`, `assignGlob`, `assignVar`, `call`) | **7** (+ `ite`, `traverse`) |
| `Block` | 17 | **0** — there was no block check at all | **4** (`nil`, `cons`, `bind`, `bindCall`) |
| `Endblock` | 6 | 3 (`ret`, `cons`, `bind`) | 3, unchanged |
| `Expr` | 42 | 27 | 27, unchanged (`exOk` untouched) |

**`Stmt`: 5 of 27 → 7 of 27.** That is the number the task asked for, and it is the number this
lane moved. It is NOT a chain number; see §4.

## 3. The cost, measured — before and after

Peak RSS and wall clock of a DIRECT `lean` run on the file (`/usr/bin/time -v`, all dependencies
freshly built, on `ki-pc-fisch-101`). "Before" is the branch's base `edaca064`, "after" is
`f87de32e`.

| file | wall BEFORE | wall AFTER | peak RSS BEFORE | peak RSS AFTER |
|---|---|---|---|---|
| `KorrespondenzAllg.lean` | 14,15 s | **14,62 s** (+3,3 %) | 3 475 724 kB | **3 770 292 kB** (+8,5 %) |
| `KorrespondenzWeitZeuge.lean` (§28's probes) | 0,34 s | **0,33 s** | 598 368 kB | **615 896 kB** (+2,9 %) |
| `KorrespondenzBlockZeuge.lean` (new) | — | **0,31 s** | — | **607 504 kB** |
| `Kette108.lean` (`korrOk … = true` by `decide`) | 4:37,54 | **4:33,90** (−1,3 %) | 72 888 492 kB | **72 925 028 kB** (+0,05 %) |
| `CText108.lean` (two `korrOk … = false` by `decide`) | 16,89 s | **16,42 s** (−2,8 %) | 2 983 232 kB | **3 001 404 kB** (+0,6 %) |

As `lake` jobs the same two files read 278 s → 282 s and 16 s → 16 s; a THIRD `Kette108` build,
after a comment-only edit, took 306 s on a busier machine. *The `lake` job time is the noisier
instrument of the two — it is the direct `lean` runs above that carry the comparison.*
`Kette104` (the other
chain that settles a `korrOk` by `decide`) builds green in **275 s** on this branch; *no
before-value was taken for it in this directory, so it is deliberately not in the comparison —
a number without its pair is not a comparison.*

**Reading of the numbers.** The only file that got measurably dearer is the one that gained the
proofs; its 295 MB are the new soundness theorem, not the check. **The two files that SETTLE
`korrOk` BY `decide` did not move**: +0,05 % and +0,6 % peak RSS, and both slightly faster on the
clock — inside the run-to-run noise of a 70 GB elaboration. *That is the point of keeping the
recursion structural*: the kernel work of `decide` on a certificate with no `ite`/`forTrav` rows
is the same work it was, because the extra arms are matches that do not fire.

**One measurement was thrown away and re-run, and that is worth booking.** The first `after` run
of `Kette108.lean` came back `exit=137` at 57 GB — the kernel killed it, because another lane on
the same machine held 63 GB at the same moment. *A build that dies of memory is not a finding*
(CLAUDE.md); the number in the table is the re-run, taken when the machine was free.

## 4. The chain count — measured, and unchanged

**Measured on `ki-pc-fisch-101`, directory `gabbro-opus-blk`, with this branch built green
(`lake build`: 249 jobs; `Kette104` 275 s, `Kette108` 306 s, both at ~72 GB) and `cargo build`
green:**

```
instrumente/zaehle-kette.py --lean --dateien korpus-blk.txt
  sieve totals: (a) 2  (b) 10  (c) 15  (d) 60  (e) 2 of 113
  first stopping sieve of the programs without a closed chain: (a) elab: 91, (a) parse: 20
== CHAIN COUNT: 2 of 113 programs have a CLOSED chain ==
```

**CHAIN COUNT 2, and every sieve total the same as before the branch** — `(a) 2 (b) 10 (c) 15
(d) 60 (e) 2`, and the same 91 / 20 split of where the open programs stop, figure for figure
what `OPUS-BERICHT-KORROK.md` §3 measured this morning. The two closed chains are the two that
were closed before, `beispiele/104-referenz.gab` (`kette_104`) and
`beispiele/108-disjoint-start-locks.gab` (`kette_108`). (`korpus-blk.txt` is the population
written out explicitly — the 113 flat `beispiele/*.gab` — because `korpus.py` cannot ask `git`
on an rsynced worktree and would otherwise fail open.)

**Why it could not have moved, stated so it can be checked.** A chain is closed only for a
program with a Lean-checked instance of `schlusssatz`, whose FIRST field is parse fidelity
through `uebersetzeAllg`. 111 of 113 corpus programs never produce a `UProg` at all — they stop
at sieve (a), the Lean parser (20) or the elaborator (91) — so no certificate is ever asked of
them, and widening what the certificate ACCEPTS changes nothing for them. The two that do pass
(a) already had checking certificates. **A new arm can raise the chain count only after sieve (a)
admits a program that uses the form**, and two Muse lanes are widening exactly that.

**And the other direction was checked too, which matters more.** `CText108.lean` asserts
`korrOk … = false` for two MUTATED certificates of 108; both still read `false` after the
widening, and `Kette108.lean`'s `korrOk … = true` still reads `true`. A check that got wider
must not have got wrong.

***Arms added are not chain progress, and are not presented as such.***

## 5. Guardians, before and after

The text guardians that read `grammatik/` and the ledgers were each run TWICE from this
worktree — once with `master`'s versions of the three changed files in place, once with the
branch's. **Eleven of twelve outputs are BYTE-IDENTICAL**, exit codes included
(`pruefe-zahlen.py` 1/1, `pruefe-termidentitaet.py` 1/1, `pruefe-praemisse.py` 2/2,
`pruefe-deckung.py` 0/0, `pruefe-widerruf.py` 0/0, `pruefe-todo.py` 1/1,
`pruefe-grammatiktafel.py` 0/0, `pruefe-cformen.py` 0/0, `miss-grammatikdeckung.py` 0/0,
`zaehle-absagen.py` 0/0, `pruefe-waechter.py` 1/1). The red ones were red on `master` for
reasons this branch does not touch.

The twelfth moved, and for the same reason it moved for §28:

* **`pruefe-gestalt.py`: 188 → 189 Lean files, 185 → 186 findings.** The new file
  `KorrespondenzBlockZeuge.lean` has no line in that instrument's ratchet — whose `ERWARTET`
  lists **23 files and nothing else**. **165 of the 188 files were already unbooked before this
  branch** (and 20 further findings are booked files whose figures have moved), so the
  instrument is red on `master` for reasons that have nothing to do with this branch: after it,
  166 unbooked and the same 20. Adding one line for this file
  alone would not change the verdict and would make the ratchet look like a list it is not. *The
  figure is not in `messung/KENNZAHLEN.md` and `pruefe-zahlen.py` does not read it, so there is
  no ledger entry to move; it is booked here.*

**And this document enlarges the surface it reports on.** `pruefe-zahlen.py` re-run with the
three documents of step 4 in place: **the same 24 findings, the same exit code 1**, and two
figures moved, both because the tree gained ONE document:

* *"Files the revocation guardian reads"*: the run says **543 → 544** (and
  `pruefe-widerruf.py` itself prints the same 543 → 544 over the same 13 entries).
  `KENNZAHLEN.md` books it as 299, so it was a finding before this branch and is the same
  finding after — the booked figure did not move, the population did.
* The unwatched surface: **816 cells in 109 files → 817 in 110**.

`pruefe-grammatiktafel.py` differed only in a printed wall-clock time (16,3 s vs 16,8 s) — not a
number. Everything else in the twelve was byte-identical a second time.

*A report that states numbers enlarges the surface it is reporting on; that is what that counter
is for.*

## 6. What stays open, and why

Each is written at the site as well (`KorrespondenzAllg.lean`, CUTS).

1. **A `traverse` whose bound is not a literal** — §2.2. Deciding `ev hiC = N` for a computed
   bound needs a C-expression evaluator inside the check, which is a different piece of work from
   this one.
2. **`retry`, `forever`, `locks`, `breaking`, `onOption`, `onTag`, `onGrund`** — block statements
   with no row in `GRow` and no path in the printer, so `blOk` never meets them. Adding a row
   type is an emitter change, and the emitter is another lane's.
3. **`bindCallInd`, `bindCallElse`, `bindAxiom`, `regLies`, `regLiesElse`, `awaits`, `exchange`,
   `narrow`, `pruefung`, and the four float binders** — the other 13 `Block` constructors. Each
   would need its own row shape; none is one line.
4. **`!=`, `(T)(e)` as a C wrapper, `_Atomic` globals, floats** — unchanged from §28's list, with
   the reasons unchanged.
5. **The printer is still narrower than the check** (`gcx`, `corrlean.rs`): it prints no `if`, no
   loop and no call-with-destination, so no certificate can exercise the three new arms outside
   the probes. **That is Rust work and out of this lane's scope** (the prompt: do not touch
   `emit.rs`; `corrlean.rs` was left alone to keep the diff one-sided). *Until it is done, these
   arms are proved and probed but not exercised by a printed certificate — which is exactly what
   §5 of the previous report said about the expression arms, one layer up.*

## 7. Commits

| step | commit | what |
|---|---|---|
| 1 | `ed598fee` | `if`/`else`: the staging (`stOk0`, `blOk`, `stOk`), `stOkBl_sound`, `rowSize`, and the probes over `wD` |
| 2 | `eda2cf31` | `let y = g(a);`: the `bindCall` arm, its soundness through `bsem_bindCall`, the fixture `cD` and eight planted defects |
| 3 | `f87de32e` | `traverse`: the `forTrav` arm with bound, freshness and body hygiene decided, its soundness through `scorr_traverse`, the probes and the nested probe |
| 4 | this one | PLAN §6.5/§6.7, SATZKARTE §30, this report |

Branch `opus/korrok-block`. **Not merged, not pushed.**
