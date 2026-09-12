# MUSE-REPORT-114: syscall corpus — a buffered writer over `write` (PLAN-SYSCALL.md lane S7)

Branch: `muse/114`. Gabbro + Rust lane. No Lean changes (`./lean-bau` green, see §7).
No new checker/emitter codes, no new probes beyond one gift file.

## 1. What was built

**`beispiele/96-buffered-writer.gab`** (new, English, corpus essay header): a buffered
writer over the `write` syscall. A table `Buffer` of fixed capacity (`CAP = 4`) holds
the bytes; `COUNT : u32 in 0 .. CAP` holds the count; one byte at a time crosses to the
kernel through a one-byte staging array (`WINDOW`). `push(fd, byte)` stores and flushes
when full; `flush(fd)` calls `write` in a `forever ... leave` loop until every buffered
byte went out or an error reason comes back; `fill` pushes `"hello\n"` (six bytes over a
capacity of four, so the fifth push flushes midway and the full-buffer path runs live);
`writer_demo(fd)` fills, flushes, and answers the final flush's byte count. The driver
answers `hello` + `2` (four bytes out midway, two at the end).

Two deliberate deviations from the first draft, both measured, both documented in the
file header:

- The syscall declares `buf : ptr<normal, r> u8` (the PLAN-SYSCALL.md §1 shape), not
  74's `u64`. The stub widens it into `rsi` itself; the call site passes the staging
  array the way `beispiele/64` passes its buffer to `extern fn write`.
- The flush loop is `forever ... leave`, not `retry ... until`. A `retry` lowers
  through a static trip count (`bounded` over the per-pass cost, `durchgangskosten`),
  and a call to a costless callee has no per-pass cost — a syscall carries no `costs`
  clause by grammar, so no bounded loop can host one today (`C001`). `forever` needs
  no trip count. That gap (a `costs` clause on `syscalldecl`) is real and is booked
  in §6, not worked around.

Checker iterations, each a named rule: `P033` (no `;` after block forms), `M147` (V4
freshness — the flush-path answer is returned as the constant `CAP`, not as the
pre-store local), `M101` (`narrow` refines locals, not statics — copy `COUNT` to a
`let c : u32`, narrow, store, write back; the declared type also keeps the emitter
from writing a `>= 0` that `cc -Wtype-limits` refuses), `M116` (`let mut sent`).

**`beispiele/gift/880-syscall-undeclared-channel.gab`** (new, `-- erwartet: N067`): the
one genuinely unpinned `N067` direction — an `errors` map whose `or` channel declares
nothing (`or GibtEsNicht`). Exactly one refusal, at the channel span. The plan's three
failure shapes are otherwise already pinned and were NOT duplicated (§4).

**`instrumente/pruefe-emission.sh`**: `TREIBER96` + `lauf "beispiel96"` (expects
`hello` + `2`; poison `s/"syscall\\n"/"nop\\n"/` shared with 74; zeugnis pin with
13 direct forms / 2 foreign bodies) and `MARKE_EMIT` 75 → 76 with reason at the mark.
The driver provides the `forever`'s watchdog (`writer_hangs`, a `-> never` extern) the
way a `sonde_*` falsifier is provided beside the unit: it aborts, and a run that
reaches it answers nothing expected.

**Doc number re-books** (convention: update to measured, decompose here): README
(77 clean / 586 poison / 1445 ceremony), DONE.md:1562 (77 / 586), TODO.md (124 fremde
Rümpfe + history, 399 Widerruf-Dateien), dokumente/PLAN.md (21 Vorbedingungen +
history), messung/ZEREMONIE.md (108 von 1445). Caution learned: the ceremony pattern
anchors on `— N and`, so a `~~1408~~ 1445` strikethrough un-guards the number
(`UNBEWACHT`); history stands parenthetically there instead.

## 2. Exact names

- `beispiel::buffered_writer`: `CAP`, `Buffer` (+ slot field `byte`), `COUNT`,
  `WINDOW`, `IoError` (`BadFd = 9`, `Interrupted = 4`, `WouldBlock = 11`,
  `exhaustive`), `linux_write_contract` / `sonde_write` (reused pair),
  `writer_hangs`, `syscall write`, `push`, `flush`, `fill`, `writer_demo`.
- `gift::syscall_undeclared_channel`: `fehlend`, `or GibtEsNicht` (no other items).
- No new Rust definitions, no new Lean definitions, no new diagnostic codes, no new
  sentences. Gift numbers used: 880 (881–884 stay free); examples: 96 (97 stays free).

## 3. Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (final run, all files final).
- `./lean-bau`: `Build completed successfully (61 jobs).` (no Lean changes).
- `./emission-pruef`: `beispiel96` green in **all 8 stages** (emit, bit-identical
  re-run, license, `cc -Werror`, result `hello`+`2`, `-O2` equal, UBSan, ASan,
  zeugnis pin, poisoned-C differs); `76 beispiele/` clears the pulled-up mark;
  225/225 emitting files compile under cc AND clang. Stage 9 still exits 1 on
  exactly the documented base baseline, file for file (M 132/73, G 8/2, X 8/1,
  UMG 2/4 per MUSE-REPORT-107 — none involves my files; my gift 880 is
  checker-refused and emits nothing). Stage 10 unmeasured, as at base.
- Guardians green: kennungen ALL PASS; sondendeckung ALL PASS 18/51 (the pair is
  reused, gifts excluded); saetze (130/55/0); gruende; deckung (UNCOVERED = 0);
  schablonen; konstrukte; reichweite; grammatiktafel (0/228); syntax.sh;
  uebersetzerfamilie; notation; ausnahmen; unfalsifizierbar.
- Guardians red, every line verified pre-existing (base run without my files where
  it mattered): zahlen 15 (my 6 lines re-booked; rest drift, §5), todo 3
  (Kennzahlen 89/88 ×2, unbewachte 179/180 — zahlen's own drift), englisch
  (7905/7881, 1085/1069 — identical numbers at base), vergabe (24/80 vs 20/68 —
  N067 has exactly one issuance site, my probe moves nothing), klauseln
  (`region`/`zucker`), aufloesung (Fach 1, m1.rs), manifest (E1 fragment gate),
  umwandlungen (Rust casts), gestalt (unbooked Lean files of other lanes),
  abstieg. sonden.sh, luecken, beweise not run (no probes/Lean changed).

## 4. Poison-probe coverage (no duplicates)

| Plan shape | Pinned by | New? |
|---|---|---|
| missing/undeclared errno side | 832 (`N067` target undeclared), 839 (doubled errno), 840 (map with no channel) | 880 = fourth direction (channel declares nothing) |
| wrong register map | 830 (`N063` dup), 831 (`N064` clobbered out), 836 (`N065` unbound), 837 (`N066` unknown reg) + 850/851 (`C180`/`C181` emitter) | none — complete |
| arch mismatch | 833 (`A005` undeclared machine), 838 (`A006` sealed), 852 (`C182` emitter) | none — complete |

By explicit design there is NO probe for "the map omits an errno": an unlisted
errno is the named hardware outcome (`hardware (annahme a)`), not a declaration
fault (`syscall.rs` says so; the stub decodes it to `__builtin_unreachable`).

## 5. Zahlen decomposition (measured, base run without my files vs with)

My delta, all re-booked: Zeremonie 1412 → 1445 (+33 mine; 1408 → 1412 was drift),
sinken 94 → 108 (new line, all drift + mine folded per convention), fremde
Rümpfe 122 → 124 (+2: the syscall + `writer_hangs`), Widerruf-Dateien 398 → 399
(+1: example 96; gift files unread), Vorbedingungen 20 → 21 (+1:
`flush :: write requires #1`). The remaining 15 Befunde are byte-identical at
base (Rücklaufwerte, deutsche Kommentare, Kennungs-Proben, Instrumente,
Absagentexte, Mutationsanker, Zeilenfortsetzungen, Umgebung-Blicke, Klauseln,
Sätze).

## 6. Item 3 — what the checker PROVES vs CARRIES (exact lines)

`gabbro pflichten beispiele/96-buffered-writer.gab` prints, verbatim:

```text
obligation	push :: ensures #1	N	beispiele/96-buffered-writer.gab:88	open	result == 0 || result == CAP
obligation	flush :: ensures #1	N	beispiele/96-buffered-writer.gab:109	open	COUNT == 0
obligation	flush :: write requires #1	V	beispiele/96-buffered-writer.gab:132	open	len <= 1024
== 3 obligations: 0 refinement, 0 preservation, 2 postcondition, 0 foreign, 1 precondition, 0 device, 0 loop invariant, 0 unowned invariant ==
```

- The two `ensures` are **counted N obligations, open, carried** — "Counted, not
  discharged" is the register's own header. The checker shape-checks them
  (`M109` names resolve, `M111` names `result`/a written place) and carries them
  to the prover; it proves neither. `push`'s disjunction reports the flushed
  count (0 = grew, `CAP` = flushed); the growth itself is established by the
  body and owed under the same N line. `flush`'s `COUNT == 0` holds on the
  success path only.
- The `requires` is a **V obligation at the call site, counted**; `M115`
  discharges it only in the weak reading — it refuses where the argument range
  EXCLUDES the condition (cf. `gift/633`: `` `write` requires `n <= 64`...``)
  and is silent otherwise ("Silence is not confirmation", the register's own
  footer). Here the call passes literal `1`, so the check is real but trivial.
- The syscall's own `ensures result <= len` appears **nowhere**: 74's register
  holds exactly one line (`schreibe :: write requires #1`, V) with 0 foreign —
  a body-less `ensures` is neither counted (N/F) nor checked. Same for the
  `requires` of `push`/`flush` (there is none to count).
- "On `or IoError` the count is unchanged" has **no obligation line**: a
  single-world predicate cannot say "unchanged", and `old()` falls to the
  present (Extraktion.lean R1a). It holds by construction — the loop advances
  locals only (`sent`), `COUNT` is written exactly once, after the loop — and
  is documented in the file, not discharged anywhere. Stated plainly as asked:
  this half of the `flush` contract is carried by the code shape, not by any
  machinery.

## 7. What remains open / what I believe is wrong

1. **A `retry` cannot host a syscall.** Bounded loops lower through a static
   trip count from callee `costs`; `syscalldecl` has no `costs` clause by
   grammar and a wrapper cannot supply one (`K003` over the unknown body).
   Until the grammar grows the clause (parser + SYNTAX.md + Wortschatz +
   guardian patterns — a language change, not this lane), every syscall loop
   is `forever` + `leave`, i.e. termination by liveness instead of by number.
   The plan's S7 "flush ... in a loop" holds operationally; the trip count
   does not exist yet.
2. **Body-less `ensures` is invisible.** `write`'s `ensures result <= len`
   produces no N/F/V line anywhere — the S7 "flush proved against the syscall
   contract" therefore rests, machine-side, on the `requires` V line plus the
   `let ... else` exhaustiveness (`M123`), not on the callee's postcondition.
3. **The errno NAME is never held against a kernel table** (already booked by
   lane S6, confirmed here): the stub decodes `-raw` against the reason case's
   declared number; `EBADF => BadFd` with `BadFd = 42` would check clean and
   land in the hardware outcome. No in-tree kernel table exists to check
   against.
4. `beispiele/96` reuses the (assumption, probe) pair of 74/90 — by the 90
   precedent this is correct, not a gap. Gift numbers 881–884 and example 97
   stay free for lane 112's neighbours.
5. Lean rules 5/6/13 need no action: no new Lean file, no new theorems, no
   TARGET/ZEUGE in this task (Rust + corpus lane, like S6).
