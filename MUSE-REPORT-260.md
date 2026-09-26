# MUSE-REPORT-260 — Lower threads created at run time to C, with our own syscall

Lane 260, branch `muse/260`. Task: Simon's rule -- threads at run time are made by OUR OWN
code issuing the kernel system call, never libc.

## 0. Commit status and the one red (read first)

This commit is red in EXACTLY ONE test: `jedes_gift_faellt_mit_seinem_code` on the
UNTOUCHED file `beispiele/gift/1112-kind-ohne-senke.gab` (lane O-1's probe; a second
latent flip waits behind it on untouched `beispiele/gift/1114-kind-handed-read.gab`,
same shape). Everything else is green (1326 passed, 1 failed).

Why the red is the task-ordered, by-design consequence and not a defect:

- Item 3 of the task orders lifting `C185` ("Lifting C185 turns the pin red BY DESIGN").
  Item 5 orders that examples 155/156 EMIT.
- 155's guarded shape (`if v == 0 { child { … } }`) and 1112's shape are the SAME
  shape -- 1112's own header says "This is the shape of beispiele/155". The only
  differences are comments, the module name, and `arbeiter(stapel)` vs a direct
  `stapel` read. No honest lowering distinguishes them; a rule that did ("regions
  must call a helper") would be fabricated to dodge the gift.
- The continuation forbids me to rename, move or rewrite 1112/1114 (reverted my
  draft rewrite; the files are byte-identical to master).
- Hence: lifting the guarded shape flips both files without touching them. The fix
  is a 2-minute re-homing owned by the O-1 side (1112's header already books
  "reported for renumbering at review"): move the two probes' expectations into
  this lane's block or re-home them as clean examples like 160. I did NOT do that
  (forbidden files); the merge review owns it.

Rule-8 note: committing with a characterized red instead of withholding the lane's
core deliverable (the alternative -- reverting the lowering -- would delete verified
work from a branch that gets cleaned up after merge). The red is localized to one
assertion on a forbidden file, documented here and in `saetze.rs`.

## 1. What was done (task item by task item)

**Item 1 -- runtime `laufzeit/faden.{c,h}`** (committed earlier as `6e4d3d4f`).
`gabbro_faden_start(fn, spitze, wort)` issues x86_64 `clone` (56) from inline asm
that branches BEFORE any C stack operation in the child (first version returned
through `pop %rbp; ret` on the new stack and jumped to NULL -- measured, then
fixed); the child calls the root on the handed stack and exits the THREAD with
`SYS_exit` (60), never `exit_group`. `gabbro_faden_warte(wort)` loops on an
acquire-load plus `FUTEX_WAIT` (202) until the kernel-cleared word reads zero.
Flags `CLONE_VM|CLONE_FS|CLONE_FILES|CLONE_SIGHAND|CLONE_THREAD|CLONE_SYSVSEM|
CLONE_CHILD_CLEARTID` (0x250F00), each justified in the file header.
**No `CLONE_SETTLS`** (no TLS use anywhere on these paths: nullary roots over
shared tables plus own stack; raw answers stay in locals, no `errno`), no libc
threading (`nm`-clean: no `pthread_*`, no `clone`, no `__errno_location`).
Every register and flag documented in `laufzeit/faden.c`.
Verified by a private scratch probe (`.tmp/opencode/probe-faden.c`, not committed):
two threads rendezvous (bounded spin on release/acquire flags -- serialization
would time out) and raise a shared atomic counter to 2x200000 at -O0 and -O2,
UBSan clean; null root and misaligned top refused with EINVAL.

**Item 2 -- `start { f, g };` lowers** (committed earlier as `ca0cb028`, extended
here with walk-order counter names for `fmt_views`). One `gabbro_faden_start`
per root on its own file-scope 64 KiB stack (`gabbro_stapel_<nr>_<i>`,
16-aligned, beside the tables), then one `gabbro_faden_warte` per root: every
spawn precedes every join. A refused spawn traps (`__builtin_trap` on the
condition line -- the census `trap-guard` row); there is no error channel in
the statement, so running on would be the silent wrong answer. Unresolvable,
bodiless (`impl_funktionen`), non-nullary, result-carrying, repeated, or empty
roots stay `C001`. Checker rules N458-N462 untouched (emitter runs on the parsed
tree; the SUM cost bill of F4/`kosten.rs` is consistent with spawn-all-then-join).
`Namen::{start_orte, impl_funktionen}` are the new maps.

**Item 3 -- `child` lowers inside the narrow triple; `C185` lifted there.**
A gate call `let v = gate(args) else (e) { … }` through a resolved stack gate
(`tor_inline_daten`: the SILENT condition-twin of the stub's C182/C180/C181/
C184/C183/error/ghost checks -- anything the stub would refuse resolves to
`None`), followed in the same top-level body by `if v == 0 { child { … } }`
with the region as the guard's SOLE statement (`antwort_wache`), no nested
`child` (`kind_verschachtelt`), one region per gate: the gate call becomes an
inline `syscall` (`__asm__ goto`) that jumps straight to the region label
(`gabbro_kind_<nr>`) when the answer is zero, plus the stub's decoding with
local targets (`kind_tor_falle`: `-4095` fence, `errors` arms against DECLARED
reason numbers, surviving range checks, `(T)raw` store, `ok`-flag legs). The
child never executes the decoding, the guard, or anything between gate and
region; the parent (answer never zero) decodes and skips the region through
its guard. Everything wider keeps `C185` with an updated message naming the
triple. NO new checker rule (the task's conditional): the in-between gap is
vacuous by construction, so nothing there is unsound for the child -- stated
plainly as ordered.
New unit: 155/156/160 emit, `gift/1181` (my block) still refuses; untouched
1112/1114 flip (see §0).

**Item 4 -- BOOT keeps pthreads.** `laufzeit/start.c` / `start_pool.c`
untouched: `concurrent` starts are boot-time (the machine coming up), not "at
run time". Runtime `start` never touches them (the 159 driver links only
`faden.c` plus a test-only spinlock).

**Item 5 -- emission, runs, TSan-free argument.**
- 159 (`start`, lock-guarded wrapping counter, N=32/root): all 8
  differenztest stages green in `./emission-pruef`, expected output `64`
  (deterministic on every schedule), mutation (`+1` to `+0`) bites with `0`.
- 155/156/160: emit + `cc -Werror -c` clean (stage 9). They do NOT get `lauf`
  entries, plainly because their gates are test doubles (`number 1000`, "not
  an OS number" by documented design; the real-number counterpart lives in the
  firewall repo outside the tree): executing one would issue syscall 1000,
  take `-ENOSYS` on an unlisted errno and reach the hardware-unreachable leg
  BY CONSTRUCTION. A `lauf` there would assert a crash. What RUNS instead:
  (a) the 159 lauf (same faden threads), (b) the faden rendezvous probe
  (true overlap proven), (c) a private fork-gate mechanism test
  (`.tmp/opencode/mech/`, gate number 57): the trap fires, the child runs the
  region (exit-code oracle 43), the parent decodes the pid and continues --
  at -O0 and -O2. The jump-vs-fallthrough skip itself is proven by
  construction (`jz %l[label]`, visible in the emitted C) plus the pin (guard
  stands exactly once); with fork-copied memory the two are unobservable, and
  the report does not claim otherwise.
- TSan-free argument, written down: the runtime shares only the join word per
  thread -- kernel clear (release) + waiter acquire-load/FUTEX_WAIT =
  synchronizes-with; everything the thread wrote is visible post-join, no lock
  and no race in the runtime itself. (TSan cannot see raw-clone threads at all
  -- no pthread registration -- so "TSan-free" here is by-construction
  reasoning, stated as such, not a tool verdict.) Unit 159 shares `zaehler`
  (both roots write -- guarded by L, `N462` pool-safe, checker-verified),
  `takt` (read by both, written by NOBODY -- no race), per-thread stacks/join
  words (disjoint by construction), driver spinlock (acquire-exchange /
  release-store); main's post-join read follows both joins. `N458`-`N461`
  silent; the `E247` hint on the post-join read is the checker's conservatism
  (it does not track that the join ended every writer) -- hint-level, documented
  at the source line.

**Item 6 -- `LG004` untouched** (lean_g.rs, corrlean.rs, obligations all
unread by this lane; no Lean work at all -- rule 13 vacuous).

**Reserved blocks:** N471-N475 UNUSED (no new checker rule owed -- see item 3);
gifts 1181 used (1 file; 1182-1190 free); examples 159+160 used (both from the
block). `MARKE_EMIT*` untouched (deltas in §3). `grow`/strings untouched.

## 2. Exact names of new definitions/theorems

No Lean definitions or theorems (no `grammatik/` change; `./lean-bau` green by
absence). New Rust items (all in `crates/gabbro-check/src/emit.rs` unless noted):
- `struct KindTor` (+ fields `nr`, `label`, `nummer`, `heber`, `param_zahl`,
  `zerstoert`, `arme`, `wert_ctyp`, `unter/ober`, `annahme`, `tor_name`,
  `region_lo`) and `Namen::{kind_tore: HashMap<u32, KindTor>,
  kind_regionen: HashMap<u32, u32>, start_orte: Vec<(u32, usize)>,
  impl_funktionen: BTreeSet<String>}`.
- `fn tor_inline_daten(...) -> Option<(...)>` (silent resolver),
  `fn antwort_wache`, `fn kind_verschachtelt`, `fn kind_tor_falle`
  (trap + twin decode), triple scan inside `emittiere_mit`.
- C runtime: `gabbro_faden_start`, `gabbro_faden_warte`
  (`laufzeit/faden.{c,h}`).
- Tests: `kind_sprungsenke_traegt_die_sprungannahme` and
  `kind_ohne_wache_faellt_mit_c185` (replace `c185_traegt_die_sprungannahme`
  BY DESIGN in `crates/gabbro-check/tests/klon_faden.rs`).
- Probes: `beispiele/gift/1181-kind-ohne-wache.gab` (C185, unguarded region),
  `beispiele/160-kind-liest-stapel.gab` (clean handed-read triple).
- Census: `stmt:label-kind` classifier row + FORMS + KNOWN_UNCOVERED
  (`instrumente/pruefe-cformen.py`); zeugnis `Posten{start: Fremd}`,
  `Posten{child: Direkt}`; `saetze.rs` C185 + start sentences updated.
- Emission: `TREIBER159` + `lauf "beispiel159"` + `@FADEN@` substitution (both
  driver paths) in `instrumente/pruefe-emission.sh`.

## 3. Verification results (numbers)

- `./cargo-pruef`: **1326 passed, 1 failed** (`jedes_gift_faellt_mit_seinem_code`
  on untouched 1112; 1114 same shape, latent). All other targets green,
  including the replaced pin, `fmt_views`, the K100 zeugnis test, and every
  `allein`/poison test.
- `./emission-pruef`: every differenztest green incl. new `beispiel159`
  (stages 1-8: emit, bitgleich, Lizenz, cc, `64`, -O2 same, UBSan clean, ASan
  NICHT GEFAHREN -- hardened kernel, the harness's own W1 case; zeugnis string
  matched; mutation bites with `0`). Stops at stage 9 (exit 1) on the two
  EXPECTED mark mismatches only: beispiele **129 statt 126** (155+156+159;
  160 untracked at run time -- committed now, so effectively 130), gift
  **20 statt 18** (untouched 1112+1114 now emit). No other mismatch; stage 10
  unmeasured behind the stop (neither yes nor no). MARKE lines untouched.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`
  (Build completed successfully, 285 jobs).
- `pruefe-cformen.py`: 0 new uncovered, 0 missing lemmas/assumptions; 1
  unclassified statement in `140-atomic-array-counter.gab` (CAS line --
  pre-existing drift, my diff touches no atomic/exchange code; 6 stale
  KNOWN_UNCOVERED entries likewise).
- `pruefe-saetze.py`, `pruefe-kennungen.py`: ALL PASS.
- `pruefe-englisch.py`, `zaehle-gifttreffer.py`: red IDENTICALLY at baseline
  (measured via stash: 7965/37/5 and verdeckt-47 both ways) -- pre-existing
  drift, untouched by this lane (all lane comments/probes English).
- Corpus verdict diff (checker: NO file changes verdict -- checker untouched):
  emitter newly emits 155, 156, 159, 160; C185 gone on untouched 1112/1114;
  new C185 on 1181; everything else byte-identical in verdict (294/294
  emitting files compile under cc AND clang families).

## 4. What remains open / requests to the review

1. **Re-home untouched 1112/1114** (O-1's files): expectations flipped by
   design (see §0). Suggested: move their shapes into this lane's block or
   re-home as clean examples beside 160.
2. **155/156 have no `lauf` entries** (test-double gates -- see item 5). If a
   real run is wanted, the gates need real numbers, which the O-1 design keeps
   outside the tree (firewall's `gab/systemrufe.gab`).
3. **Stage 10 of emission-pruef** unmeasured behind the stage-9 stop.
4. **ASan over raw-clone threads** could not run on this kernel (harness W1).
5. **Model side** (`klon_ziel`, `N457`-implies-acceptance proof, stub
   correspondence lemma for the jump, `LG004` export): untouched per item 6 --
   the model lane's, with O21/O22 status lines updated.
6. **N471-N475, gifts 1182-1190**: unused, free.
7. **What I believe is wrong in the task**: item 5's "155, 156 ... RUN in
   `./emission-pruef`" is unexecutable as stated for test-double gates (a run
   would assert the `-ENOSYS`-into-unreachable leg); 159 + the two private
   mechanism probes are the honest substitute, stated plainly per rule 4.
   Second: the task's flag list asks to "decide and justify" CLONE_SETTLS --
   decided ABSENT (no TLS use; setting it would promise a facility nobody
   reads). Third: `beispiele/159`'s `E247` hint is correct conservatism, not a
   defect (post-join read under the lock, no thread alive).
