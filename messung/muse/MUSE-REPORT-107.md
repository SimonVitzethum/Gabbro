# MUSE-REPORT-107: syscall emitter stub (PLAN-SYSCALL.md lane S6)

Branch: `muse/107`. Rust lane (emitter). One Lean edit
(`grammatik/Grammatik/Erhaltung.lean`: a decided table row, no new theorems,
`./lean-bau` green, see §7).

## What was built

The emission refusal is gone; every checked `syscall` lowers to one C
function. `beispiele/74-syscall-schreiben.gab` emits C that compiles under
GCC and Clang with `-std=c11 -Wall -Wextra -Werror`, and the emission check
runs it: a `write(1, "ok\n", 3)` returns 3. `beispiele/90-syscall-errno.gab`
runs the error path: `EBADF` decodes to `BadFd`.

**Emitter** (`crates/gabbro-check/src/emit.rs`): `syscall_stumpf` writes
prototype into `aus`, definition into `rumpf`, exactly like `funktion`.
The template binds every parameter to its declared in-register via explicit
register variables (`register uint64_t _sys_rdi __asm__("rdi")`, the musl
idiom — the sixteen GPRs have no complete constraint-letter set), loads
`number` as the `rax` pin's initial value (`+a`, one name, no input/output
aliasing question), executes `syscall` as `__asm__ __volatile__` with the
declared clobbers plus `memory`, `rcx`, `r11`, then decodes: negative
`-4095..-1` against the `errors` map into the `or R` channel (each errno
against its reason case's DECLARED number — the only number the unit writes
down), an unlisted errno or an out-of-range non-negative value into the
hardware outcome (`hardware (annahme a)` via `#if defined(__GNUC__)`
`__builtin_unreachable(); #endif`, the `D005` handover shape). The signature
is the one call sites already lower against (`bool` + `_wert`/`_grund` with
the channel, plain otherwise). No `const`/`pure` attribute whatever the
declared effects say (a `const` would let GCC merge two writes). The `-4095`
fence stands before the negation, so UBSan sees no overflow by construction.
Vacuous range checks (`hi >= 2^63-1`, `lo <= 0`) are not written —
`-Wtype-limits` in `-Wextra` refuses comparisons it can decide itself.

Five shape rules carry their own codes, each with its poison probe:
`C180` (`regs in` binds `rax` or a clobbered register), `C181` (`regs out`
is not exactly `rax`, or `rax` clobbered), `C182` (not `linux`/`x86_64`),
`C183` (non-integer answer — incl. named types, whose range the stub does
not resolve), `C184` (`number` or a result bound does not fold). Everything
else unlowerable stays generic `C001`. Ghost parameter, `errors` without a
channel, unresolvable reason/case: `C001` (checker-side shapes on a blind
tree, not template rules).

**Probes/files**: `beispiele/74` extended with `buf : u64` (the old two-arg
shape cannot return 3 from a real `write` — `rsi` would be garbage; the task
requires the runnable write, so the example grew the buffer); new
`beispiele/90-syscall-errno.gab` (EBADF path, deterministic `777`);
`beispiele/gift/797` (the healed `C001` refusal) deleted per the healed-probe
convention; new `beispiele/gift/850`-`854` (one per code, each checker-clean,
each refused by exactly its code). `beispiele.rs` harness runs the emitter
for `C180`-`C184` headers exactly as for `C001`. Example 91 and code numbers
beyond 184 unused.

**Certificate**: `syscall` stays `Fremd` (the kernel side stays foreign);
Posten grund rewritten (stub generated since S6). `korr_form` rows a
`syscall` as `None` with reason — its body is generated statements around
one `__asm__`, and statement-level rows belong to the body-walk follow-up,
exactly like a defined block function. New Satz `syscall.stub` claims the
five codes; `syscall.erklaerung` vorbehalt updated (stub sentence split out,
`C001` pin gone).

**Census** (`instrumente/zaehle-c-formen.py`): the template booked as ONE
form — `register` (4 sites, all in 74; 90 adds sites, not forms). Every other
construct was already counted. `MARKE_TABELLE` 66→67, `MARKE_UNERLAUBT`
31→32, reason at the mark. The `asm` row now reads two emission sites
(`asm` bodies + the stub); `asm-operanden` and the UNGEMESSEN note updated.

**Lean ruling** (`Erhaltung.lean`): `.luecke .syscallStub` row with
`.aufListe` price naming the stub as the assumption boundary (kernel behind
it is the named assumption; outside answers are the hardware outcome, never
a value). Structure allows it without new proofs: all matches over
`OffeneForm`/`EntscheidZiel` are total, `ruledB_voll` only covers the 19
`CForm`s, `tafel_geschlossen` decides over content-agnostic `entschieden`
(still green). Doc counts 30→30+boundary where the prose counted slots.
CUTS block appended (adequacy + emitter linkage + pairing all cut). No new
theorems, no premises — rule 13 needs no witness (Rust lane, no
TARGET/ZEUGE in task).

**Emission check**: `beispiel74` (erwartet `ok`+`3`, gift `nop` for
`syscall`) and `beispiel90` (erwartet `777`, gift retargets `BadFd`) laufs,
each passing stages 1–8 incl. `-O2`, UBSan, ASan, zeugnis pin, speech probe.
`MARKE_EMIT` 70→75 with decomposition (70 booked; 71/72/73 found emitting,
pre-existing drift already measured at 73 in MUSE-REPORT-86; +2 mine).

**Number re-books** (strikethrough/recompute convention, exact deltas in §5):
Saetze 118→122 (TODO:55 + PASSREGISTER, measured 114, codes 304→319,
claimed 249→264), Absagekennungen 304→319, fremde Ruempfe 117→122,
gruende 139→143/7→8/107→117, Vorbedingungen 19→20 (PLAN.md), Zeremonie
1376→1408 + 88→94 (README/ZEREMONIE.md).

## New definitions/theorems

- `emit.rs`: `SyscallTabellen` (module/gruende/strittig maps),
  `syscall_code` (`C180`-`C184` issuance), `syscall_stumpf` (the template);
  codes `C180 C181 C182 C183 C184` (each single-file, `pruefe-kennungen`
  ALL PASS).
- `saetze.rs`: Satz `syscall.stub` (claims the five codes).
- Lean: `OffeneForm.syscallStub` constructor + one `tafel` row (data, no
  theorems).
- No other new items; `syscall.rs`, `zeugnis.rs`, `beispiele.rs` extended
  in place.

## Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0`.
- `./lean-bau`: `== 0 error line(s) in the COMPLETE output`, `Build
  completed successfully (53 jobs).`
- `./emission-pruef`: `beispiel74`/`beispiel90` green all 8 stages;
  224/224 emitting files compile under cc AND clang; `MARKE_EMIT` clears.
  Remaining stage-9 failures equal the base baseline file for file
  (M 132/73, G 8/2, X 8/1, UMG 2/4 — none involve my files; the 8 emitting
  gifts enumerated, none mine). Stage 10 unmeasured — stage 9 exits 1 as
  at base.
- Guardians: kennungen ALL PASS (C: 6); saetze 122 sentences, 55 ohne, 0
  erfunden; sondendeckung ALL PASS 18/51 (gifts excluded from its corpus;
  74/90 reuse the counted pair); census 67/32 green incl. tracked 90;
  schablonen/konstrukte green. zahlen: every entry I move cleared (§5);
  the rest red as at base.

## What remains open

- S7 corpus (buffered writer over `write`, `entry syscall` rename) — not
  this lane; example 91 left unused for it.
- The `kernel` pairing check (`N068` still refuses; stub comment already
  carries the `kernel` shape).
- Named-type results (`C183`) and errno-name↔number agreement (see §6.1).

## What I believe is wrong (task/specs)

1. **The errno NAME is never held against a kernel table.** The stub
   decodes `-raw` against the reason case's DECLARED value (`BadFd = 9`);
   a declaration writing `EBADF => BadFd` with `BadFd = 42` checks clean
   (`N067` holds names, not numbers) and decodes against 42 while the
   kernel sends 9 — landing in the hardware outcome, loudly but for the
   wrong reason. There is no in-tree kernel table to check names against,
   so this may be unfixable checker-side; at minimum the Satz vorbehalt
   now says so.
2. **SYNTAX.md §12.1 still promises the `C001` refusal** ("the emission is
   refused as C001 until the lane-S6 stub lands"). Left stale on purpose:
   the document is S1's surface with guardian patterns on its wording;
   a syscall-docs lane should reword it, not this emitter lane.
3. **`beispiele/74` as S5 wrote it could not meet this task.** Two
   parameters and no buffer means `rsi` is garbage at the real `write`;
   `write(1, garbage, 3)` answers `EFAULT`, never 3. The buffer parameter
   is not decoration — it is what the acceptance criterion runs on.
4. **README front-page numbers** (74 clean examples, 568 poison, 94
   sentences/227 codes, 128/128 emission, 28 runs) are unread prose and
   stale far beyond this lane; left untouched.
5. **`TODO.md:4241` "53 Codes noch ohne"** vs measured 55 (saetze MARKE):
   stale at base, my codes all carry sentences (+0 ohne); left for the
   lane that owns the tooth.

## §5 Zahlen decomposition (measured 2026-09-12, this lane)

Re-booked (my delta stated, rest found drift): Saetze +1 of +4 (122);
Kennungen +5 of +15 (319); fremde Ruempfe +1 of +5 (122 — 74 counted
before and after, only 90 is new); Darstellung +1 of +1 (8 — base exact,
`C184`); unklar +4 of +10 (117 — `C180`-`C183`); Vorbedingungen +1 of +1
(20 — base exact, 90's call); Zeremonie Stellen +2 of +32 (1408) and
sinken +1 of +6 (94) — measured by restoring HEAD:74/removing 90
(1406/93) vs with (1408/94). Left red,delta-0 or foreign-dominated, with
shares: Giftproben-mehrdeutig 73→77 (base also 77, proven by the same
restore technique — my unambiguous probes + removed 797 net to zero);
tragend +0 of +4; Zeilenfortsetzungen ~75 of +450 (backslash count of my
Rust diff); Widerrufdateien +1 of +87 (only 90 is new to its `beispiele/`
population); Blicke +2 of +7 (`tabellen.gruende.get` ×2 — my struct, not
`Umgebung`, but the counter reads the field name); RUECKLAUFWERTE,
Instrumente, Mutationsanker paths, PLAN-Klauseln: 0 mine.
