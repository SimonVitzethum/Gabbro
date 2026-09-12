# MUSE-REPORT-57

Lane S2 (PLAN-SYSCALL.md section 2): syscall meaning in Lean.
New file `grammatik/Grammatik/Syscall.lean`, wired into `grammatik/Grammatik.lean`.

## What was built

- `SysReg`: inductive of the 16 x86_64 general registers (no second register file; aarch64 stays sealed).
- `SysAbi`: `nummer : Nat`, `ein : List (SysReg × Nat)`, `aus : SysReg`, `clobber : List SysReg`.
- `SysAbi.gut`: input registers pairwise distinct, no parameter bound twice, output not clobbered.
- `sysAbiGutB`: Boolean decision procedure; `sysAbiGutB_sound` proves `sysAbiGutB a = true -> a.gut` (every premise used via `simpa` on each conjunct).
- `Unerwartet` (`ausserhalb`), `SysAntwort F sig tau Grund` (`ok | grund | unerwartet`).
- `FehlerTabelle Grund := List (Nat × Grund)`, `fehlerSuche` (via `List.find?` + `Prod.snd`).
- `dekodiereB : FehlerTabelle Unit -> Int -> Int -> Int -> Nat` (class function: 0 = ok range, 1 = listed errno, 2 = named hardware outcome).
- `dekodiere_total`: under `hbereich : -4095 <= roh`, `hgef` (negative in-range raw value has its errno listed), `hkein` (non-negative raw value is in the ok range), every raw value lands in class 1 or 0 (third disjunct covers the same function for callers that discharge differently). All premises consumed by branch selection.
- `dekodiere_tabelle`: a listed errno `e` with first-occurrence freshness (`hfrei` over the `takeWhile (p.1 != e)` prefix, i.e. the task's "no duplicate errno" in the only form `find?` can use) decodes `-e` to class 1. The `find?`-split lemma (takeWhile/dropWhile reconstruction, head identification, `Unit` payload collapse via `Prod.ext`) is proved inline; both premises consumed.
- `dekodiere_ok_bereich`: non-negative raw value in range decodes to class 0.
- `dekodiere_unerwartet`: listed-range but unlisted errno decodes to class 2 (needed so the totality claim covers the unlisted leg; `fehlerSuche ... = none` + range both consumed).
- `schreibAbi` (write: number 1, rdi/rsi/rdx in, rax out, rcx+r11 clobbered) with `schreibAbi_gut` (by `decide`).
- ZEUGE `dekodiere_tabelle_zeuge`: `dekodiereB schreibFehler 0 8192 (-4) = 1` over `schreibFehler := [(9, ()), (4, ()), (11, ())]`, all three premises by `decide`. Plus `schreibFehler_fuenf_unerwartet` (errno 5 -> class 2).

## Last build result

`./lean-bau`: `Build completed successfully (37 jobs).` (0 error lines).
`./lean-probe grammatik/Grammatik/Syscall.lean`: 0 errors; `#print axioms` shows only `propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`.

## What remains open (see CUTS in the file)

- Theorems run over `FehlerTabelle Unit`, not a named reason type (`BadFd | Interrupted | WouldBlock`): no new syntax was introduced in this lane, so distinct named reasons do not exist yet.
- Class `2` is a Boolean class of `dekodiereB`, not the `SysAntwort.unerwartet` constructor: the value-level decoder (raw `Int` to `SysAntwort` with a `Zahl` proof) needs `Val`/`Zahl` plumbing.
- `dekodiere_total` assumes `-4095 <= roh` plus the listed/in-range premises; the below-`-4095` leg is class 2 by the same `dif_neg` step but not named in the disjunction.
- No `Ax` pairing (`sysabi` field) and no ghost carriers: lanes S3/S4.

## What I believe is wrong in the task

- The task asks for "`SysAntwort (tau : Ty) (Grund : Type)`" but the existing value type is `Val F sig : Ty -> Type` (needs the function type `F` and signature map `sig`); I used `SysAntwort (F : Type) (sig : F -> Nat) (tau : Ty) (Grund : Type)`. Elaboration detail per rule 12.
- The task asks for "`SysAntwort (+) Unerwartet`" (a sum) in item 2 but also calls the answer type itself `SysAntwort ... := ok | grund` in item 1: I made `unerwartet` a third constructor of one inductive instead of a sum with `SysAntwort`, so both readings hold in one type.
- The task's `dekodiere_tabelle` proviso ("provided the table has no duplicate errno") is stated as first-occurrence freshness (`hfrei`), which is what the `find?` lookup actually needs and is strictly weaker than global key-nodup; the witness table satisfies both.
- Rule 13's non-degeneracy clause (a table some function writes; a run with a memory-changing step) is about `Vertrag`/`Stmt` programs and does not fit a pure decoder theorem over `List (Nat × Unit)` with no syntax quantification; I witnessed the named ZEUGE theorem jointly (all premises by `decide` on the PLAN-SYSCALL.md write table) and report the mismatch rather than fake a run.
