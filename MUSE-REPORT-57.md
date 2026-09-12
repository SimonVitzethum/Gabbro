# MUSE-REPORT-57

Lane S2 (PLAN-SYSCALL.md section 2): syscall meaning in Lean.
New file `grammatik/Grammatik/Syscall.lean`, wired into `grammatik/Grammatik.lean`.
Revised per reviewer feedback: the decoder returns the answer type, totality
is premise-free with both-direction characterisations, and the write table
runs over a real reason type.

## What was built

- `SysReg`: inductive of the 16 x86_64 general registers (no second register file; aarch64 stays sealed).
- `SysAbi`: `nummer : Nat`, `ein : List (SysReg × Nat)`, `aus : SysReg`, `clobber : List SysReg`.
- `SysAbi.gut`: input registers pairwise distinct, no parameter bound twice, output not clobbered.
- `sysAbiGutB`: Boolean decision procedure; `sysAbiGutB_sound` proves `sysAbiGutB a = true -> a.gut` (every premise used via `simpa` on each conjunct).
- `SysAntwort (A : Type) (Grund : Type)`: `ok (v : A) | grund (r : Grund) | unerwartet (roh : Int)` — the named hardware outcome carries the raw value it came from.
- `FehlerTabelle Grund := List (Nat × Grund)`, `fehlerSuche` (via `List.find?` + `Prod.snd`), `ersterEintrag tab e r` (first-entry split: `(e, r)` present, no earlier pair with errno `e`).
- `dekodiere (tab) (lo hi roh) : SysAntwort { x : Int // lo ≤ x ∧ x ≤ hi } Grund`: negative `-4095..-1` through the table, non-negative in-range to `ok`, anything else to `unerwartet roh`.
- `fehlerSuche_erster` / `erster_of_fehlerSuche`: lookup fidelity both ways (single premise consumed at each use site).
- `dekodiere_ok`: `dekodiere … = .ok v ↔ 0 ≤ roh ∧ lo ≤ roh ∧ roh ≤ hi ∧ v = roh`.
- `dekodiere_grund`: `dekodiere … = .grund r ↔ ∃ e, -4095 ≤ roh ∧ roh ≤ -1 ∧ (-roh).toNat = e ∧ ersterEintrag tab e r`.
- `dekodiere_unerwartet`: `dekodiere … = .unerwartet u ↔ u = roh ∧ ¬(ok-cond) ∧ ¬∃ e r, (grund-cond)`.
- `dekodiere_total` with NO premises beyond the arguments: the three existentials above as an exclusive disjunction (the `unerwartet` leg carries both negations, so `= unerwartet` is no longer an always-admissible disjunct).
- `dekodiere_tabelle` (backward `dekodiere_grund` at a concrete entry) and `dekodiere_ok_bereich` (backward `dekodiere_ok`).
- `IoFehler` (`badFd | interrupted | wouldBlock`), `schreibFehler := [(9, .badFd), (4, .interrupted), (11, .wouldBlock)]`.
- `schreibAbi` (write: number 1, rdi/rsi/rdx in, rax out, rcx+r11 clobbered) with `schreibAbi_gut` (by `decide`).
- ZEUGE `dekodiere_tabelle_zeuge`: `dekodiere schreibFehler 0 8192 (-9) = .grund .badFd` (first-entry split with empty prefix + range, both by computation).
- Totality witnesses, one per class: `dekodiere_total_ok_zeuge` (5 in 0..10 → ok), `dekodiere_total_grund_zeuge` (-4 → interrupted), `dekodiere_total_unerwartet_zeuge` (-22 → unerwartet), all by `decide`.

## Last build result

`./lean-bau`: `Build completed successfully (37 jobs).` (0 error lines).
`./lean-probe grammatik/Grammatik/Syscall.lean`: 0 errors; `#print axioms` shows only `propext`/`Quot.sound` (plus axiom-free `decide` witnesses), no `sorryAx`.

## What remains open (see CUTS in the file)

- `schreibFehler` exhibits only the errno table, not a full syscall declaration: pairing `SysAbi` with the table (the `Ax` extension) is lane S4/S5, not this lane.
- No `PCReach`/`GenErreichbar` wiring: this file imports only `Grammatik.Typen` and states decoder laws, not run properties.

## What I believe is wrong in the task

- Nothing material. Two elaboration notes: the ok payload is `{ x : Int // lo ≤ x ∧ x ≤ hi }` (the task allowed this or `Zahl lo hi`); `unerwartet` is a third constructor of one inductive rather than a sum `SysAntwort ⊕ Unerwartet`, so both readings of the task hold in one type.
- Rule 13's non-degeneracy clause (a table some function writes; a run with a memory-changing step) is about `Vertrag`/`Stmt` programs and does not fit a pure decoder theorem with no syntax quantification; the named ZEUGE plus one witness per totality class are supplied jointly over the PLAN-SYSCALL.md write table, and the mismatch is reported rather than faked.
