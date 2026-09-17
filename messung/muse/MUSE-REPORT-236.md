# MUSE-REPORT-236 — ALG sketch FTP: the Obergrenze discipline, running

Lane 236. Two new example files, no other tree changes. No Lean, no Rust,
no codes, no gifts, no `extern`, no OS constants.

## What was built

- `beispiele/147-ftp-alg-control.gab` (module `beispiel::ftp_alg_control`,
  41 items) — control plane: `ablege`/`entferne` (insert/teardown by
  5-tuple), `tick` (windowed expiry), `befehl_nehme` + `befehl_schreibe` /
  `befehl_lese` (512 B command buffer, length gate).
- `beispiele/148-ftp-alg-daten.gab` (module `beispiel::ftp_alg_daten`,
  32 items) — data plane: `daten_paket` (per-packet verdict
  MISS / AKZEPTIERT / ABGELAUFEN), `erwarte` (stage a rule), own sweep.
  Same table parameters as 147 (1024 / window 64 / 16 rounds / age 63) —
  no layout experiments; each unit is self-contained because cross-unit
  table access does not exist.

Functions added (147): `xor_worte`, `fnv_schritt`, `fnv`, `freigeben`,
`ablege_innen`, `ablege`, `alter_eintrag`, `fenster_schritt`, `tick_runde`,
`tick`, `entferne_innen`, `entferne`, `befehl_schreibe`, `befehl_lese`,
`befehl_merke`, `befehl_nehme`. (148): same hash trio, `freigeben`,
`erwarte_innen`, `erwarte`, `urteil_innen`, `daten_paket`, same sweep trio
+ `tick_runde`/`tick`. No Lean theorems, so rule 13 has no target (no
`ZEUGE:` line, no ∀-over-syntax premise anywhere in the lane).

## Gates (all green)

- `gabbro check`: 147 → 0 errors, 0 hints; 148 → 0 errors, 0 hints.
- `gabbro emit` + `cc -Werror -c`: both emit (147: 340 lines C), both
  compile under `cc` AND `clang` (`-std=c11 -Wall -Wextra -Werror`).
  `-O2` runs byte-identical to `-O0`; UBSan silent on both drivers.
- `./cargo-pruef`: `== exit 0; failing tests: 0` (run twice).
- `./lean-bau`: `Build completed successfully (274 jobs).` (no Lean files
  touched; build is the pre-existing tree).
- Executed-compare bonus (drivers in lane scratch, not committed):
  emitted `fnv` == Python FNV-1a reference (3652464371 both ways).
  147: insert OK, re-insert VOLL, wrong-tuple teardown MISS, teardown OK,
  re-teardown MISS, `befehl_nehme(512)` OK, `(513)` ZU_LANG, slot
  reclaimed after 1100 ticks (would be VOLL otherwise).
  148: hit AKZEPTIERT, wrong-data MISS, wrong-port MISS, foreign-stream
  MISS, lazy ABGELAUFEN in its exact window (63rd visit leaves age 63
  standing; clearing visit 16 ticks later), then MISS, then reusable.

## Measured caps (`gabbro kosten`, computed / promised)

Hash 95 ops flat (5 words, no branch — the per-packet constant).
`ablege`/`erwarte` 242 (of which 136 under the held lock),
`daten_paket` 306 (200 held), `urteil_innen` 90, `alter_eintrag` 70,
`fenster_schritt` 77, `tick_runde` 8264, `tick` 8320 (held).
Lock budgets FW/FD `held <= 16384`, worst holder `tick` at 8320.
Window math: 1024 / 64 = 16 rounds, `runde` in 0..15,
`basis = runde * 64`, bucket `basis + k` ≤ 1023, subtraction-free
throughout; an entry lives 1007–1023 `tick()` calls (63 visits × 16 +
alignment), i.e. a full scan under lock (1024 × 70 ≈ 72k ops) is replaced
by a 8.3k-op window. Tick-vs-second skew, stated plainly: `tick()` is
caller-driven, so under flood the 1007-tick minimum is short wall-clock
and at idle it is long — fail closed both ways, since ages grow only on
sweep visits and a refresh writes 0 (never early, at most 15 ticks late).

## Emission effect (NOT touched, for the merger)

Census over tracked files with the lane binary: 119 emitting files in
`beispiele/` (booked `MARKE_EMIT=117` + these 2). `MARKE_EMIT` left at
117; the mark belongs to the merger.

## Findings (checker/emitter behavior, all paid for in the files)

1. `*%` needs the prime as an ARGUMENT into a bare-`u32` parameter: a
   singleton const next to a wrap fails M153, and a named exact range
   (`u32 in 0 .. 4294967295`) CHECKS but does not EMIT (`wrap_form`
   reads declarations, and only bare storage words lower). The xor must
   be a call result, never an inline operand. 147's header documents it.
2. E247 wants the guard in the SIGNATURE even inside a `locks` block
   (146's thin-outer/guarded-inner split, applied to every toucher), and
   the `protects` set must name `static mut` carriers too (`runde`,
   `haben`).
3. `narrow … else` arms are required even where `%`-arithmetic makes them
   unreachable (146 pattern; else answers MISS/ZU_LANG/OK accordingly).
4. No lock invariant, deliberately: a direct-mapped table's slots are
   independent (unlike 124's mirrored pair), so a fixed-index clause
   would be decoration. Every access is still under FW/FD.

## What the task got wrong / could not be read

- `messung/BEFUNDE-bm13.md` does not exist in this tree (only
  `messung/BEFUNDE.md`), and `TODO.md` §-1 has no lanes 236/237 (it runs
  221–235 + O-1/C-2). H-1/H-2/H-3, bm3 and the lane-237 boundary were
  implemented from the task text itself (windowed `altere_fenster`,
  subtraction-free index math, VOLL refuses).
- Numbers 147–148 are reserved for lane 222 in `TODO.md` §-1 (int-match
  arms). Taken as tasked; the merger must watch for a 222 collision
  (`keine_zwei_korpusdateien_teilen_eine_nummer` will catch it).
- `PLAN-SYSCALL/BITS/ERWEITUNG.md` exist and were skimmed; nothing in
  them changed the design (no syscalls, no float, no extension in these
  files by task order).

## Open

- A C driver with `_Static_assert`-pinned expectations (the `lauf` shape
  of `pruefe-emission.sh`) is NOT included: drivers live in the guardian,
  and the task asked for the two `.gab` files only. The scratch drivers
  above are the measured half of it.
- `befehl_schreibe`/`befehl_lese` take `index into befehl` — wiring a
  real parser onto the 512 B buffer is application work above this sketch.
- Costs promises carry headroom (e.g. `freigeben` 18/64); tightened only
  where the checker forced it (`fnv` 95, `alter_eintrag` 70). Deliberate:
  lane-139-style recalibrations move computed costs tree-wide.
