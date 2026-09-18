# MUSE-REPORT-221 — `+%` fetch_add arm: the binder-range refusal is lifted (TODO §-1 wave A)

Lane 221, branch `muse/221`, one commit over master `f6eeef72`. Simon's decision
2026-09-17 implemented: `t +% 1` lowers to C11 `atomic_fetch_add` wherever both
sides carry an exact unsigned range `0 .. 2^N - 1` on one storage width. Where
the range is NOT exact, the refusal stays — same code, narrowed condition.

## 0. Reviewer round-1 answers (verdict was ROT: zero commits, no report)

- Work was intact in the tree (`M emit.rs`, `M holform.rs`, untracked gifts
  1052/1053); nothing was re-applied from elsewhere and no other task was started.
- The log-tail errors the reviewer saw were the intermediate `E0004`
  non-exhaustive-match build failure of my own first cut (fixed same session by
  restoring the unreachable `PlusWrap | MinusWrap => return None` arms, keeping
  the table spelled out with no `_`).
- `./cargo-pruef` re-run to green; last line pasted in §5.

## 1. What was built (only `emit.rs`, `tests/holform.rs`, two gift probes)

**`crates/gabbro-check/src/emit.rs`** (+173/−42 with the table surgery):

- `Namen::atomic_elem_typs: HashMap<String, TypExpr>` — atomic name to DECLARED
  element type. The `atomics` map carries the C word, and a C word has forgotten
  what the declaration said (`uint32_t` no longer knows whole-word vs
  `0 .. 65535`). For array atomics this is the ELEMENT type, the same choice
  `atomics` makes. Populated in the existing atomic-type walk beside `typen` /
  `laengen`, under the same joint rule (both halves resolve or neither).
- `atom_elem_typ(o, u) -> Option<TypExpr>` — scalar: own declaration; indexed
  (`REGEL[r]`): the basis's element type, mirroring `atom_target`. `None` is
  the loop, never a guess.
- `holwrap_form(binder_typ, operand, u) -> Option<(u32, u32)>` — THE gate. Reads
  the binder side through `storage` + `intty_interval` + `exact_wrap_n` (the
  same three helpers the general `wrap_form` uses, joint-for-joint with its
  Word-Literal arm, including `konstwert` adoption), and accepts **iff**
  `n == bits` (see §4). Signed storage, non-`Int` binder types, non-constant or
  out-of-range operands, and `n != bits` all return `None`.
- `holform()` — new parameter `binder_typ: Option<&TypExpr>`; new wrapping
  branch BEFORE the bitwise table: `PlusWrap → atomic_fetch_add_explicit`,
  `MinusWrap → atomic_fetch_sub_explicit`. `t +% m` and `m +% t` both fetch
  (addition commutes mod 2^N); `t -% m` fetches but `m -% t` stays out
  (subtraction does not commute — the report's row-7 reason). The operand must
  be translation-time-constant (the row-9 once-vs-per-pass reason, unchanged).
  Call site passes `atom_elem_typ(&x.ort, u)`.
- Doc comment on the wrapping rows rewritten from "OUT" to "IN through the
  gate, refusal narrowed"; the `C001` refusal TEXT in `ausdruck_breit` is
  byte-unchanged.

**`crates/gabbro-check/tests/holform.rs`** (28 → 40 tests):

- Flipped by design (the lifted refusal): `die_umlaufform_bleibt_eine_absage`
  → `die_umlaufform_wird_eine_anweisung` (fetch_add, no CAS);
  `die_umlaufende_differenz_bleibt_eine_absage` →
  `die_umlaufende_differenz_wird_eine_anweisung` (fetch_sub, no CAS).
- New positives: `die_ausgeschriebene_wortweite_wird_eine_anweisung`
  (`u32 in 0 .. 4294967295` IS the word), `umlauf_alle_breiten` (u8/u16/u64),
  `umlauf_binder_rechts_add` (`1 +% t`), `umlauf_freigabe_wird_acq_rel`
  (ordering join rides along), `umlauf_indiziert_wird_eine_anweisung`
  (140-shape: `REGEL[r]`, fetch on `&REGEL[`).
- New pins where OTHERS own the row: `die_enge_umlaufform_bleibt_eine_absage`
  + `die_enge_umlaufdifferenz_bleibt_eine_absage` (emitter `C001`, checker
  silent — **the §2.3 surviving test, green**); `die_unexakte_umlaufform_faellt_am_pruefer`
  (`0 .. 1000` → checker `M153`); `umlauf_vorzeichen_faellt_am_pruefer`
  (`i32` → checker `M153`); `umlauf_konstante_faellt_am_pruefer`
  (`t +% MASKE` → checker `M153`: only literals adopt, consts carry their value
  point — m1's rule, read not written); `umlauf_binder_rechts_sub_bleibt_absage`
  (`1 -% t` → `C001`, no fetch); `umlauf_laufzeitoperand_bleibt_absage`
  (`t +% p` → `C001`: exact but not constant).
- All 26 pre-existing tests survive byte-identical in expectation (bitwise rows,
  orderings, widths, `M104`/`M101` rows, loop rows, clause rows, silencer rows).

**Probes** (reserved block 1052–1056; consumed 1052–1053, rest left free):

- `beispiele/gift/1052-fetch-add-narrow-range-stays-refused.gab`
  (`-- erwartet: C001`): `u32 in 0 .. 65535` + `t +% 1` — checker-clean
  (0 errors, 1 standing E247 hint, same shape as 140), emitter `C001`, no C.
- `beispiele/gift/1053-fetch-sub-narrow-range-stays-refused.gab`: the `-%` twin.
- `zaehle-gifttreffer.py --lang`: both classify `begleitet` (C001 first of its
  level) — neither `verdeckt` nor `FEHLT`. (The tool stays red overall on
  pre-existing findings: FEHLT 850–854 syscall gifts + verdeckt ceiling 40 vs
  24 — both unrelated to this lane, see TODO §6; my files contribute to neither
  class.)
- Positive probes live INLINE in `tests/holform.rs`, not as `.gab` files: a
  clean-checking new `.gab` file would emit and trip `MARKE_EMIT`/`MARKE_EMIT_G`,
  which this lane must not touch. No N391–395 consumed: no new refusal shape was
  measured — the `C001` text is unchanged.

## 2. Corpus verdict diff — zero moves (measured, not argued)

- Emitted all **1060 tracked `.gab` files** with the new and the baseline
  emitter (`git stash` + rebuild + emit + pop): `diff -rq` →
  **BYTE-IDENTICAL, all 1060**. The pre-scan explains why: no committed file
  carries a wrap op directly in an `exchange update` body (all go through
  `folge`/`schritt` wrappers, which are calls, not fetch forms).
- Near-misses, each measured after the change:
  - `beispiele/140-atomic-array-counter.gab:43` (`return x +% 1;` in `folge`):
    0 errors, emits, no fetch — parameter path, unchanged. (Task text claims a
    C001→clean move here; see §6 — it was never C001.)
  - `beispiele/gift/1042-*.gab:26` (same helper shape): still `M103` (index
    `0 .. 300` over 256 elements); the wrap site itself lowers.
  - `messung/schreibprobe/S06-fetch-add.gab`: still a CAS loop (call body),
    no fetch — by design.
  - `messung/schreibprobe/S07-wrap-ueber-lokaler.gab`: still `C001` (general
    wrap path untouched — lifting it would move S07 into the emitting
    population, i.e. `MARKE_EMIT_M`, which is out of scope).
  - `laufzeit/sperre.gab`: emits, byte-identical C (wrapper untouched).
- `./emission-pruef`: `== EMISSION: ALL PASS -- 37 durchgestochen, 280 von 280
  uebersetzen, 2 umgekehrte Probe(n) ==`. No `MARKE_EMIT*` touched.

## 3. Scope hygiene (stated for the reviewer)

- Touched: `crates/gabbro-check/src/emit.rs`, `crates/gabbro-check/tests/holform.rs`,
  `beispiele/gift/1052-*.gab`, `beispiele/gift/1053-*.gab`. Nothing else.
- NOT touched: `m1.rs` (checker rules intact — `M104`/`M101`/`M153` rows all
  green unmodified), no Lean (`./lean-bau` not needed; no `Grammatik.lean`
  change), no `MARKE_EMIT*`, no new N codes, gifts only 1052–1053 (1054–1056 free).
- `muster/sperre-muster.gab` (named in the task) does not exist in this tree;
  the warning it would carry stands in `laufzeit/sperre.gab:23-27` and
  `messung/schreibprobe/S07-wrap-ueber-lokaler.gab` — both read, both unchanged.

## 4. Soundness argument — why every accepted case has modulus == width

Cite the check, not the prose: `holwrap_form` returns `Some` only past ALL of
these — `TypExpr::Int` (else `None`); `storage()` unsigned (signed → `None`,
mirroring `M153`); `intty_interval` + `exact_wrap_n` yield `n` with
`n != 0, n <= bits`; operand `constexpr_value ∈ [0, 2^n − 1]`; and then
**`if n != bits { return None; }`**. So accepted ⟺ the binder promises exactly
`0 .. 2^bits − 1`. The general lowering `wrap_c` emits the UNMASKED form
(plain C unsigned arithmetic) exactly when `n == bits`, which C11 6.2.5p9
defines as modulo 2^N — the same operation C11 7.17.7.5 names
`atomic_fetch_add`/`atomic_fetch_sub`. The mismatch shape
(`u32 in 0 .. 65535`, modulus 2^16, where `wrap_c` would mask) is declined by
the `n != bits` line and stays `C001`, pinned by gift 1052/1053 and the two
`die_enge_*` tests. Three further guards ride unchanged: the eight-word C-type
list (no bool/float fetch), the ordering join (`holordnung`), and the
constexpr-only operand (no once-vs-per-pass smuggling). A modulus mismatch is
therefore a refused program, not a TODO.

## 5. Last `./cargo-pruef` result line

`== exit 0; failing tests: 0` (full `cargo build` + `cargo test --no-fail-fast`;
holform suite alone: `test result: ok. 40 passed; 0 failed`).

## 6. What in the task I believe is wrong (stated plainly)

1. **140:43 / 1042:26 "verdicts move from C001 to clean BY DESIGN".** Both lines
   are `x +% 1` over a PARAMETER in a helper fn — the resolving path since lane
   201, never refused. Measured: 140 is `0 errors` + emits before AND after;
   1042 is `M103` before AND after. The C001→clean move happens for the
   DIRECT-binder-wrap shape, which zero committed files carry — so the move
   list is empty and the "expected 140-shape moves" did not occur.
2. **"(exchange binder, locals, parameters …)" as the acceptance set.** What was
   built resolves the binder side inside the fetch gate only. Locals/params as
   wrap OPERANDS stay excluded by the constexpr rule (row 9, load-bearing), and
   general wrap-over-local (S07) stays refused (emission-population reason, §2).
   If Simon wants S07's `ueber_lokale` to lower as masked wrap, that is a
   separate verdict move with its own `MARKE_EMIT_M` booking — not this lane.

## 7. What remains open

- `laufzeit/sperre.gab` still draws through `folge()` (byte-identical C by
  choice); inlining `t +% 1` into the update body is now legal but is a
  follow-up edit, not this lane's.
- Exact-but-nonfetchable binder wraps (`t +% p`, param operand) still end at
  `C001` — the narrowing stops at the fetch gate; the loop path was deliberately
  not taught the binder (same emission-population reason).
- No Lean correspondence lemma for the two new fetch rows (`CFormen*` has no
  fetch form — the same standing gap the bitwise arm already has).
- Reserves left free: N391–395, gifts 1054–1056.

Co-Authored-By: muse-agent-221 <muse-agent-221@noreply.invalid>
