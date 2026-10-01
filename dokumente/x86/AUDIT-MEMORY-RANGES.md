# Audit: MEMORY-RANGES — Speicher / Regionen / SpeicherKommutation

Owner: lane 405. Scope: actual current implementations only; no broad architecture
review, no second IR, no new Lean. Method: read the three audited modules plus the
definitions they consume (`X86/Typen.lean`, `X86/Ausfuehrung.lean` steps,
`X86/Zugriffe.lean`, `X86/Stapel.lean`, `X86/OverlapRefusal.lean` as the main
consumer), and reproduced six positive/negative probes in the private file
`.tmp/probe405/P1.lean` (uncommitted, all `decide`/`rfl`, `./lean-probe` 0 errors).
Line references are against master at `0b3132b7` plus lane-312 history.

## 1. What was checked and found correct within its stated claim

- **Wraparound base (`Speicher.lean` ll. 52–73).** `addrOff_inj8` needs no
  no-wrap hypothesis, and that is correct: `addrOff a i = a + ofNat i` is a group
  action, so distinct small offsets stay distinct for every `a`, including
  near `2^64-1`. `OhneUmbruch` (l. 160) is demanded exactly where `Nat`
  reasoning starts (`ohneUmbruch_addrs`, `disjunkt_von_intervallen`). No bug.
- **Last-byte bounds.** `lesbarN`/`schreibbarN` (ll. 138–146) check bytes
  `0..n-1`, last byte included; `initialisiere_schreibbar8`/`_lesbar8`
  (`Regionen.lean` ll. 372–421) discharge all eight indices explicitly;
  `rahmenOk` (`Stapel.lean` l. 46) bounds the whole frame including its last
  byte (`spitzeNat ≤ 2^64`). No off-by-one found.
- **Permission/footprint preservation.** `write64_erhaelt_berechtigungen`,
  `lesbarN_update`, `schreibbarN_update`, `write64_rahmen`, `read64_rahmen`
  (ll. 252–373) are tight: a store replaces only `bytes`, permissions are
  independent fields, refusal (`none`) changes nothing by construction.
  Read-after-write honestly requires readability *besides* writability
  (`read64_nach_write64`, l. 327) — correct, since the fields are independent.
- **Allocation identity/aliasing (`Regionen.lean` ll. 92–351).**
  `reserviere` refuses `len = 0` and `ausr = 0`, checks ceiling *and*
  `≤ 2^64` *and* lower bound; `reserviere_frisch`/`_decke`/`_innerhalb` and
  the `alleUnten` threading (`reserviere_disjunkt_unten`,
  `reserviere_haelt_alleUnten`) prove freshness against every tracked region.
  The disjointness premise is an explicit consumer obligation (`hinv`), not
  smuggled in. No bug.
- **Commutation honesty (`SpeicherKommutation.lean` ll. 64–142).**
  `write64_kommutiert` takes *both* orders' success as premises and concludes
  byte-extensional agreement plus unchanged permissions — no atomicity is
  claimed, per-byte events stay hooks for the TSO bridge, and `StabilFuss`
  (ll. 150–198) explicitly leaves publication/locks to the source level. The
  `kein_atomarer_zugriff`/`keine_ablauf_spur` empty types (in `Zugriffe.lean`)
  close the two stronger misreadings. No false theorem.
- **Wrapped footprints are refused loudly, not admitted.**
  Probe P2 (`.tmp/probe405/P1.lean`): `Fuss (natAdresse (2^64-4))` against the
  top 8-byte region gives `fussEnthalten = false` by `decide` — wrapped bytes
  map to small `toNat`s outside the `Nat` extent. The model *allows* wrapped
  accesses at the `Speicher` level (permission-gated) but no admission checker
  accepts them. Correct separation of mechanism vs admission.
- **Classifier conservativity (`OverlapRefusal.lean` ll. 87–98).**
  Probe P3: same-set-different-order lists classify `.unbekannt`, hence refused
  by `aliasZulassen`. For genuine `Fuss` lists the head determines the base, so
  `.gleich` coincides with same-base; for arbitrary lists the order-sensitivity
  fails safe. `fussDisjunktB_klingt` (ll. 119–127) is a real soundness lemma.
  No bug.
- **CUTS match the code.** Every gap listed below under "open/missing" is
  either already in the files' CUTS blocks (narrow commutation, TSO, source
  correspondence) or a precisely new consumer-side item (F3–F5). No theorem
  statement overclaims, except the one doc sentence in F1.

## 2. Findings (prioritised, each with repair)

### F1 — Doc sentence overclaims: "empty regions touch nothing"
`Regionen.lean` l. 50 (`regionDisjunkt` doc): an empty region whose basis lies
strictly inside another region is *not* disjoint — probe P1:
`regionDisjunkt {basis := 5, len := 0, …} {basis := 0, len := 10, …} = false`
by `decide`. Impact: none on soundness (`reserviere` refuses `len = 0`, so
empty regions never arise from allocation; no theorem depends on the sentence).
Repair: reword to "empty regions at the boundary touch nothing" or state the
exact `decide` condition. Severity: cosmetic. Owner: whoever next touches
`Regionen.lean`.

### F2 — `sichereWort`/`ladeWort` do not check the frame bound (silent wrap at def level)
`Stapel.lean` ll. 81–88 check the slot index and (via `write64`/`read64`) the
memory permissions, but not `spitzeNat ≤ 2^64` / `rahmenOk`. Probes P4a/P4b/P5:
`rahmenOk {basis := 2^64-8, tiefe := 32} = false`, yet slot 1 computes to
machine address `0` (`schlitzAddr 1 = ofNat 64 (2^64) = 0`) and
`sichereWort speicherZeuge rahmenWrap 1 42` still succeeds (`∃ m', … = some m'`).
Full slot *aliasing* needs `tiefe ≥ 2^64` (Nat), but slot *misplacement* to
address zero needs only an 8-byte wrap. Every disjointness theorem correctly
takes `hle` as a premise, so no theorem is false — but a consumer that saves
without establishing `rahmenOk` gets silent misplacement with no `none`.
Repair (pick one, P2 priority): (a) add a bound-checked wrapper
(`sichereWortOk` requiring `rahmenOk = true`) and point the layout/ABI
consumer at it; or (b) record a named consumer obligation that every
`sichereWort` call site discharges `spitzeNat ≤ 2^64` first. Not a soundness
bug in the current files; a pitfall with a concrete trigger.

### F3 — Missing bridge: no rsp↔frame connection; push underflow gated by permissions only
`stapelOben s = rsp - 8` (`Zugriffe.lean` l. 37; same shape inline in
`Ausfuehrung.lean` l. 107) wraps when `rsp < 8`; `schritt`'s push path then
attempts `write64` at the wrapped address, refused only if the permission maps
say so. Nothing links `rsp` (a `Wort`) to any `Rahmen`/`Belegung` (Nat-based):
grep over `X86/*.lean` shows zero lemmas connecting `stapelOben`/`rsp` to
`schlitzAddr`/frames. The `OverlapRefusal.lean` witnesses (`push_in_traeger_*`,
ll. 229–234) show the *intended* discipline (push footprint inside a carrier)
but it is not a checked predicate over `schritt`. Repair (P2, owner: layout/ABI
work, cf. WORK-ALLOCATION C1): a decided `rspInRahmen` predicate plus
push/pop-against-frame lemmas (`zugriff … Kelch` footprint ⊆ frame slots ⇒
permission facts). Missing task, not a bug in the audited files.

### F4 — Missing bridge: region admission ⇒ memory success, interior offsets
`zugriffOk` admits against `Region` rights while `read64`/`write64` consult
`Speicher` maps; the only bridges are at the region *base*
(`initialisiere_schreibbar8`/`_lesbar8`, `Regionen.lean` ll. 372–421, address
`natAdresse r.basis`), and `einzelTraeger_wertUeberein`
(`OverlapRefusal.lean` l. 143) takes `hwr`/`hrd` as premises. For a region
larger than 8 bytes there is no lemma giving `schreibbar8`/`lesbar8` at an
*interior* admitted address of initialised memory. Any AccessList/IR consumer
(WORK-ALLOCATION B1; lane-287 interface pending) that goes
`zugriffOk → schritt succeeds` must prove this per site today.
Repair (P2): lemma `initialisiere_*8_at_offset`: `inRegion r (basis+k)`-style
premise + `initialisiere` ⇒ permission facts at `natAdresse (r.basis + k)`,
following the existing base proofs. Missing lemma, not a bug.

### F5 — Missing lemma: ceiling-free allocator has no freshness/disjointness fact
`freiReserviere` (`Regionen.lean` ll. 433–442) advances a bare cursor with no
`belegt` tracking and no `alleUnten` analogue; successive allocations are
disjoint by construction but no theorem states it (contrast `reserviere_*`
ll. 186–351). Repair (P3, tiny): `freiReserviere_disjunkt` for two successive
successes. Missing lemma, not a bug.

### F6 — Known-incomplete, acknowledged: narrow + cross-width commutation
`SpeicherKommutation.lean` l. 314–316 CUTS already says only 64-bit forms
commute and `readBreite`/`writeBreite` commutation is unstated. Added precision
for the consumer: cross-width overlap (e.g. `write32` at `a` then `read64` at
`a`: upper bytes stale) has no frame/read-back lemma anywhere, and the
TSO-bridge/spill consumer (WORK-ALLOCATION B3/B4, narrow-carrier work A1) will
need at least the narrow-narrow and narrow-covering frame facts. Keep as
tracked incomplete deliverable; do not present the 64-bit commutation as
covering spills until this lands.

## 3. Explicit non-findings (checked, no action)

- No invented unaligned-CPU-fault claim exists in the audited files; alignment
  is validator admission (`addrAusgerichtet`, `zugriffOk`, `ausr = 0` refuses)
  while hardware accepts wrapped/permission-gated accesses — the
  fault-vs-refusal distinction is respected, so no repair is filed for wrapped
  `Speicher`-level accesses being *possible*.
- `reserviere_voll_verweigert`, `reserviere_leer_verweigert`,
  `ausricht_null_verweigert`, `write64_verweigert*`, `sichereWort_ausserhalb`,
  `sichereWort_verweigert`, `spanne_verweigert_*`, `gegenbeispielC_verweigert`
  are genuine negative cases, not vacuous: each fires on a concrete
  misaligned/over-ceiling/out-of-frame input (several re-decided in probes).
- `freiReserviere_ohne_statik_gebunden` claims only "no static bound below
  `2^64`", each extent still `≤ 2^64` — read the statement, it does not claim
  physical unbounded addresses. No action.
- `zugriff` potential-vs-realised discipline (`Zugriffe.lean` §§3–7: footprint
  from pre-state, success exactly when `schritt` succeeds) is stated and used
  consistently by `erfolg_*_im_fuss`. No action.

## 4. Consumer-gap summary for the direct-compiler chain

| # | Gap | Consumer blocked | Priority |
|---|---|---|---|
| F2 | bound-checked frame save wrapper or named obligation | layout/ABI (C1), any `sichereWort` user | P2 |
| F3 | `rsp`-in-frame predicate + push/pop-against-frame lemmas | layout/ABI (C1), SpillPrivate (B3) | P2 |
| F4 | interior-offset region⇒permission bridge | AccessList (B1), IR lowering (287) | P2 |
| F5 | `freiReserviere` freshness/disjointness lemma | ceiling-free users | P3 |
| F6 | narrow + cross-width frame/commutation facts | narrow carriers (A1), TSO spill (B3/B4) | P3 (tracked) |
| F1 | one doc sentence reword | next editor of `Regionen.lean` | P4 |

No change to the goal, checker, emitter, or any accepted module is required by
this audit. The audited helpers are correct within their stated claims; the
work above is all bridge/pitfall/missing-lemma work, none of it a false theorem
or a broken model semantic.
