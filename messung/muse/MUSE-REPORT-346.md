# MUSE-REPORT-346: Reviewed organisation plan C2 — GateStub

## What was done

New module `grammatik/Grammatik/X86/GateStub.lean` (389 lines) plus one
additive import at the end of `grammatik/Grammatik.lean`. Caller-side gate
declaration checks mirroring the source gate shape (N063–N067,
`crates/gabbro-check/src/syscall.rs`, sentences `syscall.erklaerung` /
`syscall.stub` in `saetze.rs`) plus caller-stub byte-shape obligations, with
C186 / C187 / M140 as refusal predicates. Callee-side contract (obligation
(c)) stays OPEN. No existing file touched except the one import line; no
second IR, no duplicated evaluator of the 14 pilot forms, no source admission
tightened.

## Exact new definitions

- `TorArt` (`.normal` / `.region` / `.stapel`), `TorDekl` (nummer, ein, aus,
  clobber, errors, gruende, hatOr, art, paramAnzahl) over canonical
  `X86.Register`.
- Decided checks: `regsDistinctB` (N063), `alleGebundenB` + `paramsAbgedecktB`
  (N065 + arity: length = paramAnzahl, indices Nodup, all 0..n-1 present),
  `ausNichtClobberB` (N064), `linuxClobberB` (rcx + r11), `fehlerOkB` (N067:
  distinct errnos, every target < gruende, nonempty map needs `hatOr`),
  `torOkB` (conjunction).
- Refusals: `c186VerweigertB` (region without `or R`), `trampolinVorrat` /
  `freieTrampolin` / `c187VerweigertB` (stack gate, < 2 free registers of the
  emitter-exact pool `r12 r13 r14 r15 rbx` from `emit.rs::syscall_stumpf`;
  occupancy is in-registers + answer register + clobbers, mirroring the
  emitter's `belegt`; `rbp` is never pinned), `StubenWert` (.zahl bare word /
  .zeiger base+extent) / `m140VerweigertB` (site-indexed: a number at a site
  index that expects a pointer is forged; tags are given, detection is the
  checker's business).
- Stub shape: `trapBytes` (`0F 05`, literal only), `trapBytes_pin`,
  `stubEndsTrapB`, `bindungErstelltB`, `zeugenMoves`, `zeugenStub`.
- Decode: `RohKlasse` (`.ok` / `.grund errno` / `.hardware`), `torKlassifiziere`
  (negative `-4095..-1` against the errors map, else range-checked ok, else
  hardware outcome). Named `torKlassifiziere` (not `klassifiziere`) because
  `Grammatik.X86.OverlapRefusal` on master already owns `klassifiziere`
  (overlap classifier over address lists) — the integration gate failed on
  exactly this duplicate; renamed mine, verified zero identifier overlap
  against every top-level name of `OverlapRefusal.lean` and every other
  master `X86/*.lean` module for all owned identifiers.

## Exact new theorems

- Admission: `schreibTor_ok` (write-shaped witness admitted).
- Refusals: `torDoppelt_verweigert`, `torAusClobber_verweigert`,
  `torUngebunden_verweigert`, `torOhneR11_verweigert`,
  `torDoppelErrno_verweigert`, `torFremdGrund_verweigert`,
  `torRegionOhneOr_verweigert`, `schreibTor_kein_c186`,
  `torStapelOhneTrampolin_verweigert`, `torStapelAntwortBelegt_verweigert`
  (answer register inside the pool counts as occupied: `aus = rbx` with
  `r12`-`r15` clobbered is refused; the pre-fix callee-saved model with `rbp`
  cleared this gate), `schreibTor_stapel_kein_c187`,
  `m140_geschmiedet` (site-indexed: bare number at pointer site 1),
  `m140_echt_kein_fund` (pointer with extent not forged),
  `m140_zahl_erlaubt` (number at a non-pointer site not forged).
- Stub: `zeugenMoves_ok`, `zeugenStub_trap`,
  `zeugenStub_prefix_dekodiert` (via canonical `roundtrip_movReg64`).
- Decode: `torKlassifiziere_ebadf` (-9 → reason 0), `torKlassifiziere_ok`,
  `torKlassifiziere_unbekannt` (-22 → hardware), `torKlassifiziere_ausserhalb`
  (99999 → hardware), `torKlassifiziere_zaun` (-5000 → hardware).
- Joint: `torStub_zeuge` (admission + moves + trap suffix + EBADF decode +
  memory-change existential via canonical `write_read_zeuge`).

## Verification

- `./lean-probe grammatik/Grammatik/X86/GateStub.lean`: 0 errors. Axioms per
  `#print axioms`: subset of `[propext, Quot.sound]` only (`torStub_zeuge`:
  `[propext, Quot.sound]`); no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
  (only `admitted`/`admits` prose and `#print axioms` lines match the word
  grep); every premise used; no `Prop`-typed premise; no per-program rule.
- `./lean-bau` last line (previous commit, quiet machine):
  `Build completed successfully (386 jobs).`
- Goal probe (`BeweisAtomar.lean`, previous commit): `gabbro_ziel` still
  depends on exactly `[propext, Classical.choice, Quot.sound]` — unchanged.
- Post-recovery fix (this commit): C187 pool corrected from generic
  callee-saved (`rbx rbp r12-r15`) to the emitter-exact trampoline pool
  (`r12 r13 r14 r15 rbx`, `emit.rs::syscall_stumpf`, `belegt = regs_in +
  regs_out + clobbers + fest_zerstoert`); M140 generalised from a bare
  `(istZahl, benutztAlsZeiger)` pair to a site-indexed tagged-operand list.
  Both re-probed at 0 errors before commit.
- Integration-gate repair (this commit): the gate failed with
  `import Grammatik.X86.GateStub failed, environment already contains
  'Gabbro.Grammatik.X86.klassifiziere' from Grammatik.X86.OverlapRefusal`.
  My `klassifiziere` (+ 5 `klassifiziere_*` theorems) is renamed to
  `torKlassifiziere` (`torKlassifiziere_*`); no semantics changed.
  Verified: (a) `./lean-probe GateStub.lean` 0 errors after rename, axioms
  unchanged; (b) read-only check of the master tree: zero identifier overlap
  between my module's 24 top-level names and every top-level name in
  master `X86/OverlapRefusal.lean` and all other master `X86/*.lean`
  modules; (c) full-build output shows `GateStub.olean` rebuilding cleanly
  under the new names.

## CONCRETE BLOCKER (environmental, not content)

- The final aggregate step (`[385/386] Building Grammatik`, also
  `./lean-probe grammatik/Grammatik.lean` and the `BeweisAtomar` goal probe,
  which passed 40 minutes earlier with zero tree change) currently crashes
  on THIS machine with `libc++abi: terminating ... failed to create thread`
  (exit 134) — 6 consecutive failures over ~50 minutes. 385/386 modules,
  including the renamed `GateStub.olean`, build cleanly.
- Proven independent of my change: `git stash` of both owned files
  (pristine committed tree) crashes identically on the same step; `git stash
  pop` restored the repair. The gate machine is unaffected (its log shows
  lean elaborating normally — it reported the real `klassifiziere`
  collision, which this commit removes).
- This commit is therefore made with module-level green (`lean-probe`
  0 errors) and an honestly red aggregate step. A fresh independent review
  of the changed commit is still required; the reviewer should re-run
  `./lean-bau` on a quieter machine or at the gate.

## What remains open (see CUTS)

Caller side only (IMAGE-ABI section 7 caller half). OPEN: trap semantics (no
`Befehl` form, literal `0F 05` shape only); callee-side obligation (c);
bare-metal `int $0x80` clobber rule (`linuxClobberB` is Linux-only); kernel
meaning of numbers/tables/costs; source-to-byte correspondence; refused-form
scalar fallback (consumer obligation); N066 implicit (unrepresentable type,
not a refusal). Full final-byte/source/hardware correspondence OPEN.

## Task remarks (believed wrong or noteworthy)

1. N066 has no Bool in this file by construction: `TorDekl` ranges over the
   canonical 16 `Register`, so an unknown register cannot be stated. This
   mirrors the source check without duplicating it; the report states this
   openly rather than inventing a refusal.
2. Lean `{ s with a := .x, b := ... }` multi-field update with dot-notation
   first value failed to parse in this tree; single-field `with` updates and
   explicit `TorArt.stapel` in struct literals were used instead.
3. The joint `_zeuge` reuses the canonical `write_read_zeuge` memory witness
    from `Speicher.lean` (name `zeugenSpeicher` was already taken there)
    rather than minting a second memory.
4. C187 scope note: the emitter's trampoline pins exactly
    `["r12", "r13", "r14", "r15", "rbx"]` and `belegt` includes `regs_out`
    (`emit.rs`, trampoline block of `syscall_stumpf`); an earlier draft used
    the generic callee-saved six with `rbp` and ignored the answer register.
    Fixed before this commit; `torStapelAntwortBelegt_verweigert` pins the
    divergence.
5. M140 scope note: this file mirrors only the refusal shape over caller-
    supplied tags (`StubenWert`, site list); which site expects a pointer is
    the checker's type business (`m1.rs`), stated in CUTS, never derived here.
