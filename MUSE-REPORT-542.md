# MUSE-REPORT-542: N9 StackUnwind (lane 542)

## Task

N9 `grammatik/Grammatik/X86/StackUnwind.lean` (NEXT-PROOF-WAVE §3):
frame-chain well-formedness + guard-page facts for actual pilot
push/pop/call/ret, over `Stapel.Rahmen/Belegung`, `Regionen`,
`Byteschritt` fetch. WITNESS+: nested call/return restoring rsp with a
memory store. WITNESS-: return to a non-executable or guard address
refused. Reviewer: 526.

## What was delivered

New file `grammatik/Grammatik/X86/StackUnwind.lean` (~820 lines, 21
theorems, 0 `sorry`/`admit`/`axiom`/`native_decide`), plus one additive
umbrella import in `grammatik/Grammatik.lean`. No existing file
touched otherwise; no friend path, no second IR, no new executor (all
steps reuse `Ausfuehrung.schritt`, `Byteschritt` fetch, `Stapel`,
`Regionen`).

Definitions: `KetteOk` (both frames checked, inner top at/below outer
base), `rspImRahmen` (rsp inside a frame extent, inclusive top),
`Wache` (declared extent with no rights), witness states/values
(`zeugS`, `zeugOben`, `zeugM1`, `zeugS1`, `zeugS2`, `zeugMc`,
`zeugSc1`, `zeugSc2`, `zeugNobenP`, `zeugNmp`, `zeugNS2`, `zeugNS3`,
`zeugNS4`, `zeugRet*`, `zeugWache*`, `zeugFlags`, `zeugSpeicherRW`,
`zeugReg42`).

Theorems (all generic over arbitrary states/values; every premise used):

- `rsp8_runter_rauf` — one-word down/up restores rsp (arithmetic only).
- `push_pop_wiederhergestellt` — actual push then pop into another
  register restores rsp and delivers the pushed value (via accepted
  `schritt_push64_erfolg` / `schritt_pop64_reg` + `read64_nach_write64`).
- `call_ret_wiederhergestellt` — actual call then ret restores rsp and
  lands on the stored post-decode address.
- `verschachtelt_wiederhergestellt` — nested call/push/pop/ret
  restores rsp and the return address, delivers the inner value, and
  preserves all three permission maps (bytes-only stores). Needs the
  explicit `Disjunkt` premise keeping the inner store off the saved
  return address (adjacent slots, carried by `read64_rahmen`).
- `nicht_ausfuehrbar_verweigert` — no execute permission at rip means
  empty fetch (`decode [] = none` via `decode_nichts_leer`) hence
  `byteschritt = .verweigert`. Data readability is never consulted.
- `ret_ins_nicht_ausfuehrbar_verweigert` — ret into a non-executable
  target admits no byte step. Guard regions carry `ausfuehrbar =
  false`, so guard returns refuse here too.
- `wache_schreibschutz` — a write-denied initialised `Regionen` region
  answers `schreibbar8 = false` at its base (guard footprint closed).
- `wache_push_verweigert`, `wache_call_verweigert` — guard below the
  top loudly refuses push/call (via `write64_verweigert`).
- `ausrichtung_ohne_rahmen` — concrete: 16-aligned rsp far outside the
  frame is aligned and not in the frame. Alignment never substitutes
  for frame/guard validity.
- `kette_ok_sonde` — concrete adjacent checked frames satisfy
  `KetteOk`; the boundary top counts as inside.
- `belegung_gerettet_schranke` — under a fitting `Belegung`, every
  callee-save index names a frame slot.

Joint witnesses (each instantiates ALL premises of its target on one
concrete run; positives carry an observed zero-to-nonzero byte change):

- `push_pop_wiederhergestellt_zeuge` (push 42 at 8184, pop to rbx),
- `call_ret_wiederhergestellt_zeuge` (call stores 4101, ret restores),
- `verschachtelt_wiederhergestellt_zeuge` (call + inner push/pop +
  ret, disjoint slots 8184/8176, outer store changes memory),
- `ret_ins_nicht_ausfuehrbar_verweigert_zeuge` (ret to 12288,
  non-executable, byte step refused),
- `wache_push_verweigert_zeuge` (push below a write-denied guard
  refused),
- `belegung_gerettet_schranke_zeuge` (concrete fitting layout).

Axioms: every theorem depends only on subsets of
`propext/Classical.choice/Quot.sound` (machine-printed at file end);
no `sorryAx`. `decide` witnesses are axiom-free.

## Build evidence

- `./lean-probe grammatik/Grammatik/X86/StackUnwind.lean`:
  `0 error(s)`, exit 0.
- `./lean-bau` (full project): `Build completed successfully
  (415 jobs).`

## Open / CUTS (in-file)

No decoder/TSO/source/ABI/loader/cost/image claim. Interrupts,
concurrency, callee-save and entry contracts, external ABI byte
correspondence stay OPEN. Full source-to-final-bytes validation OPEN.
`Wache` covers the machine-checked permission side only; OS guard-page
installation is user logic, never an assumption.

## Notes on the task (nothing believed wrong)

- The wave's "`table` some function writes" witness formula is
  source-level; the pilot analogue used here (observed memory-byte
  change on a reached `schritt` run, as in accepted `Stapel.lean`) is
  recorded in each `_zeuge`.
- Two toolchain facts cost cycles: `simp` does not prove
  `(R - 8) + 8 = R` (used `BitVec.sub_add_cancel`); `by_contra` is not
  available (used `by_cases`); `decide` needs `unfold OhneUmbruch`
  first. `rw`'s auto-rfl does not unfold plain defs (used `congrArg`
  / `simp only` for successor projections).
