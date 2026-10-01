# MUSE-REPORT-598: Checked validator to loaded fetched execution

## Task

Connect accepted `ValidatorSkeleton.valX86`/`valX86Voll`, `DecodingCoverage`
and `LoadedExecution` to an admitted mapped entry's fetch/decode/execution
consequence, without assuming entry coverage or confusing whole-section
decode with entry boundary. Prove a concrete counterexample if the current
Bool admits an interior entry, add a separate optional strengthened check
with generic soundness, plus a memory-changing loaded store witness and
interior/truncated/BSS/permission refusals. No `valX86_sound`/source claim.

## Result

Delivered in `grammatik/Grammatik/X86/ValidatorExecution.lean` (new file,
`import Grammatik.X86.ValidatorExecution` appended to
`grammatik/Grammatik.lean`; nothing else touched).

**New definition** (optional, old `valX86`/`wohlgeformt` untouched):

- `valEintrittStark p bild bias e reg fl : Bool` — checked mapping AND
  entry containment AND executable byte at the entry AND successful
  `fetchDekodiert` from the actual loaded bytes at the entry state.

**Generic soundness** (all premises used; derived through the actual fetch,
never assumed):

- `valStark_wohlgeformt`, `valStark_eintrag`, `valStark_ausfuehrbar`,
  `valStark_fetch_exist`, `valStark_fundstelle` (names the actual member
  section with bounds + execute flag via `List.any_eq_true`).
- `valStark_gibt_deckung` — entry-at-decoded-start: containment AND
  executable byte AND the fetched bytes decode to a covered pilot form
  (`decktAb`) at its exact length with executable prefix (via
  `fetchDekodiert_entspricht` + `decode_abdeckung`).
- `valStark_schritt` — loaded-step consequence: containment AND
  `byteschritt = .weiter s'` for the fetched instruction (via
  `byteschritt_weiter`).

**Counterexamples** (old Bool admits, fetched execution refuses):

- `innenBild` (one 3-byte `movReg64` `72 137 216`, entries at base
  `0x1000` and interior `0x1001`): `innen_gegenbeispiel` —
  `valX86 = true`, interior contained, fetch `none`, stark refuses
  interior and admits base.
- `bssEintrittBild` (same bytes + 5-byte BSS tail, entry `0x1005`):
  `bss_eintritt_gegenbeispiel` — `valX86 = true`, BSS entry contained,
  fetch `none`, stark refuses BSS entry, admits base.
- `stumpfBild` (lone `232`): `stumpf_fetch_verweigert` — the 15-byte
  loaded window (`eintrittDekodiert`) decodes by reading zeros past the
  executable boundary while the actual executable fetch refuses. This is
  why the strengthened check is fetch-based, not window-decode-based.
- `innenBildOhneExec` / `bildStoreWx`: `permission_verweigert`,
  `valStark_store_wx_verweigert` — cleared execute / set writable
  refuse mapping, fetch and stark.

**Positive witness**: `valStark_store_ok` (biased store entry admitted),
`valStark_store_start` (stark state is definitionally `bildStoreStart`),
joint `valStark_store_zeuge` — admission, store fetch, step moves 42
into data (zero before), `schreibLese_zeuge`, interior refusal.

## Verification

- `./lean-probe .../ValidatorExecution.lean`: 0 errors. `#print axioms`
  for every theorem: at most `[propext, Quot.sound]` (standard subset).
- `./lean-bau`: Build completed successfully (440 jobs).

## Open (not claimed)

No `valX86_sound`, no source correspondence (IR287 pending, no substitute
invented), no hardware/silicon claim, no multi-step control flow,
relocation re-decode, TSO/GX bridge, costs or termination (see file CUTS).

## Notes for the coordinator

- The task is correct as stated; the interior gap is real and proved.
- Producer interface used: `valX86`/`bildDeckung`, `decode_abdeckung`,
  `eintrittDekodiert`, `bildZustand`/`bildStore`, `fetchDekodiert`/
  `byteschritt`/`fetchDekodiert_entspricht`/`byteschritt_weiter`,
  `schreibLese_zeuge`. Consumer: whatever closes `valX86_sound` can
  reuse `valEintrittStark` + `valStark_gibt_deckung`/`valStark_schritt`
  as the entry leg instead of raw containment.
- Lean pitfalls met: (1) multi-line `{...}` struct literals nested in a
  `[...]` list fail to parse at the trailing comma — used standalone
  section defs (`innenCode`, `stumpfCode`, `bssEintrittCode`,
  `innenCodeOhneExec`) instead; (2) `cases`/`match` on a scrutinee
  occurring in the goal substitutes it in the goal — used
  `Option.ne_none_iff_exists'` + `obtain` + `cases` on the fresh pair.
- Suggested next independent tasks: (a) per-entry decode-boundary
  traversal from each listed entry (fuel-bounded, fail-closed) reusing
  `decodeFuel`; (b) patched-relocation-site re-decode correspondence;
  (c) multi-step control-flow validation over admitted entries.
