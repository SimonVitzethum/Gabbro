# MUSE-REPORT-720: Real selected integer bytes on shared TSO execution

Lane 720. Clone `/home/simon/Dokumente/gabbro-muse/a720`, branch `muse/720`
(verified at start). Owned files only: new module
`grammatik/Grammatik/X86/ConcurrentIntegerExecution.lean` (~2050 lines),
additive umbrella import in `grammatik/Grammatik.lean`, this report.
`HardwareExecution.lean` not edited (layered over, as tasked). No network,
no push, queued wrappers only (`./lean-probe` per increment,
`./lean-bau` for the whole project).

## What was built

Width-selected (1/2/4/8-byte) integer load/store execution over the canonical
`HwMaschine` (lane 660), with ordered byte issue, youngest-own forwarding,
ordered drain, and register/partial-register effects derived from the accepted
scalar producer equations. No SC word effect is substituted for a buffered
access anywhere; word single-event claims go through `WortGruppe` with
cross-core interleavings, never from alignment.

- §1 ops/addresses: `ConcIntOp` (load/store at explicit `Breite` through
  base plus displacement), `concAddr` (= accepted pilot `effAddr` on the
  pre-state file). Theorems: `concAddr_prestate`, `concAddr_alias_beispiel`
  (no injectivity), `concAddr_basisForm`, `concAddr_store_basisForm`
  (selected `adrEff` bridge, accepted equation symmetric).
- §2 byte entries: `entriesOf` (little-endian `wortByte` bytes, oldest
  first), `concBytes`/`concBytes_eq`, `entriesOf_laenge`,
  `entriesOf_b64` (= accepted `wortEintraege`), `entriesOf_b8_pin`,
  `entriesOf_in_fuss`.
- §3 admission + issue: `concAdmitted` (canonical address, no-wrap range,
  per-direction `lesbarN`/`schreibbarN`); refusal splittings
  (`concAdmitted_braucht_kanonisch/bereich/schreibbar/lesbar`,
  `concAdmitted_lesbar/schreibbar`); `concIssue` (gate first, then the
  accepted `issueListe` fold): `concIssue_braucht_gate`,
  `concIssue_haengt_an` (oldest-first append), `concIssue_kein_speicher`,
  `concIssue_mem` (identical memory), `concIssue_berechtigungen`,
  `issueListe_berechtigungen/anderer_kern/erreichbar`,
  `concAdmitted_issue_stabil`, `lesbarN_byte`.
- §4 forwarding loads: `concLoad` (every footprint byte through accepted
  `loadByte`, assembled exactly like `read8/16/32`/`bytesWort`);
  `concLoad_braucht_gate`; `neuestens_entriesOf` (buffer resolution per
  width over the exact entry list); `concLoad_ohne_eintrag` (buffered =
  sequential where nothing forwards -- the no-substitution bridge);
  `loadByte_nach_concIssue_leer` + `concLoad_nach_concIssue`
  (whole-access forwarding to the accepted read-after-write values at
  every width, proved by the same `wortByte`-unfold + `omega` pattern
  the accepted proofs use).
- §5 machine adapters: `concStoreMaschine` (pre-state address/value,
  buffer issue, RIP advance, registers/flags kept) with flags/regs/rip/
  kein_speicher/puffer/wf/erreichbar preservation;
  `concLoadMaschine` (forwarded value merged via accepted
  `mergeRegNarrow`/`regSet`) with flags/dst/fremd/rip/speicher/puffer/
  wf, `b32_clears` (accepted fit lemma), `b64_full`, length + gate
  refusals (pre-fault order: refusal = `none`, no successor);
  `HwSchritt` correspondence: `concLoadMaschine_b8_lade`
  (via `concLoad_b8_beobachtet`), `concStoreMaschine_b8_gibAus`
  (via `issueListe_einzeln`); `concDrain` with `concDrain_spuele`
  (canonical `.spülung` event + `flush_schreibt_kopf`) and
  `concDrain_wf`.
- §6 word discipline: `concIssue_b64_gruppe` (our 64-bit issue
  establishes the accepted `WortGruppe` from empty + foreign-free
  buffers), `concWort_liest_zurueck` (accepted grouped read-back),
  `concWort_verflochten_liest` (accepted interleaved read-back with
  real foreign accesses from finite checks), `concGruppe_verweigert_lock`
  (LOCK stays refused on grouped states). No alignment premise is
  taken on purpose: byte drains are alignment-agnostic and alignment
  alone never groups (accepted `ausrichtung_reicht_nicht`, cited).
- §7 codec boundary: `concDecode` admits exactly the accepted memory
  producers -- pilot `load64`/`store64` (`concDecode_load64/store64`
  via accepted round trips) and narrow `store32`
  (`concDecode_store32` via accepted round trip + pilot disjointness);
  register-only rows refuse (`concDecode_mov32rr_verweigert`);
  `concDecode_nur_b64_b32` proves every success is one of the three
  (8/16-bit memory rows stay PENDING, not reinvented); decoded lengths
  pass `laengeOk` on both paths (`concDecode_laenge_ok` via accepted
  `decode_abdeckung`/`decodeNarrow_abdeckung`).
- §8 joint witness `concWit_zeuge`: core 0 fetches a real narrow
  `store32 [rbx], rax` (7 bytes) from actual executable memory,
  decodes through our boundary (`concWit_fetch_decode`), issues
  width-selected with register/flag/memory discipline
  (`concWit_store_rip/buf/mem_still/flags/rax`, `concWit_addr`),
  forwards to its own load (`concWit_weiterleitung`), hides from core 1
  (`concWit_fremd_alt`), drains observably into shared memory
  (`concWit_spuelung`: 0 becomes `0x04`, `concWit_fremd_neu`), with a
  reached store + TSO run in the existential. Negatives beside it:
  core-1 fetch refusal, dark-memory issue/load refusals, canonical-hole
  and wrap-edge refusals, tearing refusal (`concWitTeil_keine_gruppe`
  via accepted partial-buffer lemma), overlap refusal
  (`concWitOverlap_keine_gruppe`), and the address alias
  (`concWit_alias`: `rax = 8176` + disp 16 names the same cell as
  `rbx + 0`).

## Checks

- `./lean-probe grammatik/Grammatik/X86/ConcurrentIntegerExecution.lean`:
  `== 0 error(s) in the COMPLETE output` (final; every increment probed).
- `./lean-bau`: `Build completed successfully (482 jobs).`
- `#print axioms` for every major theorem (61 prints at file end): all
  within `propext`, `Classical.choice`, `Quot.sound` (most need only
  `propext`/`Quot.sound`; `Classical.choice` arrives through reused
  accepted round-trip lemmas). No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`. Full project (incl. `gabbro_ziel` owners)
  builds green.
- Manual provenance: Intel SDM 325462-093US via clone-local
  `.tmp/HARDWARE-REFERENCES/REFERENCES.json` +
  `intel-instruction-reference.txt` (MOV/MOVZX/MOVSX/ADD/SUB/TEST/LEA
  headings); headings are provenance, never silicon proofs (stated in
  CUTS). `DIRECT-COMPILER-DESIGN.md` §§2A/2D/3/5 read (root file, not
  `dokumente/`).
- No `ZEUGE:` targets in the task and no premise quantifies over
  program syntax, so no mechanical `_zeuge` obligation; `concWit_zeuge`
  is the reached, memory-changing joint inhabitation (store +
  forwarding + foreign-read/drain + all refusal shapes jointly).

## Open (not claimed)

Per-access TSO-to-W/GX simulation; source/contract/checker
correspondence; 8/16-bit (and 32-bit load) byte codecs; LOCK RMW
producer; faults beyond carried permission/canonical/refusal outcomes;
interrupts, timing, liveness; any silicon/hardware correspondence.
See CUTS for the exact list and the consumer interface
(`concStoreMaschine`/`concLoadMaschine` + preservation,
`concDrain`, `concIssue_b64_gruppe`, `concWort_liest_zurueck`,
`concWort_verflochten_liest`, `concDecode` + coverage/length,
`concWit_zeuge`).

## Task feedback and pitfalls hit

- Nothing in the task statement is wrong; one location note:
  `DIRECT-COMPILER-DESIGN.md` lives at repo root, not `dokumente/`.
- `cases h : term` abstracts occurrences of `term` in the GOAL
  (standard Lean dependent elimination, but it bit three times):
  in `concLoadMaschine_dst` the goal mentions `concLoad`, so the
  abstracted equation is closed by `rfl` (kept `hl` used via
  `simp [hl] at h`); same pattern in the joint witness existential
  and in `issueListe_einzeln` (restructured to `by_cases`-free
  obtain/`rw` style). Follow-up lanes casing on `concIssue`/
  `concLoad`/`issueByte`/`loadByte` where the goal mentions them
  should expect this.
- `{ x with ... }` structure updates must stay on ONE source line in
  this tree (parser breaks otherwise; hit in the store-adapter def,
  two witness statements, and the reachability helper).
- `simp` leaves `if True then ... else ...` residues here (used
  explicit `rw [if_pos ...]` closers for gate/permission `if`s).
- `concWitM0_wf` mirrors the accepted `hwWitStart_wf` shape
  (`intro c f _; cases f <;> rfl`): admission is vacuous on full
  silicon, so the premise is genuinely unneeded -- flagged
  transparently rather than worked around. (An attempt via
  `hwWf_aus_zugelassen` + per-feature lambda produced a `sorryAx`
  and was reverted.)
- `rw [h] at h`-style `cases h` on `some X = some (m', e)` pairs:
  `simp` pre-splits these into conjunctions, so `cases h` silently
  stops substituting -- `obtain` + `subst` is the robust form
  (seen in `concDrain_spuele`/`concDrain_wf`, diagnosed via
  `trace_state`, since removed).
