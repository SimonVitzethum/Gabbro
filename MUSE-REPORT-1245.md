# MUSE-REPORT-1245: x86 address to source carrier mapping for the TSO-to-W bridges

## Task

Follow-up of lane 1213 (`TsoRmwLink.lean`): the TSO-to-W links hold over the
GENERIC history shape because no accepted x86-address to carrier mapping
existed. Define the mapping from the pipeline placement layout
(`PipelineImage.lean`: `Platz`, `layoutVon`, `TabLayout`) to the source
carriers (`t`,`k`,`f`) used by the W history, prove it injective on admitted
placements and that distinct carriers have disjoint 8-byte footprints, and
specialise one existing bridge theorem (read or write) to it, with a witness
on a placed table that a function writes. Report as a FINDING any bridge that
needs more.

Note on the lane file: the CONTEXT/MECHANISM boilerplate (§11-style
`HwAdapter`/`HwSchritt` family-connection text) does not match this TASK
paragraph. The TASK paragraph is specific and self-contained (mapping +
injectivity + one bridge specialisation + witness), so it was executed as
written; no `HwAdapter` was built and no existing file was changed except the
one `import` line the task orders. No new silicon claim was needed either
(the mapping reuses accepted definitions only).

## What was done

NEW FILE `grammatik/Grammatik/X86/TsoAddressCarrier.lean` (429 lines) plus
one appended line `import Grammatik.X86.TsoAddressCarrier` in
`grammatik/Grammatik.lean`. Nothing else touched.

New definitions/theorems (all in `Gabbro.Grammatik.X86`):

- `kartiert ps a t k f : Prop` — THE MAPPING: `(layoutVon ps).loc t k f =
  some a`. Reuses `PipelineImage.layoutVon` unchanged.
- `kartiert_sep` — two placed slots are the same slot or have disjoint
  8-byte `Disjunkt` footprints. From decided `sepB` via `sepB_sound`
  (`LayoutSep`), Nat-interval disjointness lifted with
  `disjunkt_von_intervallen` + `natAdresse_ohneUmbruch` under explicit
  no-wrap bounds. Axioms: propext, Quot.sound.
- `kartiert_injektiv` — one placed address names one slot (same address
  on both sides; the footprint alternative is impossible since a
  footprint meets itself). Axioms: propext, Quot.sound.
- `platzOk_rep` — a member placement naming `(t,k,f)` discharges `repOk
  (D.typ t f) p.a 8 0` plus `lesbar8`/`schreibbar8` at `natAdresse p.a`,
  from decided `platzOkB` (`List.all_eq_true`) with the key rewritten
  through `trifft_inv` (all three key components via `subst`).
- `zugelassen_schranke` — a mapped address satisfies `a + 8 ≤ 2^64`,
  via `layoutVon_loc` + `repOk_int` over `platzOk_rep`. Feeds the
  no-wrap premises of `kartiert_sep` from the checks, never assumed.
- `kartiert_von_erst` — the first placement naming a slot IS the mapping
  (plus it indeed names the slot, derived from the `find?` equation).
- `schrittW_aus_gruppen_drain_platziert` — specialisation of the
  accepted no-read WRITE bridge to `natAdresse p.a`, discharging its
  `repOk` premise from `platzOkB` via `platzOk_rep`. Axioms: propext,
  Classical.choice, Quot.sound (inherited from the accepted bridge).
- Refusals: `leer_ohne_kartierung` (empty placement maps nothing),
  `platz_ueberlapp_verweigert` (placements at 4096 and 4100 refused by
  decided `sepB`, on two distinct rows of `witD`).
- Witness placement `psWit := [⟨(), 0, (), 4096⟩]` on `witD` with
  `psWit_sep`, `psWit_platz`, `psWit_trifft`, `psWit_mem`, `psWit_loc`
  (all `decide`) and `witA_ist_platziert : witA = natAdresse 4096`
  (`rfl`).
- `schrittW_aus_gruppen_drain_platziert_zeuge` — joint witness: `witD`
  (one table, witness function writes it: `ctHw`), reached one-step run
  `0 → 42` with observably changed target bytes at placed address 4096,
  decided admission + layout facts, and the specialised bridge
  conclusion (`SchrittW`, value agreement, `RepSlot` at the placed
  address). Non-degenerate per rule 13 (written table + memory-changing
  source step and target drain).

## Verification

- `./lean-probe grammatik/Grammatik/X86/TsoAddressCarrier.lean`: 0 errors.
- `./lean-bau`: exit 0, 0 error lines, 642 jobs, whole project green.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every theorem
  premise is used by its proof (checked by construction; the `&&`-chain
  split uses the left-nested `⟨⟨hre, hles⟩, hschr⟩` pattern).
- `#print axioms` for every main theorem: at most propext,
  Classical.choice, Quot.sound — the `gabbro_ziel` standard set.

## FINDING: bridges that need more (as the task requests)

1. Committed-read bridge (`TsoReadBridge.schrittW_aus_lesefragment_gruppe`)
   and forwarded-read bridge
   (`schrittW_aus_lesefragment_weiterleitung`) are NOT specialised to
   placed addresses. Each needs its own `repOk`-from-`platzOkB` discharge
   (same `platzOk_rep` applies) plus its read-side premises
   (`ladeWort8` linkage, `sichtVon` projection bounds) restated at
   `natAdresse p.a`. Mechanical, no new idea required.
2. Run induction (`TsoRunInduction.brueckenLauf_erreichbar`) consumes
   `BrueckenSchritt` values, not addresses; placing it needs placed
   specialisations of all three per-step bridges first (finding 1 closes
   the read two-thirds). No change to the induction itself is expected.
3. `TsoRmwLink`'s timestamp/value link stays over generic history
   addresses (`Adresse`/`Wort`), not placed carriers; lifting it needs
   the placed-address form of the LOCK event footprints, which is a
   separate lane (LOCK steps are outside the fragment bridges).
4. Globals (`D.Glob`) have no address form here: `kartiert` covers table
   slots `(t,k,f)` only. A global placement layout does not exist in the
   accepted tree.

## What remains open (not claimed)

Full per-access target-to-W/GX simulation; hardware correspondence beyond
self-consistency; no source/checker/contract/budget/duty/goal change.

## Believed-wrong check

Nothing in the task paragraph appears wrong. The generic HwAdapter
mechanism text in the lane file does not apply to this task (see top
note); following it would have built the wrong deliverable.
