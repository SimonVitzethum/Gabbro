# MUSE-REPORT-603: Whole-word grouping under actual trace exclusion

Lane 603, branch `muse/603`, clone `/home/simon/Dokumente/gabbro-muse/a603`.
Owned files: `grammatik/Grammatik/X86/WordAccessGrouping.lean` (new, ~950 lines),
`grammatik/Grammatik.lean` (one added import line), this report.

## What was done

Connected actual per-byte TSO traces (`TSO`), canonical word `read64`/`write64`
(`Speicher`), the LOCK-profile vocabulary (`WordAtomicity`), realised footprints
(`AccessExecution`) and shared TSO witnesses (`TSOHistory`) for one useful
whole-word observation grouping, in `Grammatik/X86/WordAccessGrouping.lean`.

**Vocabulary (no new executor, no new transition):**
- `wortEintraege a v`: the eight canonical byte-store entries of word `v` at
  `a`, oldest-first (`wortByte v k` at `addrOff a k`).
- `FremdFrei s c a`: no other core holds a pending buffer entry inside `Fuss a`
  — inspects real buffer accesses at one state.
- `WortGruppe s c a v`: start-state check — acting core carries exactly the
  eight canonical entries plus `FremdFrei`. Deliberately alignment-free.
- `DrainSchritt c` (own flush / foreign flush / foreign issue) and `DrainSpur`
  (trace with visited states): the exclusion check is stated over the REAL
  intermediate states, never over a desired end state alone.

**Main results (all premises used by their proofs):**
- `wort_gruppe_liest_zurueck` (§3, generic read-back): an exclusion-checked
  drain from the exact group installs the whole word unsplit
  (`read64 sN.mem a = some v`). Proved by induction carrying the installed
  prefix (`drain_installiert_aux`); foreign flushes use `FremdFrei` from the
  trace, foreign issues are memory-silent, own shape is pinned by the step
  equations.
- `wort_gruppe_rahmen` (§4, generic frame): a disjoint word observation
  survives the drain, via `drain_fuss_bleibt_aux`.
- `realisiert_store_gruppe_treu` + `gruppe_fuss_form` (§5, AccessExecution
  link): a realised `store64` step installs exactly the group bytes in
  post-state memory, and group entry addresses are the realised `Fuss` list.
- `ausrichtung_reicht_nicht` + `riss_unter_verweigerter_gruppe` (§6, tearing
  refusal): address zero is aligned yet core 0's real two-entry buffer
  (`hS2`) is refused by the check, and it tears on flush (first byte new,
  second stale, memory changed) — alignment alone is insufficient.
- `drain_spur_erreichbar` + `drain_schritt_ist_tso` (§7): every drain trace
  is a reached `TSOErreichbar` run.
- `gruppe_verweigert_lock` (WordAtomicity link): grouped states admit no
  LOCK step on the acting core (buffer full) — byte drains and LOCK updates
  never coincide.
- `GruppeNachW` empty (`keine_gruppe_nach_w`): no source bridge claimed.
- Joint witnesses with reached memory-changing runs: full concrete eight-drain
  `grpS2..grpS10` (each flush `rfl`, foreign-free chained, `TSOErreichbar`),
  `wort_gruppe_liest_zurueck_zeuge` (read-back + byte 0 changed 0 → 0x08),
  `wort_gruppe_rahmen_zeuge` (distant word still 0, grouped bytes changed).

**Checks:** `./lean-probe .../WordAccessGrouping.lean` → `0 error(s)`, exit 0.
`#print axioms` throughout: only `propext` / `propext + Quot.sound` (subset of
the standard goal set; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in
the file). Full `./lean-bau` result line:
`== exit 0; 0 error line(s) in the COMPLETE output`.

## Findings during the work (all resolved, recorded honestly)

1. The first frame attempt ("bytes outside `Fuss a` are preserved") is FALSE:
   a foreign flush outside footprint `a` is a real step and may hit the framed
   word. Fixed honestly: the frame theorem takes the exclusion check at the
   framed footprint too (`FremdFrei x c b`). No guarantee weakened — the
   premise was added, the conclusion unchanged.
2. `by_contra` is not available as a tactic in this toolchain (probe error
   "unknown tactic"); used `omega`-disjunctions instead.
3. `if x = addrOff (0 : Adresse) k then ...` fails to PARSE in witness defs
   (parser stops after the bare constant, expects `then`); parenthesized
   conditions plus a hoisted `grpA` address def parse and keep `rfl`-defeq
   with `flushKern`'s output.
4. `decide` cannot synthesize `Decidable (OhneUmbruch _)` (typeclass search
   does not unfold the plain def); `unfold OhneUmbruch` first.
5. `DrainSpur.schritt` keeps explicit state binders, so the trace
   construction needs underscores (`.schritt _ _ _ _ ...`).

## Producer/consumer interfaces

- Produces for BridgeWrite/BridgeRead (or the typed-carrier W bridge owner):
  `wort_gruppe_liest_zurueck`, `wort_gruppe_rahmen`,
  `realisiert_store_gruppe_treu`, `gruppe_fuss_form`, `WortGruppe`,
  `FremdFrei`, `DrainSpur`, both `_zeuge` witnesses.
- Consumes (unchanged, only applied): `TSO` issue/flush/frame lemmas,
  `Speicher` read/write-back/frame facts, `LockedOps` refusal lemmas,
  `AccessExecution.realisiert_store64_gefunden`,
  `Ausfuehrung.schritt_store64_erfolg`, `TSOHistory` tearing witnesses.

## Useful next independent tasks (exact ownership, not started)

- N1 (new lane, own new file): lift the pure own-flush witness drain to a
  drain with interleaved foreign issues (still exclusion-checked) — needs no
  change to accepted lemmas here.
- N2 (bridge owner 573/574): consume `wort_gruppe_liest_zurueck` for the
  per-access W store/read bridge; the `GruppeNachW` gap names exactly what is
  open (typed-carrier histories, `GeteiltV`/`HavocA` environments).
- N3 (validator owner): admit only `WortGruppe`-checked drains plus
  `ausgerichtet8` for lowering consumers; cite `gruppe_verweigert_lock` for
  LOCK-path disjointness.

## Open / not claimed

See the `CUTS:` block in the file: no multi-byte hardware atomicity (eight
visible intermediate states), no source/checker/contract/ABI/loader/cost
claims, no fairness/progress/timing, no LOCK source refinement. Nothing in
the task statement is believed wrong; the task's demand that the exclusion
predicate inspect real trace accesses is met by `FremdFrei`-over-`DrainSpur`.

Co-Authored-By: muse-agent-603 <muse-agent-603@noreply.invalid>
