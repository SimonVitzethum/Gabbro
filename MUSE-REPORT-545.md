# MUSE-REPORT-545: N11 PayloadResidue

Lane 545, organisation plan N11 (`dokumente/x86/NEXT-PROOF-WAVE.md` row N11:
`X86/PayloadResidue.lean`, consumer C6 AtomicPayload + QUELLBRUECKE, DEP C6).
Branch `muse/545`, clone `/home/simon/Dokumente/gabbro-muse/a545` (verified at start).

## What was done

New owned file `grammatik/Grammatik/X86/PayloadResidue.lean` (273 lines) plus one
additive import line in `grammatik/Grammatik.lean`. The residue half of QUELLBRUECKE
section 3.3: a generic plain-payload observation/footprint obligation for guarded
transfer over actual source execution. No language construct added, no atomic-rely
duty relaxed, no release/acquire bridge assumed beyond the accepted theorem.

New definitions (witness scaffolding over the accepted payload declaration `pD`
of lane 350: `konfig` atomic publishes plain `zaehler`):

- `qI0`, `qDarf`, `qGd`, `qRumpfH` (`tabA[0] = zaehler`), `qP : Programm pD`
  (one payload reader, everything else idle)
- `q_mem` (payload in footprint, by `decide`), `q_schreibt` (table written, by
  `decide`), `q_fuss` (`FussSX` cover with every carrier local)
- three `DecidableEq` instances for `pD.Fn/Glob/Tab` (TC cannot see through the
  declaration projection; same pattern as needed for any `pD` use)

New theorems (all generic over every declaration/program):

1. `payload_fuss_braucht_deckung` -- a payload carrier in a footprint covered by
   `FussSX` over the admitted atomics `GeteiltV` is thread-local or guard-locked.
   Proof kills the shared-atomic disjunct via `nutzlast_braucht_restbeweis`.
   Every premise used. Axioms: `[propext]`.
2. `nutzlast_ohne_deckung_verweigert` -- a non-atomic payload is refused by
   `atomarFussB` and never admitted, via `nichtatomar_verweigert`.
   Axioms: `[propext]`.
3. `flagge_ist_kein_schloss` -- the admitted flag `konfig` is shared (`GeteiltA`)
   and guardless: a shared atomic flag is not a lock. Axioms: `[propext,
   Quot.sound]`.
4. `bewachte_uebergabe_ohne_rueckstand` -- guarded release/acquire transfer of a
   payload through its atomic flag leaves no observable residue (reader view at
   least writer view; every later payload read at or above it). Thin wrapper over
   the accepted `hb_uebergabe` (Speichermodell/Atomar.lean); the payload premises
   (`atomar a`, publication, plain payload) discharge exactly the side inequality
   `x != c`, nothing else is assumed. `omit [DecidableEq D.Fn]` for the
   linter-clean build. Axioms: `[propext, Classical.choice, Quot.sound]`.

Joint witnesses (each with a written table and the reached memory-changing run
`atomar_nichtleer.2` on `nP`: `konfig` 0 -> 3):

- `payload_fuss_braucht_deckung_zeuge` (all five premises jointly on `qP`/`pD`)
- `nutzlast_ohne_deckung_verweigert_zeuge` (negative case: unguarded plain
  payload refused, no residue proof)
- `flagge_ist_kein_schloss_zeuge`
- `bewachte_uebergabe_ohne_rueckstand_zeuge` (scoped: the flag/payload separation
  jointly, the part the transfer adds over `hb_uebergabe`; see open point 2)

## Build evidence

- `./lean-probe grammatik/Grammatik/X86/PayloadResidue.lean`: 0 errors.
- `./lean-bau`: exit 0, "Build completed successfully (416 jobs)", whole project
  green including the new umbrella import.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `intro _`, no unused
  premise (linter clean). `#print axioms` for all four mains: standard subsets
  only (see above; full `gabbro_ziel` triple only where inherited from
  `hb_uebergabe`).

## What remains open (also the file's CUTS block)

1. No per-access x86-TSO refinement: the transfer is over source W steps, never
   target bytes. TSO bridge owns it.
2. No fresh acquire read exhibited on a payload program: no in-tree run has one
   (the stale-read run `w_nicht_sc` exhibits exactly the complementary unfresh
   case); the transfer witness scopes the step premises to the accepted
   `hb_uebergabe` instead of faking them. A bridge lane that builds a fresh
   release/acquire pair (e.g. via `schrittW_bau`) can complete this leg.
3. No duty construction for payload-bearing units (`nutzerA_aus_quelle` is
   atomic-free only); this file audits the cover, it does not build duties.
4. No IR/validator/lowering/optimisation content; no checker/emitter/friend-file
   edits (untouched: source Spec/checker/emitter, OptimizationRules/Witnesses).

## Task assessment

Nothing in the task was wrong. One scoping note: the "joint positive witness
must write real memory" is met as a written table (`q_schreibt`, by `decide`) on
the payload program plus the reached run with actual memory change
(`atomar_nichtleer.2`: `konfig` 0 -> 3) on `nP`, whose tables and functions the
witness shares. A reached run over the payload program itself does not exist
in-tree (runs need oracle/execution infrastructure over a new declaration);
building one is bridge work, not this row. No NEEDS LEAN obstruction was needed:
the required source transfer exists (`hb_uebergabe`) and is reused, not
reinvented -- no toy handoff semantics was introduced.
