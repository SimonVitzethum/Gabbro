# MUSE-REPORT-1223: valX86_sound for the decidable part

Clone `/home/simon/Dokumente/gabbro-muse/a1223`, branch `muse/1223` (verified at start).
Owned files only: `grammatik/Grammatik/X86/ValidatorSoundPart.lean` (new),
`grammatik/Grammatik.lean` (one appended import line),
this report. No other file touched.

## What was done

Proved soundness for exactly the part that `valX86` decides (checked
image mapping AND whole-section decode coverage from each section
base), reusing the accepted definitions unchanged
(`ValidatorSkeleton`, `ValidationBudget`, `Bild`, `LoadedExecution`,
`Byteschritt`, `HwLoadedImage`, `ValidatorExecution`). No model was
copied or redefined; no existing theorem was deleted or weakened.

New theorems in `Grammatik.X86.ValidatorSoundPart` (21 total):

- `valSound_mapping`, `valSound_deckung`: admission implies the
  checked mapping / whole-image coverage (reuse `valX86_wohlgeformt`,
  `valX86_deckung`).
- `valSound_abschnitt`: every member section is covered (through the
  same `List.all` the definition uses).
- `valSound_exec_vollex`, `valSound_exec_traversierung`,
  `validAllFuel_gibt_traversierung`: every executable member section
  fully decodes from its base with no remainder (no stray bytes from
  the base; interior offsets are a pinned gap, see below).
- `valSound_wx`, `valSound_groesse`, `valSound_datei`: W^X, size and
  file-containment mapping inversions.
- `valSound_lade_datei`: inside the file-backed part the loaded byte
  IS the mapped file byte, and the mapped index lies inside the file
  (equality reuses `geladenByte_datei`; the bound discharges
  file containment, so all premises are used).
- `valSound_lade_bss`: BSS tail reads defined zero.
- `valSound_ausserhalb`: outside every section, byte zero and no
  read/write/execute permission.
- `valSound_perm_exec`, `valSound_wx_kein_schreiben`: loaded execute
  permission is the section flag; executable sections are not writable.
- `valSound_hw_fetch_gleich`, `valSound_hw_schritt_gleich`: under
  explicit memory coincidence plus core agreement, the core projection
  fetches/steps exactly what the loaded image does (reuse the accepted
  `HwLoadedImage` identities; coincidence is a premise, never derived
  from the validator Bool).
- `valSound_stark_gibt_deckung`: the strengthened entry check yields
  the fetched covered pilot form at exact length with executable
  prefix (packages accepted `valStark_gibt_deckung`; this is the half
  plain `valX86` does NOT supply).
- `valSound_mutiert_verweigert`, `valSound_wx_verweigert`: planted
  decode and permission refusals (Bool admission, never fault claims).
- `valSound_kein_innen_eintritt`: pinned limit -- skeleton admits the
  interior entry, containment admits it, actual fetch refuses.
- `valSound_zeuge`: joint witness -- admitted minimal image, its
  mutation refusal, admitted store image with a real memory-changing
  loaded step (42 into the data section, zero before), a
  `schreibLese_zeuge` write/read, and the refused interior entry.

This is explicitly NOT source refinement; `valX86_sound_full`
(source correspondence/refinement) is listed as OPEN in CUTS, with
the no-hardware, no-concurrency, no-cost/time scope limits.

## Check results

- `./lean-probe grammatik/Grammatik/X86/ValidatorSoundPart.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`. Every theorem
  depends only on standard axioms (`propext`, plus `Quot.sound`
  where listed); no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- Last `./lean-bau` result line: `Build completed successfully
  (640 jobs).` with `== exit 0; 0 error line(s) in the COMPLETE
  output`. Whole `grammatik/` stays green.

Commits on `muse/1223` (via `arbeitsprotokoll/.commitmsg` +
`./commit.sh`, all with the lane attribution line): `ac843166`
(skeleton + first legs), `834b6517`, `98fdd1b7`, `bd1d55c4`
(all remaining legs, pins, witness, final CUTS). Note: the last two
commit messages both read "mapping inversions, loaded-byte legs and
Hw identities" although the final commit also contains the stark leg,
the refusal/limit pins, the joint witness and the final CUTS -- the
message file was not refreshed before that commit. Content is
complete and green; the message wording is stale, not the proof.

## What remains open

Everything in the file's CUTS block: `valX86_sound_full`, source
correspondence, silicon/hardware correspondence, multi-step
control-flow, relocation re-decode, TSO/GX bridge, contracts,
cost/time, termination. Nothing of that is claimed here.

## What I believe is wrong in the task

1. The MECHANISM paragraph (§27 of the lane file) does not describe
   this lane: it asks for a family event type, a `HwAdapter`, `HwWf`
   preservation, and a multi-core non-degenerate witness with TSO
   forwarding. That is a hardware-family-connection task; lines
   23-24 define THIS lane as validator soundness. I followed the
   specific task and did not invent an adapter or event type --
   inventing one would duplicate an accepted model (rule 16). The
   coherent-machine connection is present as the fetch/step
   identities under explicit coincidence.
2. "Every reachable executable byte decodes" as written would be
   false: coverage starts at section bases, and the in-tree
   `innenBild` counterexample admits an interior entry whose fetch
   refuses. I proved the true statement (whole-section decode from
   the base) and pinned the gap as a theorem
   (`valSound_kein_innen_eintritt`) instead of claiming the stronger
   one. This is not weaker by choice; the stronger claim is refuted
   in the tree.
3. Rule 13 required no `_zeuge` companion here: no premise quantifies
   over `Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args`, and the
   task names no `ZEUGE:` target. The joint `valSound_zeuge` (with a
   real memory-changing step) is provided anyway.

## Repair diagnosis after the failed integration gate (2026-10-05)

The integration gate failed while building
`Grammatik.X86.ValidatorSoundPart` as job 640/642 in the main
checkout (`-j2 -M4096`):

- `libc++abi: terminating due to uncaught exception of type
  lean::exception: failed to create thread`, Lean exit 134.
- This is the documented apparatus failure (AGENTS.md section 9: the
  virtual-address/thread ceiling causes exactly `failed to create
  thread` even on unchanged source), NOT a defect in this module:
  - the file contains zero `decide` calls; every proof is cheap
    term-mode reuse (`exact` of accepted theorems), `omega`, `simp`,
    `rfl`, or a `generalize`/`cases` inversion;
  - it builds green standalone (`./lean-probe`: 0 errors, all 21
    theorems, standard axioms only) and inside the full local build
    (`./lean-bau`: exit 0, 640 jobs), re-verified after the gate
    failure on the unchanged content;
  - the crash hit this module only because it was next in the build
    queue; any module could have crashed instead.
- Repair action taken: NONE in the Lean sources -- manufacturing a
  change (let alone weakening a theorem) to "fix" a resource crash
  would violate the safety rules. The module is unchanged and green.
- Concrete blocker for the coordinator: the integration environment
  needs resources (or a retry when the machine is quiet) -- thread
  creation failed under `-j2 -M4096` with many concurrent agents and
  builds on the machine. A fresh independent review of the changed
  commit and a fresh integration run are still required; nothing was
  merged. No push, no network (HARD RULES).
