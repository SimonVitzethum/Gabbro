# MUSE-REPORT-318: Independent review of candidate 317

## Scope and method

Reviewed ONLY the pinned snapshot in `.tmp/review/author-317/` against
`SNAPSHOT.json` (author 317, HEAD
`9e97546f46f9ec5706148c1e0da3b988b1125023`, base
`a81a64a2fb5571a2a2df82c214c56e755efafb41`, files
`MUSE-REPORT-317.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/Zugriffe.lean`, clean) and its
`BUILD-EVIDENCE.json` tool log. Read the full 687-line snapshot file,
the owner task (`OWNER-TASK.md`), and the report (`MUSE-REPORT-317.md`).
Checked the candidate's claims against the canonical modules in this
clone (`Typen.lean`, `Speicher.lean`, `Ausfuehrung.lean`). Ran
`./lean-probe` on the snapshot file itself (absolute path, no copy into
`grammatik/`, no central-file edits). No other clone read, no code
edits, no Rust work.

## Independent build check (this clone)

`./lean-probe .tmp/review/author-317/grammatik/Grammatik/X86/Zugriffe.lean`
prints as its first line `== 0 error(s) in the COMPLETE output`. The
`#print axioms` output matches the report exactly: every listed theorem
depends on `[propext, Quot.sound]`; `kein_atomarer_zugriff` and
`keine_ablauf_spur` depend on no axioms. No `sorry`, `admit`, `axiom`,
`native_decide`, or `unsafe` tokens in the file (case-sensitive whole-word
grep; the only substring hits are prose words such as "admitted"). No
premise typed as `Prop` itself; no `intro _` / `have _ :=` discards; every
premise of every theorem is used by its proof (spot-checked all groups).
`PATCH.diff` confirms the only central change is one additive umbrella
import in `grammatik/Grammatik.lean`; no source, Spec, goal, Typen, or
Rust edits.

## Cross-checks that hold (verified, no finding)

- 14-constructor coverage: `Typen.lean` defines exactly 14 `Befehl`
  constructors; `zugriff` matches all 14 generically, reusing `effAddr`,
  `Fuss`, `ripNach`, and fixed `Register.rsp` stack addresses. No new ISA,
  no alternate evaluator, no fetch footprint, no source-specific rule.
- Read/write distinctions match `schritt`: pure/control forms expose
  nothing; `load`/`pop`/`ret` read-only; `store`/`push`/`call` write-only.
- Stored words: `store` = source register, `push` = source register read
  before the move (matches `schritt`'s `let v` before `oben`, including
  the `push rsp` case), `call` = actual next RIP `ripNach s.rip d.laenge`
  (matches `schritt`'s `nach`). Taking `Decodiert` rather than bare
  `Befehl` is required for exactly this reason; the report's note is
  correct.
- `stapelOben` (`rsp - 8`) is syntactically the address `schritt`
  pushes/calls through. Per-constructor equations (all 14 named) are
  definitional unfolds; `fuss_mem` correctly chains `leseEreignisse_acht`
  with `leseEreignisse_mem` (both exist in `Speicher.lean`).
- Pure/read agreement: all cited `schritt_*_speicher` lemmas exist with
  matching signatures; each theorem concludes memory equality AND the
  extracted footprint.
- Read linkage (3): `getD 0 0` of each `Fuss` equals the base address via
  `addrOff_null`; destination/RIP value conclusions reuse the canonical
  `schritt_load64_erfolg` / `schritt_pop64_reg` / `schritt_ret_erfolg`.
  The `dst != rsp` bound on the pop value is inherited from the canonical
  lemma shape and honestly stated.
- Refusals (7) are complete: bad length plus the six memory forms that can
  fail (`load`/`store`/`push`/`pop`/`call`/`ret`); pure/control forms
  cannot refuse, so nothing is missing.
- Witnesses are real and memory-changing: `zugriff_lauf_zeuge` is a reached
  two-step `lauf` run changing byte 8192 from 0 to 42 by `decide`;
  `zugriff_zeuge_im_fuss` puts that byte in the same step's extracted
  footprint. Probes (`8184 = 8192 - 8`, next RIP `4101 = 4096 + 5`,
  pop base `8192`) are consistent with `zeugeZustand` (rip 4096, rsp 8192)
  and all close by `decide` (probe green independently).
- Potential-vs-realised framing is exact: `zugriff` checks no permission or
  length; every agreement theorem is conditioned on a successful `schritt`,
  and every refusal concludes `False` from a success hypothesis. No assumed
  correspondence; TSO visibility, byte order beyond `wortByte`, grouping,
  W/GX simulation, and fetch (lane 319) stay OPEN in CUTS.
- The empty-inductive non-atomicity pair (`AtomarZugriff`,
  `AblaufSpur`) is vacuous by construction, but CUTS says so plainly and
  the substantive content (four length-8 footprint theorems over the shared
  per-byte `Fuss`) is proved. No hardware theorem is smuggled.
- Report label "(11)" for the pure/read group versus 12 listed items is a
  self-corrected typo (parenthetical says 12 counting both jumpIf arms);
  not material.

## Finding (one omission, blocks ACCEPT)

The owner task requires for every pilot constructor: "all changed memory
bytes lie in the extracted write footprint, all permissions preserved".
The three write-agreement theorems conclude only TWO of the three
permission maps:

- `erfolg_store64_im_fuss` (snapshot lines 361-387; conclusion 367-371)
- `erfolg_push64_im_fuss` (lines 392-420; conclusion 398-402)
- `erfolg_call32_im_fuss` (lines 425-453; conclusion 431-435)

each prove `lesbar` and `schreibbar` preservation (projections `.1` and
`.2.1`) but drop `ausfuehrbar`. The cited canonical lemmas conclude all
three maps: `schritt_store64_berechtigungen`,
`schritt_push64_berechtigungen`, `schritt_call32_berechtigungen` (this
clone's `Ausfuehrung.lean`: store ~492, push ~625, call ~690) each end in
`...lesbar... /\ ...schreibbar... /\ ...ausfuehrbar...`, documented as
"keeps every permission". The candidate file contains zero occurrences of
`ausfuehrbar`. Its docstrings ("permissions are preserved") and the report
("permissions preserved") therefore overstate the formal statements, and
the cut is not labelled OPEN anywhere. The theorems as stated are true,
but the mandatory "all permissions" deliverable is 2/3 proved.

## Required changes (mechanical, then re-probe)

1. In `grammatik/Grammatik/X86/Zugriffe.lean`, add the conjunct
   `s'.speicher.ausfuehrbar = s.speicher.ausfuehrbar` to the conclusions of
   `erfolg_store64_im_fuss`, `erfolg_push64_im_fuss`, and
   `erfolg_call32_im_fuss`, each proved by the `.2.2` projection of the
   already-cited `schritt_*_berechtigungen` lemma (same argument lists as
   the existing `.1` / `.2.1` lines).
2. Adjust the three docstrings to name all three preserved maps.
3. Correct `MUSE-REPORT-317.md` accordingly and re-run `./lean-probe`
   (expect `0 error(s)`) plus `./lean-bau` green.

## Last build result

Independent `./lean-probe` on the pinned snapshot file:
`== 0 error(s) in the COMPLETE output` with the axiom lines quoted above.
No full `./lean-bau` run (gratuitous for a review; the author's
`BUILD-EVIDENCE.json` final `./lean-bau` entry shows exit 0, 376 jobs,
consistent with the report).

## Verdict lines

CANDIDATE: 317 9e97546f46f9ec5706148c1e0da3b988b1125023
VERDICT: REPAIR
