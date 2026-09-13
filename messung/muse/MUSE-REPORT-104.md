# MUSE-REPORT-104 — lane 104 (D4: chain from a machine run, N threads)

Second revision (reviewer feedback addressed). First revision used
full-rights premises `hVollT`/`hVollG`; the reviewer rejected them
(rightly: false for ordinary programs such as `refP`'s `lies`) and
asked for `progAus` + typing-derived frames, an unchanged conclusion,
a two-function witness, and a separate lemma falsifying `hVollT`.
All five are done below.

## What was done

`grammatik/Grammatik/KetteVoll.lean` (namespace
`Gabbro.Grammatik.KetteVoll`, imported at the end of
`grammatik/Grammatik.lean`) proves the D4 target: from any `PCReach`
run **over the extracted program** whose steps fire their threads' own
contracts, a joint chain with the same worlds and step threads, for
any number of threads and any interleaving.

How each `GemeinsamerLauf` field is discharged (no premise quantifies
over `Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args`):

- `hKette`: `spurLaenge` — one world per rebuilt spur step.
- `hSchritt`: per step. Old positions ride the prefix chain
  (`kette_schritt_rahmen2`). New leaf positions close by the fired
  step's frame (`blatt_rahmen_vertrag` via `hO`) widened through the
  honesty identity `hV : V = vertragVon D (code g)` plus the signature
  coincidence (`vertragVon_schreibt`/`_gschreibt`, both `rfl`) —
  this is where typing does the wiring — then transported through
  memory equalities (`KetteVorSpeicher`, `speicher_welt_speicher`).
  Lock positions close by unchanged memory.
- `hPaar`/`hBeschraenkt`/`hGesittet`: the chain's recorded run stays
  empty (`J.l = []`, the target only asks for worlds and step
  threads), with the permissive pair set `ketteNb`.
- `hEintritt`: entry worlds built to fit (`eintrittOf`).
- `hSchuld`: premise-free for every function by U003
  (`schuldnerHaelt_gilt`).
- `hInvSicht`: follows from entry (`sicht_aus_eintritt`).

The induction runs over `EhrlichAbleitung` (honest derivations indexed
by the `PCReach` derivation they track): lock steps as in `PCSchritt`,
and every fired leaf carries its thread's own contract. The `PCSpur`
for the conclusion is rebuilt alongside from the same data.

## Exact names of new definitions/theorems

- defs: `ketteNb`, `spurFuer`, `eintrittOf`, `writerSig2`,
  `readerSig2`, `D2`, `idx2`, `wahr2`, `writeLeaf2`, `rumpfSchreibt2`,
  `liesSlot2`, `rumpfLiest2`, `P2`, `O2`, `sp2`, `code2`, `prog2X`,
  `sigma2'`, `neu2`, `cs2`, `M2`, `pc2`
- theorems: `offen_spurFuer`, `mem_offen_spurFuer`,
  `eintrittOf_passt`, `sicht_aus_eintritt`, `gesittet_nil`,
  `beschraenkt_nil`, `spurLaenge`, `letzteSpeicher`,
  `vertragVon_schreibt`, `vertragVon_gschreibt`, `blattRahmenEhrlich`,
  `KetteVorSpeicher`, `kette_schritt_rahmen2`, `kette_aus_ehrlich`,
  `kette_aus_lauf_voll`
- inductive: `EhrlichAbleitung` (`leer`, `schrittNehmen`,
  `schrittGeben`, `schrittBlatt`)
- witness/result theorems: `writeLeaf2_blatt`, `O2_gut`, `hstep2`,
  `hneu2`, `hkn2`, `hLambda2`, `hpc2`, `hax2`, `hEreignis2`, `hmark2`,
  `hcar2`, `hs2`, `h2B`, `hV2`, `hHon2B`, `slotTrue2`, `neSchreibt2`,
  `kette_aus_lauf_voll_zeuge`, `hVollT_falsch2`

## Last `./lean-bau` result

`== 0 error line(s) in the COMPLETE output`, build completes.
`./lean-probe` on the file: 0 errors, no warnings for the file.
`#print axioms` for `kette_aus_lauf_voll`,
`kette_aus_lauf_voll_zeuge`, `hVollT_falsch2`:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no extra
axiom. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no
`intro _`, no `have _ :=` in the file (`by decide` appears only inside
`.weiter` index-bound proofs copied from `D1.i0`). Every premise is
used (audited per theorem; `hO` feeds the leaf frame, `hHonest` the
induction, `h` scopes it).

## What remains open

- The built chain has `J.l = []`, not `J.l = M.lauf`. A chain tracking
  the recorded run as well would additionally owe `PCMarkSep` /
  `PCUnsharedSep`.
- Honesty (`EhrlichAbleitung`) is a per-run firing discipline, not
  derived from `progAus` alone — see "wrong" §2. Narrowing it (e.g. to
  scheduler-checkable atom identity S12) is downstream work.
- No diagnostic codes, probe numbers, or example numbers were added
  (the task assigns none).

## Things in the task / review I believe are wrong or incomplete

1. **Name collision (unchanged).** `MaschinenKette.lean:322` already
   owns `Gabbro.Grammatik.kette_aus_lauf_voll`; mine lives in
   namespace `KetteVoll`. No existing file was touched.
2. **Typing alone does not imply the frame — honesty is load-bearing.**
   `progAus` + the `PCSchritt` checks (`hpc`/`hΛa`/`hmark`/`hcar`) do
   not pin a fired leaf's contract: a leaf with another contract and
   the same footprint (same `Λ`, carriers covering the atom's) fires
   just as well, and a writing one breaks the frame outside its
   rights. Hence the frame cannot "follow from typing" without a
   firing discipline; `EhrlichAbleitung` (fired `V = vertragVon D
   (code g)` per step, scoped to the run's own derivation, no
   syntax-quantified premise) is the minimal closure of the
   reviewer's sketch. What typing does contribute, and what the proof
   uses: an honest firing's contract IS its function's, whose writes
   ARE the signature's (`vertragVon_schreibt`, both `rfl`) — and the
   fired statement's own `hw` premises are what make honest firings
   respect exactly those rights. The frame itself is derived from the
   fired step, never posited.
3. **`refP` cannot serve as the witness program (measured, not
   assumed).** Its signatures hold the lock, so no `progAus` leaf can
   fire from `GenStart` (`HeldGenau [held] []` is false), and no
   `locks` statement can open at its holdings (rank `0 < 0` fails for
   the only lock). `D2` keeps the demanded writer/reader split — one
   table, `true` writes it, `false` only reads and returns it — with
   empty holdings instead; thread 1 fires the writing leaf straight
   from `GenStart`, thread 0 maps to the reader. `hVollT_falsch2`
   shows the old premise false exactly there (the reader writes
   nothing).
4. **Witness (rule 13).** `kette_aus_lauf_voll_zeuge` fixes all
   program inputs (`P2`, `O2`, `0`, `sp2`, `code2`, `[()]`, `[]`,
   `M2`, `pc2`, `h2B`, honesty `⟨[1], hHon2B⟩`) and proves every
   premise jointly, plus non-degeneracy: the writer writes the table
   (`⟨(), rfl⟩`) and the one-step run moves memory (`neSchreibt2`:
   slot `false → true`).

## Lean formatting lesson (for other lanes, kept from v1)

A multi-line `by` block *inside* a record literal breaks parsing
(`unexpected identifier; expected '}'` at the block's end), while the
same tactic sequence at top level is fine. `KetteVoll.lean` keeps
record fields single-line (long frame proofs live in preceding
`have`s / helper theorems). Term continuations must also outdent past
the opening bracket's column.
