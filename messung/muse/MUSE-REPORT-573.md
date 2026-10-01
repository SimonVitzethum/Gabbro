# MUSE-REPORT-573: Projected TSO stores to source W writes

Lane 573, branch `muse/573`, clone `/home/simon/Dokumente/gabbro-muse/a573`.
OWN ONLY: `grammatik/Grammatik/X86/BridgeWrite.lean` (new),
`grammatik/Grammatik.lean` (one additive import line),
`MUSE-REPORT-573.md` (this file).

## What was done

New module `Grammatik.X86.BridgeWrite` (323 lines) consuming the ACCEPTED
`TSOHistory` (`histVon`/`sichtVon`/fresh-message/FIFO facts) and
`SourceMemory` (`RepSlot`/`rep_schritt_bleibt`) interfaces over the
canonical `TSO`/`Speicher`/`WordAtomicity` vocabulary. No fork of
TSO/IR/source semantics, no source/checker/Spec/goal/emitter change,
no friend-file edit. New definitions/theorems (all in
`Gabbro.Grammatik.X86`):

- `issue_beobachtet_bleibt`: issued (buffered) byte store changes no
  `read64` word observation (stutter; visibility needs a flush).
- `issue_rep_bleibt`: issued store preserves `RepSlot` of every
  admitted carrier.
- `flush_nur_ein_byte`: one `flushKern` changes at most one canonical
  address (two distinct changed addresses are contradictory) — the
  word guard is necessary, a single flush is never a carrier write.
- `riss_im_fuss`: tearing addresses `sbX`/`sbY` sit inside one word
  footprint (`Fuss 0`).
- `riss_gemischt_verweigert`: after the first flush the word at `0`
  holds mixed halves (new byte 0, stale byte 1) — tearing refusal.
- `bruecke_schritt_rep` (positive bridge): one real source
  table-write step (`execStmt` over `Stmt.assignSlot`) plus the
  matching guarded `write64` under a checked `WortGuard` (all four
  guard facts re-concluded) yields `RepSlot` plus the
  `wortZahl` parse-back roundtrip. Derived via `rep_schritt_bleibt`;
  no simulation premise taken. Every premise used.
- `bruecke_fifo_stutter`: two same-core issues from empty plus one
  flush — older value committed and history-readable
  (`fifo_hist_konsistent`), younger byte still pre-flush (stutter);
  W admits any fresh-timestamp order so TSO FIFO is the safe direction.
- `bruecke_fremd_kein_wort`: foreign-drain refusal — fence-ready core
  0 coexists with core 1 forwarding `7` past the committed word `0`.
- `bruecke_schritt_rep_zeuge`: joint witness for the bridge (witD
  one-table/write-function plus TSO guard state over the same `witM`,
  source slot `0 → 42`, target bytes changed).
- `bruecke_zeuge_gelenk`: joint two-core reached memory-changing
  witness (TSO `sbStart → sbNach2 → sbGespült` plus admitted slot
  write with changed word).
- `BrueckenProfil` (= `repOk`) plus `brueckenProfil_zeuge`
  (witness slot admitted, `bool` refused).

Axioms: every theorem depends only on `propext`, `Classical.choice`,
`Quot.sound` (the goal-axiom set); several on `propext` alone or none.
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `Prop`-typed
premise, no dropped premise.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (441 jobs)`. Goal axioms untouched
(this lane adds no goal-level theorem).

## What remains open (labelled blocked, not closure)

Full per-access `SchrittW` (`wahl`/`neu`) assembly is OPEN and
documented in the module CUTS: a W write installs ONE message with
the whole post-step carrier value while a TSO flush installs one
byte; the byte-`Lesbar`/`Frisch` facts do not transfer to
carrier-granular `Frisch`. Needs the per-rule access-list
decomposition (O-access, ~70 `RufSchrittG` rules) and the drain-to-
`write64` packet lemma, owned by the follow-up bridge (consumer:
BridgeRead574 for the load side). `valX86_sound` and the
source-to-final-bytes closing theorem stay OPEN.

## Task remarks

Nothing in the task was wrong. One scoping note: the task asks for
"the real source W write relation" — this lane ties the target word
install to the real source slot-write transition (`execStmt` via
`rep_schritt_bleibt`, which is what `SchrittW` wraps per access);
the `SchrittW`-witness packaging itself is the stated OPEN leg, not
claimed here. A per-byte `Sicht` lemma alone is indeed insufficient
for the full-carrier claim, as the task warns — the carrier claim
comes only through `RepSlot` + `WortGuard` + roundtrip.

## Producer/consumer interface and next integration

Producer (this lane): `RepSlot`-at-word + guard + FIFO/tearing/
foreign facts listed above. Consumer BridgeRead574 takes the load
side against the same `histVon`/`sichtVon`/`RepSlot` vocabulary;
validator soundness consumes `bruecke_schritt_rep` +
`bruecke_fifo_stutter` with the refusals as validator rejections.
Measurable next step: packet-drain lemma (8 ordered flushes of one
word packet = one `write64` effect) feeding a `SchrittW`-witness
constructor once O-access lands.

## Verification

- `./lean-probe grammatik/Grammatik/X86/BridgeWrite.lean`: 0 errors.
- `./lean-bau`: exit 0, 0 errors, 441 jobs, green.
- No Rust touched: no `./cargo-pruef` owed. No credentials read,
  no network, no push, no other clones touched.
