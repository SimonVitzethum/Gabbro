# MUSE-REPORT-648: Generic checked source-assignment byte certificate

## What was done

New file `grammatik/Grammatik/X86/GenericSourceByteCert.lean`
(+ one import line in `grammatik/Grammatik.lean`), built in small
checked increments through `./lean-probe`, full `./lean-bau` green.

A NEW generic finite-data certificate/check for the admitted actual
typed `assignSlot` fragment, parameterised over declaration, table,
field, source expression, environment and data layout:

- `GenByteCert`: pure finite data (profile, image, bias, entry,
  layout extent, redundant base-register number, admitted range,
  expected value number, redundant expected value byte). No
  proof-valued field, no assumed simulation, no trusted Rust print.
- `genCertReg` / `genCertStart`: the register file and loaded start
  state recomputed in Lean from the certificate data.
- `genCertOk`: honest Bool (representation admission, profile scope
  pin `.p48`, strengthened entry admission, fetched-decode shape,
  base/layout consistency, value/byte consistency, cell readability,
  observed target byte).
- `genCert_sound`: generic over ANY `D t f i e` — from the accepted
  Bool and the actual source step, the covered `assignSlot` and the
  decoded loaded step agree (representation at joint post-states,
  target read-back and parse, mapping/entry legs, realised footprint
  exactly the slot). The value link is finite identity
  (`hvCert : v.n = c.vval`); `RepSlot`, read-back and footprint are
  DERIVED via `rep_schritt_bleibt` and the fetched-step
  decomposition, never premises. All premises used.
- Two acceptances through the SAME checker: `genCertA` (range
  `0..100`, value 42, reuses the accepted `SourceMemory` witness
  fragment) and `genCertB` (range `10..60`, value 17, fresh
  declaration `witDB` with its own recomputed source execution).
- Six planted refusals by decision: mutated opcode, mutated entry
  (data-section start), mutated layout base, mutated source-value
  number, mutated profile (`.p57`), mutated map (writable code).
- `genCert_sound_zeuge`: joint non-degenerate witness — both
  certificates accepted, writer contracts on both declarations,
  reached source steps `0→42` / `10→17`, reached loaded steps with
  target bytes `0→42` / `→17`, representation at both joint
  post-states, all six refusals.

## Exact exported producer/consumer interfaces

- Producer (later lowering/loader): establish `genCertOk c = true`
  (finite checks) plus the source step `hExec` with
  `hvCert : v.n = c.vval`.
- Consumer (validator/TSO bridge): `RepSlot`, `read64` read-back,
  `wortZahl` parse, `wohlgeformt`/`eintragEnthalten` legs, exact
  realised footprint `Fuss (slotAddr ...)`.
- The redundant pairs (`rbase` vs `basis+off`, `vval` vs `vbyte`)
  are what make layout/value mutations checker refusals instead of
  silent agreements.

## Last build result

`./lean-bau`: `Build completed successfully (458 jobs).`
`#print axioms`: `genCert_sound` and `genCert_sound_zeuge` on exactly
`propext, Classical.choice, Quot.sound`; decide-facts on a subset.
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

## What remains open (see CUTS)

Single `.int` slot / single `assignSlot` / single decoded store
only; no multi-step control flow, relocation re-decode, TSO/GX
bridge, hardware, OS/loader, optimiser/loader closure, or
`valX86_sound`. Values above 255 need a wider observation than the
single lowest byte checked here.

## Next useful independent task

Lift the observation leg from one lowest byte to a proved 8-byte
word read-back inside the checker (width-generic `CodeFremdN`-style
byte window), keeping certificates finite-data-only.

## Task fidelity note

The lane-632 fixed witness (`SourceValidatorConnection`) is
untouched and never a premise of the generic claim; its `witD`
family is reused only as witness-A instantiation data (witnesses are
off the trust path by rule). No other agent was started, no files
outside the clone were read, no push was made.
