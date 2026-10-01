# MUSE-REPORT-349: ValidatorSkeleton (WORK-ALLOCATION C5)

## What was done

New file `grammatik/Grammatik/X86/ValidatorSkeleton.lean` (~300 lines) plus one
additive import at the end of `grammatik/Grammatik.lean`. Decided syntactic
validator skeleton over the actual accepted vocabulary, nothing else touched.

`valX86 p bild := wohlgeformt p bild && bildDeckung bild`: the checked image
predicate (`Bild.wohlgeformt`: `groesseOk`/`dateiOk`/`virtuellOk`, alignment,
W^X, disjointness, entry containment, class-checked `relokOk`, mode) AND full
decode coverage of every executable section through the canonical decoder
(`validAllFuel (dateiLen + 1)` over `abschnittBytes`, reusing lane 431's
`decodeFuel`; data sections carry arbitrary bytes and are not decoded).
Untrusted backend output is re-read as bytes and re-validated; no Rust print
is a premise (`hinweisOk` re-decides hints, never assumed).
Full half `valX86Voll` adds the C1/C2 outputs (`valTore` over `torOkB`,
`valLayout` over `layoutOk`) plus extern-site bookkeeping (`externOk`:
every `extern fn` site needs its proved template flag, the declaration
alone admits nothing) and the pointer mirror (`valZeigerOk` over
`m140VerweigertB`).
Fetch tie: `valZeuge_fetch_ret` proves the byte step's `fetchDekodiert`
over actual executable memory sees exactly the validated `ret` on the
canonically loaded witness state (no caller-supplied `Decodiert` trusted).
Extension interface: `ErwDec`/`decodeErw` consults the extension ONLY where
canonical `decode` refuses, with `decodeErw_kanonisch` (no existing form
shadowed, none re-evaluated; the 14 pilot `Befehl` forms were counted).
`valX86_sound` is stated as OPEN obligation in CUTS only, never as a
premise of any delivered theorem.

## Exact names

Definitions: `ValFehler`, `abschnittBytes`, `abschnittDeckung`,
`bildDeckung`, `valX86`, `valZeugeCode`, `valZeuge`, `valFalscheStelle`,
`valWx`, `valTore`, `valLayout`, `valX86Voll`, `ExternStelle`, `externOk`,
`valZeigerOk`, `valBssNeg`, `transferOk`, `ErwDec`, `decodeErw`,
`valZeugeZustand`.
Theorems: `valX86_wohlgeformt`, `valX86_deckung`, `valZeuge_akzeptiert`,
`valZeuge_mutiert_verweigert`, `valZeuge_mutiert_mapping_bleibt`,
`valFalscheStelle_verweigert`, `valWx_verweigert`, `valX86Voll_bild`,
`valAbi_falsch_verweigert`, `valVoll_abi_verweigert`, `valFremd_verweigert`,
`valZeiger_geschmiedet_verweigert`, `valBssNeg_verweigert`,
`valTransfer_unlisted_verweigert`, `valZeuge_gelenk`,
`decodeErw_kanonisch`, `valZeuge_fetch_ret`.
Refusals cover all seven sec. 15 shapes: altered byte, bad site
(site past section end with in-code value), wrong ABI (`torAusClobber`,
N064), unchecked foreign body, forged pointer (M140), BSS mismatch
(`dateiLen > memLen` with decode coverage intact), unlisted mapping
(hole address; code base passes). Joint witness `valZeuge_gelenk` ties
acceptance + mutation refusal to the reused real memory-changing run
`Bild.schreibLese_zeuge`. No theorem quantifies over source syntax, so no
`_zeuge` companion is owed by HARD RULES 13; the joint witness covers the
task's witness direction instead.

## Verification

- `./lean-probe grammatik/Grammatik/X86/ValidatorSkeleton.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
  Axioms: 13 theorems `[propext]`, 2 with `[propext, Quot.sound]`
  (`valZeiger_geschmiedet_verweigert`, `valZeuge_gelenk` via BitVec
  `Quot.sound`), 2 with no axioms — all within the standard goal set.
- `./lean-bau`: `Build completed successfully (417 jobs).`, exit 0.
- Goal probe `#print axioms ...gabbro_ziel`:
  `[propext, Classical.choice, Quot.sound]` — unchanged.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise used;
  no Prop-typed premise; English only.

## What remains open (see CUTS)

`valX86_sound` (waits on IR+TSO+decoder coupling; lane-287 IR pending, no
substitute invented); source correspondence; TSO/GX bridge, concurrency,
contracts, budget, cost/time; silicon/FP/flags beyond decoded refusal;
loader-observed BSS, data-in-code ranges, patched-site re-decode,
control-flow legality beyond containment, callee-side template proofs.

## Task remarks

Nothing in the task is believed wrong. Name checks against source, all
confirmed present as used: `groesseOk`/`dateiOk`/`virtuellOk`/`relokOk`/
`wohlgeformt`/`abteilFinden`/`geladen`/`schreibLese_zeuge` (`Bild`),
`decode`/`encode`/`natByte` (`Codec`), `fetchDekodiert` (`Byteschritt`),
`torOkB`/`torAusClobber`/`schreibTor`/`m140VerweigertB` (`GateStub`),
`layoutOk` (`TableLayout`), `decodeFuel`/`validAllFuel` (`ValidationBudget`).
The "existing 14 forms" count matches the 14 `Befehl` constructors.
Safety corrections were honoured literally: refusal Bool as admission only
(stated in `valWx_verweigert` doc), gate/OS contracts as user logic
(`ExternStelle` docs), no hardware/latency/cost claims anywhere.
