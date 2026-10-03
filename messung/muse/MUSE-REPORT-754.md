# MUSE-REPORT-754: Hardware completion — zero idiom XOR reg, reg

Lane 754, clone `/home/simon/Dokumente/gabbro-muse/a754`, branch `muse/754`.
Owned files only: `grammatik/Grammatik/X86/ZeroIdiomXor.lean` (new),
`grammatik/Grammatik.lean` (+1 import line), this report.

## What was done

Covered the 31/r zero idiom ONLY (`XOR r, r`, REX.W + opcode 31,
register-direct ModRM with equal fields) with a flag-liveness proof at
the site. All value/flag/decode/step facts reuse the accepted canonical
operations; nothing is redefined:

- Codec: `encodeZero` routes to pilot `encode (.xorReg64 r r)`;
  `decodeZero` is the pilot `decode` filtered to XOR-self
  (`ZeroDecodiert`: register + consumed length as checked data).
- Execution: `zeroSchritt` IS the accepted pilot `schritt` on the
  XOR-self row (no second implementation); value/flags reuse
  `Wort.xor64` and `Ganzzahl.LogikGueltig`.
- Liveness: `FlagBedarf` (CF/PF/ZF/SF/OF demand, AF absent by
  construction since the idiom leaves AF undefined), `darfNullen`,
  `Lebendig`, site replacement `ersetzeDurchNull` (idiom where no flag
  is live, `none` where any flag survives).
- Target `ZeroIdiomXor_verbindung`: pilot bytes, zero value, clobbered
  flags with `LogikGueltig`, untouched memory, RIP past the 3 bytes,
  live-demand refusal — with companion `ZeroIdiomXor_verbindung_zeuge`
  (canonical bytes, zero step 42→0, ZF-live refusal, reached
  three-step run storing 7: data byte 0→7, permissions kept).
- Dispatcher link: `zeroSchritt_laufAlt`, `zeroSchritt_stepExt` — the
  idiom runs through the accepted `ExtendedExecution.stepExt` pilot
  arm (XMM/FP untouched, `kern` carries the zero successor).
- Pins/refusals: `pin_zero_rax` ([72,49,192]), `pin_zero_rax_dekode`,
  general `decodeZero_verweigert_fremd` (distinct-register XOR) and
  `decodeZero_verweigert_nicht_xor` (every non-XOR pilot form),
  `pin_nachbarn_verweigert`, `sonde_zero_abgeschnitten`.

Exact new definitions/theorems (all in `Gabbro.Grammatik.X86`,
`ZeroIdiomXor.lean` §§1–8): `ZeroForm`, `encodeZero`, `ZeroDecodiert`,
`decodeZero`, `encodeZero_laenge`, `zeroLaenge_ok`, `roundtripZero`,
`roundtripZero_len_ok`, `decodeZero_verweigert_fremd`,
`decodeZero_ist_pilot`, `zeroSchritt`, `zeroSchritt_ist_schritt`,
`xor_selbst_null`, `xor_selbst_flags`, `xor_selbst_gueltig`,
`zeroSchritt_ok`, `zeroSchritt_wert`, `zeroSchritt_flags`,
`zeroSchritt_speicher`, `zeroSchritt_rip`, `zeroSchritt_fremd`,
`FlagBedarf`, `darfNullen`, `Lebendig`, `ersetzeDurchNull`,
`darfNullen_heisst`, `ersetze_verweigert_bei_lebendig`,
`ersetze_erlaubt_bei_tot`, `zeroZeugeReg`, `zeroZeugeStart`,
`zeroBedarfLebendig`, `progZero`, `pin_zero_rax`,
`pin_zero_rax_dekode`, `decodeZero_verweigert_nicht_xor`,
`pin_nachbarn_verweigert`, `sonde_zero_abgeschnitten`,
`zeroSchritt_laufAlt`, `zeroSchritt_stepExt`,
`ZeroIdiomXor_verbindung`, `ZeroIdiomXor_verbindung_zeuge`.

## Build status

- `./lean-probe grammatik/Grammatik/X86/ZeroIdiomXor.lean`:
  `== 0 error(s)`, all `#print axioms` within
  `[propext, Classical.choice, Quot.sound]` (several depend on none).
- `./lean-bau`: `Build completed successfully (483 jobs).`
  (Two transient infrastructure failures preceded it, both retried
  clean: one `failed to create thread` exit 134 on the final
  aggregation step, one stale `.olean` read right after; neither was a
  proof error. No source/checker/Spec/goal/emitter files touched, so
  `gabbro_ziel` is unaffected — `git status` shows only the two owned
  Lean files.)
- No new diagnostic/gift/example/CLI numbers, no MARKE changes, no
  friend-reserved optimiser files touched.

## What remains open (see CUTS in the file)

No hardware correspondence (stated Intel SDM rows only, per
`.tmp/HARDWARE-REFERENCES/REFERENCES.json`: combined volumes 1-4,
325462-093US; exact heading-level line groundings not re-verified
here); no 32/8/16-bit or memory-operand XOR, no `SUB r, r`; no
program-wide liveness analysis and no optimiser claim (demand is site
data); no TSO/GX bridge (register-only step, no store-buffer effect by
construction); no cost/time/source/checker/Spec/goal claim.

## Task remarks

Nothing in the task statement is wrong. Two notes: (1) the inhabitation
rule's "table that some function writes" is source-level language; the
X86 analogue applied here is the store-changing reached run in the
companion, following the ShiftCodec witness pattern. (2) `./lean-probe`
and the final `./lean-bau` aggregation step hit the known
thread-creation/virtual-address ceiling twice under load; both passed
on retry with no proof change — apparatus, not content.
