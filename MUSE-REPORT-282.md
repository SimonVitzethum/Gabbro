# MUSE-REPORT-282: Integer families beyond the pilot (X86/Ganzzahl.lean)

## What was done

New file `grammatik/Grammatik/X86/Ganzzahl.lean` (~500 lines) plus one additive
umbrella import (`import Grammatik.X86.Ganzzahl` at the end of
`grammatik/Grammatik.lean`). Nothing else touched: no canonical
Typen/Wort/Speicher edits, no Befehl change, no Rust, no numbers, no MARKE.

## Exact new definitions

- Logic: `andB`, `orB`, `notB` (width-truncated over `trunc`), `and64`, `or64`
  (64-bit result with flags; CF/OF cleared, AF `none`).
- Multiply: `mulLow` (modular low half), `mulHighU` (unsigned high half via
  `toNat`), `sVal` (two's-complement signed value), `mulHighS` (signed high
  half via `ediv` by `2^b.bits`, wrapped with `emod`).
- Division: `TeilFehler` (`durchNull`, `quotientUeberlauf`), `divU` (refuses
  only divisor zero), `sMin`, `divS` (refuses divisor zero AND `sMin / -1`).
- Shifts: `schiebeZaehler` (`% 64` at b64, `% 32` below), `shlB`, `shrB`,
  `sarB` (arithmetic via `sVal`/`ediv`).
- Flags: `LogikGueltig`, `mulTrag`, `MulGueltig`, `SchiebeNachweis`,
  `SchiebeGueltig` — undefined flags are pinned by nothing; MUL snapshots pin
  only CF/OF/AF(`none`), shift snapshots pin OF only for a one-bit count.
- Ranges: `passtU`, `passtS` — unbounded source sums meet modular words only
  through an explicit fit check.
- Witness memory: `sondenSpeicherNach`.

## Exact new theorems (all proved, no sorry/admit/axiom/native_decide/unsafe)

- Logic: `andB_b64`, `orB_b64`, `notB_b64`, `and64_cf/of/af`, `or64_cf/of/af`,
  `and64_gueltig`, `or64_gueltig`.
- Multiply: `mulLow_b64`, `mulHighU_null_links`, `mulLow_null_links`,
  `mulTrag_heisst`, `mul_gueltig_existenz`, `mul_unbestimmt_unbeschraenkt`
  (two valid MUL snapshots differ in SF — undefined is unconstrained).
- Division: `divU_verweigert_bei_null`, `divU_antwortet_bei_nichtnull`,
  `divS_verweigert_bei_null`, `divS_verweigert_min_durch_neg1`.
- Shifts: `schiebeZaehler_b64_schranke`, `schiebeZaehler_schmal_schranke`,
  `shlB_b64_null`, `shrB_b64_null`, `schiebeZaehler_periode_b64`,
  `shlB_b64_breite_ist_null`, `schiebe_gueltig_existenz`.
- Ranges: `passtU_heisst`, `passtS_heisst`.
- Boundary probes (`decide`): `probe_logik`, `probe_logik_flags`,
  `probe_mul_hoch_u` (max*max high = max-1, low = 1), `probe_mul_hoch_s`
  (-1*-1 high = 0 vs unsigned 0xFE), `probe_div_s_ueberlauf` (INT_MIN/-1),
  `probe_div_antwort`, `probe_schiebung` (counts 0/64/33/63),
  `probe_sar`, `probe_erweiterung`, `probe_bereich`.
- Memory probe: `ganzzahl_speicher_sonde` — `shlB .b64 1 3` stored via
  `write64`, read back via `read64`, byte observably changed (reuses
  `zeugenSpeicher`/`writeBytesN_hit`/`read64_nach_write64`).

## Checks

- `./lean-probe grammatik/Grammatik/X86/Ganzzahl.lean`: 0 errors. All
  `#print axioms` report `[propext, Quot.sound]` (or `[propext]` alone).
- `./lean-bau`: `exit 0; 0 error line(s)`, `Build completed successfully
  (369 jobs)` (was 368; +1 is this file).
- `grep sorry|admit|axiom|native_decide|unsafe`: only `#print axioms` lines.

## Cuts / open (also in the file's CUTS block)

No encodings (lane 279), no source correspondence (277), no cost, no TSO/GX
bridge (274/284), no hardware verification of mask/fault/carry rules, narrow
shifts use one uniform `% 32` mask. No INHABITATION-style `_zeuge` needed:
no theorem quantifies over program syntax and the task names no ZEUGE target;
the memory probe is the executable memory witness.

## Task remarks believed wrong

None blocking. One judgement call: narrow shifts got a uniform `% 32` mask
(hardware-accurate split would be per-form); flagged in CUTS for the encoding
review rather than modelled per-form here.
