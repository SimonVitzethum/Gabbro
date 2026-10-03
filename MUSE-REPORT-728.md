# MUSE-REPORT-728: Actual IDT TSS descriptor and entry stack selection

Lane 728, clone `/home/simon/Dokumente/gabbro-muse/a728`, branch `muse/728`.
Own files only: `grammatik/Grammatik/X86/InterruptDescriptorHardware.lean`
(1187 lines), additive import in `grammatik/Grammatik.lean`, this report.
English throughout. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
no premise of type `Prop` itself; every theorem premise is used
(`lean-probe` reports zero warnings).

## What was built

A generic descriptor-read/check layer on actual canonical memory
(`Speicher`), in long mode, for the 672 (delivery) / 708 (entry)
consumers. No trusted parsed descriptor anywhere: `liefere` starts
from raw gate words and every refusal is a precise `TorFehler`.

- §0 control state: `Steuerstand` (IDTR base/limit, TSS base/limit,
  CPL, IF bit). Generic architectural registers, no OS content.
- §1 gate read: `torAdresse` (base + vector*16), `torImLimit`
  (`vector*16+15 ≤ limit`), `liesTorBytes` (two accepted `read64`
  halves; either unreadable half refuses) with refusal/success
  equations.
- §2 parse: `IdtTor` (offset, selector, IST, DPL, interrupt flag),
  field extractors (`torOffsetNat`/`torOffset`/`torSelektor`/`torIst`/
  `torTyp`/`torDpl`/`torVorhanden`/`torIstReserviertOk`/
  `torHochReserviertOk`), `zerlegeTor` → `TorDetail`
  (`ok`/`falscherTyp`/`reserviertIst`/`reserviertHoch`).
  Interrupt type `0xE`, trap `0xF`; DPL needs no range check.
- §3 checks in INT-entry pseudocode order: `Herkunft`
  (`softwareInt` with INT1 flag / `extern`), `dplZugelassen`
  (software non-INT1 needs `cpl ≤ dpl`; INT1 and external pass),
  `TorFehler` (9 members), `TorErgebnis`, `pruefeTor` +
  `pruefeTorKern` (limit, type/reserved, DPL, present, NULL
  selector, downstream-owned `codeOk`, canonical handler),
  with one forward equation per stage plus `pruefeTor_bereit`.
- §4 TSS/stack: `stapelSlotOffset` (nonzero IST → `ist*8+28`,
  else `neuDpl*8+4`), `slotImLimit` (`off+7 ≤ limit`), `StapelWahl`,
  `waehleStapel` (no TSS read where nothing switches; limit before
  load; refused TSS read is a TSS-access fault). Slot pins
  IST1=36, IST7=84, RSP0=4, RSP3=28.
- §5 faults: `torVektor` (Table 6-1: GP=13, NP=11, TS=10, SS=12),
  `torFehlerCode` with `codeFuerIdt`/`codeFuerSelektor` and the EXT
  bit from `extVonHerkunft` (clear for software, set for external;
  DPL fault hardcodes EXT=0 per pseudocode), `alsArch` bridge to
  `HardwareFaults.ArchFehler` (#NP/#TS have no admitted member --
  proved), `fehlerRang`, and `erste_pruefung_gewinnt_dpl`
  (a DPL fault implies limit+type passed: first failure wins).
- §6 delivery: `schiebeRahmen` (accepted-`write64` chain, 8 bytes
  down per word), `LieferAnfrage` (vector, raw words, source,
  `codeOk`, switch data, current pointer, SS/RSP/RFLAGS/CS/RIP
  words, optional error code), `rahmenWorte` (SS,RSP,RFLAGS,CS,RIP,
  code; length 5/6), `LieferErgebnis`
  (`zugestellt mem rip ifNeu gewechselt` / `lieferFehler f code`),
  `schiebeUndStelle` (canonical-RSP check, then push),
  `liefere` (check → select → push). Ordering facts:
  `liefere_prueft_zuerst`, `liefere_stapel_vor_wirkung`,
  `liefere_rsp_nichtkanonisch`, both `liefere_zugestellt_*`.
- §7-9 witness + probes + interface: byte-populated IDT
  (vector-2 interrupt gate, IST 1, selector 8, handler `0x2000`)
  and TSS (IST1 = `0x4000`) in canonical memory; positive pins
  (`idtWit_liest`, `wit_zerlegt`, `wit_bereit`, `wit_stapel`);
  twelve negative probes (limit, type, absent, both reserveds,
  NULL selector, noncanonical target, DPL contrast incl. INT1
  exemption and external bypass, TSS limit naming slot 36,
  no-switch keep, dark-stack #SS with vector/code projections,
  error-code values 26/19/25); joint `liefer_zeuge_gemeinsam`
  (IST switch, IF cleared, five-word frame read-back, two
  observably changed cells from zero). Consumer list for 672/708
  is written in the §9 header comment.

## Checks

- `./lean-probe`: `== 0 error(s) in the COMPLETE output; exit 0`
  (final file; no warnings).
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`
  (whole `grammatik/` project, 482 targets).
- Axioms: main theorems depend only on `propext` (some helpers
  additionally on `Classical.choice`/`Quot.sound`; nothing else,
  no `sorryAx`). Full `#print axioms` block at file end.
- `git log`: skeleton `88c177e6`, pipeline `81570b11`
  (both via `./commit.sh` with the lane co-author line).

## Open / not claimed (see file CUTS)

GDT/code-row ownership (`codeOk` explicit input); async completion,
nested delivery, #DF escalation, TSO interaction (672/708);
full 20-vector error-code presence table (presence is an explicit
`Option`); the `RSP & ...F0` mask line (loaded pointer is the
output); shadow-stack/CET/FRED/task gates (FRED-off IDT only);
Vol. 3 gate/TSS figures are stated architecture (outside the local
txt snapshot) -- every check is proved from canonical equations.

## Task feedback

The task asks for "precise fault class/error code, priority and
pre-fault effects". Priority is implemented as the pseudocode
check order with the first-failure theorem; a cross-class numeric
rank (`fehlerRang`) exists but has no ordering theorem attached
to delivery beyond `erste_pruefung_gewinnt_dpl` -- if a global
simultaneous-fault ranking (e.g. against in-flight divide/page
faults) is wanted, that is a separate 672-side theorem. The
16-byte layout and TSS figure provenance gap is recorded honestly
in the file header and CUTS rather than worked around.

Co-Authored-By: muse-agent-728 <muse-agent-728@noreply.invalid>
