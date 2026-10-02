# MUSE-REPORT-693: Exact review of author 692 (observable defined/undefined RFLAGS)

CANDIDATE: 692 4cc9d67fc12ed2e7f85c9e283f385ebb09eba1e5
VERDICT: ACCEPT

## Scope reviewed

Exact pinned snapshot from `.tmp/review/author-692/` (PATCH touches only
`MUSE-REPORT-692.md`, `grammatik/Grammatik.lean` additive import,
`grammatik/Grammatik/X86/ArchitecturalFlags.lean` ~1537 lines, 71 theorems).
No source, Spec, checker, emitter, or friend-path edits. No live-control or
build-tree changes made by this reviewer; verification is static inspection
of the pinned file/PATCH plus local reference-manual greps and canonical
producer reads in this clone. No network, no other clones, no keys.

## Checks performed

- Prohibited constructs: `sorry` 0, `native_decide` 0, `unsafe` 0, new
  `axiom` 0 in the pinned module. The 9 `admit` greps are all the English
  word "admitted" in comments/theorem docs. No `intro _` / `have _ :=`
  premise discards. `Prop`-typed binders found are only `... : Prop :=`
  relation definitions, not premises of type `Prop` itself.
- Build evidence: snapshot `BUILD-EVIDENCE.json` (58 entries) ends with
  `./lean-probe ... == 0 error(s)` and `./lean-bau ... Built Grammatik`
  (report: 467 jobs). Intermediate red probes during construction are
  visible in the log and all resolve to green; one transient
  `sorryAx` in an intermediate probe is gone in the final 0-error probes.
  Axiom prints cited are within `[propext, Classical.choice, Quot.sound]`.
- Provenance: local Intel SDM 325462-093US Sep 2026
  (`.tmp/HARDWARE-REFERENCES/`, REFERENCES.json verified entry, AMD
  absent as declared). Re-checked: ADD "set according to the result"
  (19 hits incl. the cited sentence), PUSHFQ VM/RF-clear text and
  `RFLAGS AND 00000000_00FCFFFFH` operation, "Flags Affected: None",
  POPFQ Table 1-12 (Vol. 2B 4-407/4-408) with the exact S/N/0/X rows, RF
  always-zero note, EFLAGS init bit 1. Author headings/pages match the
  local text.
- Canonical reuse: `add64`/`sub64`/`negWf`/`NegGueltig`, `LogikGueltig`,
  `mulTragU`/`mulTragS`/`MulGueltigU/S`, `SchiebeGueltig`/`SchiebeNachweis`/
  `schiebeZaehler`, `bedingung_stabil`, `bedingung_af_frei`,
  `write64`/`read64`/`lesbar8`/`regSet`/`ripNach`, `geholt`,
  `Codec.decode`. No second adder/interpreter: AF-width lemmas rewrite to
  canonical `afAdd`/`afSub` via `trunc_nibble`; effect relations admit
  exactly the accepted snapshots plus free undefined bits.
- Soundness of undefinedness: ADD/SUB/NEG fully defined; logic AF free
  with two-choice witness (`logik_af_frei`, 0-result, AF false vs true);
  MUL/IMUL only CF/OF pinned with two-choice SF witness
  (`mulU_sf_frei`); DIV all-free with two disagreeing status words;
  shift AF free and OF free off one-count (`schieb_of_frei`) with the
  one-count evidence kept load-bearing (`hc`, `hnone1`). Producer
  abstractions (`mulFlagsU` SF/ZF/PF preservation, DIV whole-snapshot
  preservation) are exhibited as single admissible members
  (`mulU_hat_roh`, `mulS_hat_roh`), not trusted as truth. No invented
  zero/preservation, no "never observable" premise; the AF
  non-observability used for the logic admission is the derived
  `rohAf_frei` lifting the accepted `bedingung_af_frei`.
- Byte forms: PUSHFQ/POPFQ one-byte adapters with pinned length 1,
  mutual cross-refusal, two-byte refusal, and proved pilot-decoder
  non-shadowing (`pushfq_fremd`, `popfq_fremd` by `decide`). PUSHFQ word
  = `r AND 0x00FCFFFF` with proved status-preservation below bit 16 and
  VM/RF clearing; stack is a real 8-byte `write64` with access/flags/RIP
  frames, readback, `archOK` preservation, v8086/IOPL refusal, dead-stack
  and foreign-byte refusals. POPFQ restores via case masks checked
  against Table 1-12 64-bit rows (LadenA/B/C bit sets verified above:
  status always loads; IF loads iff CPL=0 or CPL<=IOPL; IOPL loads only
  at CPL 0; RF/VM/VIF/VIP never load; RF cleared by master equation),
  with RF-cleared, VM-preserved, IF-gating (high/low), status-from-image,
  CPL/VM control, v8086/read/foreign refusals, and concrete stack
  witnesses. The v8086 refusal (`vm && iopl<3`) over-refuses the
  VME/16-bit exception path; that path is declared open in CUTS, so the
  refusal is conservative, not unsound, for the claimed 64-bit form.
- Joint witness: `pushfq_lauf_zeuge` runs canonical `add rax,rbx` on
  0x0F+0x01 (rax=0x10), proves `addErlaubt`, fetches `[0x9C]` from real
  code memory (`geholt`), saves the VM/RF-cleared image to real stack
  memory (changed from zero, `pushfqWort != 0`, rsp moved, RF cleared,
  AF set), plus two legal MUL undefined choices. AF distinguisher
  (0x0F+0x01 vs 0x10+0x01), push/pop roundtrip (status recovered, RF
  cleared, rsp restored), IF-gating witness, and dead/unreadable-stack
  refusals are concrete and non-degenerate (real memory change, defined
  AF observed, two undefined choices).
- Premise use: major premises are used (`hn` selects the read flag in
  `logikVerbrauch_sicher`/`mulVerbrauch_sicher`/`shiftVerbrauch_eins`;
  `hc` pins shift OF; `hval`/`hcf`/`hzf`/`hsf`/`hpf`/`hof` all rewrite in
  `schiebAdapter`; `hv`/`hdec`/`hwr`/`hrd` all consumed in step
  equations). No desired-correctness premise found; DIV/shift gaps are
  refusals, not assumed unusedness.

## Bounds of this ACCEPT (not new claims)

- FP/FPU rows, INC/DEC, ADC/SBB, CMPXCHG/XADD, BT, SAHF/LAHF: open.
- POPFQ 16-bit form, VME/PVI rows, task-switch/real-address rows: open.
- Pending-interrupt delivery (only the IF bit is modelled), TSO: open.
- No wiring into `decodeExt`/`schritt`/`lauf`; adapters are the declared
  boundary for HardwareExecution660/HardwareInterrupts672.
- The ADD leg of the joint witness is a canonical `schritt`, not
  byte-fetched ADD bytes; the byte-fetched leg is PUSHFQ via `geholt`.
  Sufficient for the "at least fetched PUSHFQ" bar; full fetched-ADD
  coverage belongs to the integer-form lanes.
- Minor follow-up (not verdict-blocking): `verbrauchOK` admits OF/CF
  conditions for `.mulS`, but the proved consumer theorem covers
  `.mulU` only; the symmetric `.mulS` safety lemma is missing. Same
  shape, same proof technique; recommend the owner/660 lane add it
  rather than reopening this candidate. Likewise no POPFQ `archOK`
  preservation theorem is stated (construction makes it hold: flags are
  re-read from the restored word), a one-lemma follow-up.

## Result

CANDIDATE: 692 4cc9d67fc12ed2e7f85c9e283f385ebb09eba1e5
VERDICT: ACCEPT (bounded as above; no silent guarantee weakening, no
invented determinism, provenance exact, CUTS honest subject to the noted
minor overstatement on mulS pairs)
