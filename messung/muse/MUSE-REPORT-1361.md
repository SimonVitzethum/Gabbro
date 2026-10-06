# MUSE-REPORT-1361 — String instructions with REP prefixes and the direction flag

Lane 1361, clone `/home/simon/Dokumente/gabbro-muse/a1361`, branch `muse/1361`.
Commits: `4d309ba1` (decoder), `2805b728` (semantics), `0d55a8ca` (adapter+chain;
message says "semantics" but the content is adapter+chain — cosmetic skew, noted),
plus the final commit with witness, CUTS, import and this report.

## What was built

New module `grammatik/Grammatik/X86/Befehle/Zeichenketten/StringOps.lean`
(module `Grammatik.X86.Befehle.Zeichenketten.StringOps`), imported once at the
end of `grammatik/Grammatik.lean`. NOTE: the task names the path
`grammatik/Grammatik/X86/StringOps.lean`, but `lean-layout.py --check` rejects
it (`^String\w+$` → `Befehle/Zeichenketten`, mandatory rule); I created it at
the tasked path and ran `--apply` per HARD RULE 18. `instrumente/lean-layout-map.json`
is updated by that tool run (mechanical fallout, committed alongside).

1. **Decoder + encoder.** `strDecode` covers MOVS/STOS/LODS/SCAS/CMPS (A4–AF)
   with F2/F3, 66H and REX prefixes, plus CLD/STD (FC/FD). LOCK (F0) refuses;
   doubled prefixes, 66H/REX on byte opcodes and prefixed CLD/STD refuse.
   REX.W overrides 66H; other REX bits are accepted and ignored (no register
   field exists). Canonical encoder `strEncodeD`/`strEncode` with proved
   round trip `strRoundtrip` over all 60 op/width/prefix shapes, six closed
   decode pins and seven planted refusals.
2. **TSO-sequence semantics.** `strElement` runs per element a load then a
   store through the accepted `loadByte`/`issueByte`; LODS merges via the
   accepted `mergeRegNarrow` (8/16-bit merge, 32-bit zero-extends, 64-bit
   whole); SCAS/CMPS model ZF only. `strWeiter` steps RSI/RDI by ±width from
   DF, RCX only under REP. `strAnzahl` with proved zero-count no-op
   (`strAnzahl_rep_null`, `strLauf_rep_null`). Fuelled loop `strLauf` carries
   a precise fault index; `strLauf_fehler_grenzen` bounds it (induction in the
   tree's `bsfVon` idiom). CLD/STD as `strDirSchritt`.
3. **Extended chain.** `kapDecodeStr` tries the old `kapDecode` first:
   exact agreement (`kapDecodeStr_kap`), string arm only on old refusal
   (`kapDecodeStr_str`), joint refusal (`kapDecodeStr_nichts`), three
   conditional string-row pins and LOCK refusal.
4. **Coherent-machine adapter.** `HwAdapter StrEvent` (`adapterString`); the
   event carries incoming DF (canonical `Flags` has no DF), incoming ZF comes
   from core flags. Proved: `HwWf` preservation, clean-loop agreement
   (`adapterString_fertig`), fault refusal (`adapterString_verweigert_bei_fehler`).
5. **Two-core witness.** Core 0 runs REP STOSB ×3 (bytes 65 at 8192–8194),
   core 1 one STOSB (byte 7 at 8200). `strWit_zeuge` joins: stepped RDI
   (8195/8201), drained RCX, buffer lengths (3/1), owner-only forwarding
   (owner reads 65, foreign reads 0), memory 0→65 in three cells after the
   drain, well-formedness and clean finishes. Non-degenerate: three shared
   bytes change. All computational claims are closed `decide`/`rfl`.

## Finding during the work

The round trip caught a real decoder defect in my own code: the REX.W bit
was read off the byte at the REX position even when that byte is the opcode
itself, refusing valid STOSB/LODSB/SCASB and mis-widthing 16-bit forms.
Fixed (W bit counts only on a real REX byte); all 60 shapes go green.

## Verification

- Last `./lean-probe …/Befehle/Zeichenketten/StringOps.lean`: `== 0 error(s) … exit 0`.
- Last `./lean-bau`: `Build completed successfully (709 jobs)`, exit 0
  (`✔ [708/709] Built Grammatik`).
- `lean-layout.py --check`: all 852 files placed.
- `#print axioms` per main theorem in-file: subsets of
  `[propext, Classical.choice, Quot.sound]` only (`strLauf_fehler_grenzen`
  uses the full trio via `omega`; no `sorry`/`admit`/`axiom`/`native_decide`).
- No Rust touched: `cargo-pruef` not applicable. No text-guardian documents touched.

## Open (see CUTS for the full list)

- `kapDecode` refusal of A4–AF/FC/FD bytes is a hypothesis in the pins, not
  a proved fact. Maintainer extends `kapDecode` in
  `grammatik/Grammatik/X86/Hw/Kapstein/HwKapsteinDecoder.lean`; then the
  hypotheses discharge (expected: by `decide`) and `kapDecodeStr` folds in.
- Only ZF modelled for CMPS/SCAS (CF/SF/OF/PF/AF FREE, named
  over-approximation); no segment/address-size overrides, no I/O string ops.
- Narrowings (refusals stricter than silicon): 66H/REX on byte opcodes,
  doubled or prefixed CLD/STD.
- DF rides in the event; persistence across steps is caller-managed.
- A mid-sequence fault refuses the whole adapter step; precise
  RCX/RSI/RDI-at-fault state lives at loop level (`strLauf`), not in the
  adapter successor.
- No source/W/GX bridge claimed.

## Task feedback

- The family-specific evaluator list (ShiftLogic, MulDiv, ArchitecturalFlags
  flag classes, HwAddressed events) has no string-op content to reuse: no
  shifter/divider use, no ModRM/SIB addressing (implicit RSI/RDI), ZF handled
  directly. Reused instead: NarrowOps (`mergeRegNarrow`), TSO
  (`issueByte`/`loadByte`/`flushKern`), AddressEncoding (`addrOff`).
- The literal file path in the task conflicts with the mandatory layout rule;
  resolved via `--apply` (rule 18). Suggest future family tasks name the
  layout-derived path.
- Line 26 of LANE.md is truncated mid-sentence (fault-state requirement);
  intent was clear from the MECHANISM section.
