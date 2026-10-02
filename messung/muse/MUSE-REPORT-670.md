# MUSE-REPORT-670: Hardware completion — precise selected fault and exception transitions

## What was done

New module `grammatik/Grammatik/X86/HardwareFaults.lean` (~540 lines,
green) plus the additive umbrella import in `grammatik/Grammatik.lean`.
Nothing else touched. The module classifies admitted-profile
architectural faults over the REUSED canonical dispatchers -- no new
machine, decoder row, instruction, interpreter, handler model or source
claim.

Definitions: `ArchFehler` (de/ud/gp/ss/pf/ac/nm/xm, Intel SDM Table 6-1);
`klassifiziereMulDiv`, `klassifiziereExt`, `adapter660_klasse` (660
consumer entry point); `istKanonisch` (48-bit, SDM Vol.1 §3.3.7.1) with
`adrKlasse` (#SS stack vs #GP data); `datenFehlerKlassen` (permitted
`[#SS,#PF]` / `[#GP,#PF]` sets -- the model has no paging, so #GP vs #PF
is explicit nondeterminism) with `leseKlasse`/`schreibKlasse` tied to the
real `read64`/`write64` equations; `FehlerBeobachtung`/`beobachte`
(pre-state RIP + memory as the observation; RAX/RDX carry no claim after
#DE); `einByteSpeicher`/`einByteKern`/`einByteStart` fetch witnesses.

Main theorems: halt_ist_de, ok/misslungen kein Fehler, adapter660
soundness trio, kanonisch pins + adrKlasse gp/ss/kein-Fehler,
lese/schreibFehler_in_klassen + Erfolg_kein_Fehler, div_null/ueberlauf and
idiv_null/min-neg1 _ist_de on REAL execution (incl. through stepExt),
stepExt_verweigert_kein_de, storeVerweigert_erhaelt,
untaken_kein_stiller_erfolg (untaken CMOV-memory fault cannot be made
fault-free -- contradicts the accepted step equation), fehlbyte (no
silent #UD: `decodeExt [0xFF] = none` is refusal only), fetch
abgeschnitten/fehlbyte/ohne_exec _verweigert on actual bytes,
steuerung_vec_ohne_os_verweigert + kein_fehler (would-be #NM stays a
refusal), zugriff_ohne_ac (unaligned 8193 reads/writes, no #AC),
ueberlapp_verweigert_bleibt (reused), dunkel_schreiben_in_klasse, and the
JOINT witness fehler_zeuge_gemeinsam (reached two-cell 42-store run from
zero + #DE divide with preserved fault RIP + truncated-fetch refusal
with no fault + dark-store in-class refusal).

## Checks

- `./lean-probe grammatik/Grammatik/X86/HardwareFaults.lean`: 0 errors.
- `./lean-bau`: Build completed successfully (460 jobs), whole project green.
- Axioms: at most `[propext, Quot.sound]` -- subset of the
  `gabbro_ziel` standard; no sorry/admit/axiom/native_decide/unsafe.
- No premise has type `Prop` itself; every premise is used (no
  `intro _`); no theorem quantifies over source syntax, so rule 13 needs
  no extra `_zeuge` beyond the joint witness (non-degenerate:
  memory-changing reached run + faulting divide/fetch/store).

## Manual provenance checked

`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`:
Table 6-1 vectors (txt lines 9641-9671); §3.3.7.1 Canonical Addressing
(txt line 4220, incl. RSP/RBP -> #SS rule); DIV entry (line 31795),
IDIV entry (line 31887). Recorded in the file header.

## Open / not claimed (see CUTS)

Fault priority between pending classes, #GP-vs-#PF disambiguation
(needs paging), privilege/stack-switch detail and all delivery
(IDT/stack/handler/error code) stay with lane 672 -- untouched.
#UD membership of refused bytes, unmasked #XM, flag-gated #AC,
CR0-gated #NM, TSO/GX bridge, hardware verification against silicon,
and source stop-class transfer stay OPEN. The #DE destinations
(RAX/RDX) are deliberately unclaimed (undefined per the entries).

## Task assessment

Nothing in the task as written appears wrong; the scope boundary
against 672 (no duplicate interrupt model) was respected by keeping
observations at the pre-state with no handler call and no RIP advance.
