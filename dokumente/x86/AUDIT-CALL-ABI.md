# Audit: CALL-ABI (lane 410)

*Owner: lane 410. Owns only this file plus `MUSE-REPORT-410.md`.
Status: review evidence, not an implementation. No Lean module, no validator,
no refinement and no image acceptance is proved here. Full source-to-final-byte
validation remains OPEN. Method: read the accepted implementations at the exact
lines cited, checked each theorem against its stated claim and its `CUTS`, and
compared against the frozen consumer contract (`dokumente/x86/IMAGE-ABI.md`,
`DIRECT-COMPILER-DESIGN.md`, `WORK-ALLOCATION.md`). Existing in-tree `decide`
probes are cited as the positive/negative evidence; no new Lean file is added
by this lane. Do not read a helper as claiming its explicitly OPEN bridge.*

## 0. Scope and verdict summary

Audited (accepted, merged):

- `grammatik/Grammatik/X86/Stapel.lean` (lane 309) — frame extents, 16-byte
  call-boundary alignment, slot layout, argument/result carriage.
- `grammatik/Grammatik/X86/AufrufOpt.lean` (lane 310) — ghost call-event
  reconstruction for inlining over the real source model.
- `grammatik/Grammatik/X86/Ausfuehrung.lean` (lane 272) — `call32`/`ret` plus
  `push64`/`pop64` steps over canonical `Speicher`.
- `grammatik/Grammatik/X86/Zugriffe.lean` (lane 317) — per-instruction
  footprint extraction, including call/push/pop/ret rows.
- `grammatik/Grammatik/X86/ControlFlow.lean` (lane 338) — `direktZiel`
  equation and `direktZielOk` admission.
- `grammatik/Grammatik/X86/SpillPrivate.lean` (lane 343) — TSO-side private
  spill producer half.
- Consumers/read-only: `Typen.lean`, `Byteschritt.lean`, `Bild.lean`,
  `Syscall.lean`, `FremdRuf.lean`, `Folge.lean`, `IMAGE-ABI.md` secs. 5–8, 11.

Pending (OPEN, explicitly not foundations — see `WORK-ALLOCATION.md` secs. 1–2):

- C2 `GateStub` (lane 346, candidate pending), C4 `EntryState` (lane 348,
  candidate pending), C1 `TableLayout` (lane 345), C5 `ValidatorSkeleton`
  (lane 349, waiting). Nothing in this audit invents a bug because these are
  OPEN; the gaps in secs. 2–7 name them as the consumer that must close them.

Verdict: each helper is **sound within its stated claim and its CUTS**. No
false theorem or false model semantics was found. What is missing is **four
P0 bridges** (sec. 8) between helpers that no single helper claims: dynamic
`rsp` to static `Rahmen` linkage, `ret`/indirect provenance with caller
liveness, indirect-call ghost coverage, and the x86 stub/entry correspondence
(path is C-target only today). Details below.

## 1. What each module actually claims (so the audit does not over-read it)

| Module | Proved | Explicitly OPEN (not a bug) |
|---|---|---|
| `Stapel` | checked extents (`rahmenOk`, lines 46–48), alignment (`spitze_ausgerichtet`, 70–77), slot save/load round-trips (92–101, 341–349), slot/frame disjointness (156–207), spill/callee-save/stack-arg separation (249–277), System V arg registers (283–315), region save/load (366–517), joint memory-changing witness (557–580) | no decoder/`schritt` (CUTS 616–619), no TSO bridge (620–622), no source correspondence (623–625), callee-save/entry contracts and external ABI byte correspondence OPEN (629–632), no image/loader/cost (633), no Linux mechanism (634–635) |
| `AufrufOpt` | ghost pair shape (32–37, length 40–42), order preservation both channels (57–84), log classification over real `RufSchrittG` (99–113), inline obligation data (127–144), entry-duty derivation (149–174), joint witness on a table-writing program with a reached 5-step run (191–253) | no body-splice simulation (CUTS 256–262), `nachOk` derivation OPEN (263–266), duty discharge OPEN (267–271), indirect calls have no ghost form (272), bounds/budget untouched (273–275), no SCFG/target bridge (276–278) |
| `Ausfuehrung` | per-form step equations; `push rsp` stores the OLD top (102–109); `pop rsp` takes the loaded word (111–119, 321–339); `call32` stores post-decode RIP and jumps to `nach + disp` (121–126, 351–360); `ret` pops target and advances rsp (127–132, 373–379); store-changing witness (787–789); call/return probe (804–806) | no decoder/encoder (CUTS 834–836), no TSO bridge (837–839), no source correspondence (840–841), no ABI/loader/image (842–843), narrow widths absent (844–845) |
| `Zugriffe` | single extraction `zugriff` (42–58); `call32` row stores ACTUAL next RIP (57, 151–156); `push` stores pre-move source (55, 136–140); `pop`/`ret` read OLD top (56, 58); realised-footprint linkage (431–462); explicit refusals never a trace (466–527); no-atomicity/no-trace emptiness (540–551); reached witness (591–597) | POTENTIAL vs REALISED distinction (CUTS 637–639), no atomicity (640–643), no interleaving (644–646), no RMW/LOCK/fence/narrow (647–649), no simulation/source/cost/ABI (650–651), no fetch footprint (652) |
| `ControlFlow` | `direktZiel` from decoded length only (19–22); `direktZielOk` start-or-entry guarantee (179–185); reuse equations for `jump32`/taken-`jumpIf32`/`call32` (189–218); mid-instruction/data/off-image refusals (306–323) plus one accepted target (428–431); no-speculation CMOV-memory fact (117–124) | no new encoding/decoding (CUTS 447–449), no hardware correspondence (450–452), no alignment admission (453–456), 32-bit clearing not modelled (457–458), **no indirect-target certificates** (459–461), no whole-image coverage (462–464), no source/TSO/cost (465–467) |
| `SpillPrivate` | admission Bool with three refusals (36–57) plus positive probe (60); spill = `write64`/`read64` at slot (93–105); freshness base/unfold (117–131); commutation + stable-carry (156–180); reached TSO witness with observably changing foreign byte and untouched spill bytes (327–347) | SCFG-side application WAITS for 287 (CUTS 356–358), no multi-byte atomicity/LOCK/source/cost (358–360), refusal is admission never a fault (361), no second IR (362–364) |

## 2. Stack and private spills

**Correct within claim.** `Stapel` never assumes a correct caller: every save
states its bound (`idx < schlitzZahl`) and permission checks and refuses with
`none` (`sichereWort`, lines 82–84; `sichereWort_ausserhalb`, 104–108;
`sichereWort_verweigert`, 111–117; CUTS 626–628). Separation facts use both
bounds plus the interval order (`schlitz_disjunkt`, 156–177;
`rahmen_getrennt_von_intervallen`, 186–207; `bereich_getrennt`, 237–246).
`SpillPrivate` keeps the same discipline on the TSO side: admission is a
`Bool` (validator admission, never a hardware fault — `spillPrivatOk`, lines
36–37; CUTS 361), spills are ordinary permission-checked accesses
(`spill_speichern_ist_write64`, 93–98), freshness is per-byte disjointness
from buffered bytes (`SpillFrisch`, 24–26), and the commutation lemma consumes
all its premises through `write64_kommutiert` (156–169).

**Real gaps (missing bridges, not false theorems):**

1. **No `rsp` ↔ `Rahmen` linkage.** `Rahmen` is a static `(basis, tiefe)` Nat
   pair (`Stapel`, 17–20) with slot addresses `basis + idx*8` (29–33), while
   `Ausfuehrung` moves a dynamic `rsp` register (`schrittPush/schrittCall`,
   `Ausfuehrung` 42–60) and `Zugriffe.stapelOben` reads `rsp - 8`
   (`Zugriffe`, 37–38). No theorem ties any `rsp` value to any `Rahmen`
   extent, nor a `call32`/`push64` write to a `Belegung` slot. A consumer
   that lowers frames to `rsp`-relative accesses must prove this mapping;
   today `rahmen_getrennt_von_intervallen` (static Nat intervals) and the
   dynamic stack discipline are two unconnected facts. **P0** (bridge owner:
   layout/lowering + validator; needs accepted 287 interface for the SCFG
   side; the TSO-side half exists in `SpillPrivate`).
2. **Callee-save is layout only.** `Belegung.gerettetIdx` (227–229) names
   slot indices and proves they do not overlap spills/args (249–277), but no
   theorem says which registers survive a call, on which paths they are
   saved/restored, or what a missing restore refuses. `Stapel` CUTS states
   this as OPEN (629–632); `IMAGE-ABI` sec. 8 makes it a per-image checked
   convention with the C187 trampoline minimum as the gate-entry shape. Any
   backend relying on more than the declaration states is refused — but the
   refusal predicate for ordinary calls does not exist yet. **P0** (owner:
   validator + per-image convention; GateStub C2 covers the gate-entry shape,
   ordinary-call shape still ownerless).
3. **Red zone, guards, overflow are absent — correctly absent.** No red-zone
   rule, no guard page, no stack-overflow/underflow theorem exists in
   `Stapel`/`Ausfuehrung`/`Zugriffe`. `IMAGE-ABI` sec. 8 requires the choice
   (respect vs disable) recorded per image and checked; sec. 3 requires guard
   pages as fault-by-construction. Since no helper claims them, this is a
   consumer gap, not a helper bug. **P1** (owner: EntryState C4 + image
   contract; needs 287-independent entry predicates first).
4. **`Belegung` is slot arithmetic, not allocation.** `braucht/passt`
   (220–225) and the separation lemmas assume the layout fits; no register
   allocator, liveness, or fuse rule is present (correctly — the file never
   claims one). The fused-16-byte-spill hazard noted in `REVIEW-OPT-BINAER`
   stays with the optimiser/validator, not here. **P2** (owner: optimiser
   certificate + overlap checker `OverlapRefusal`, which already refuses
   cross-carrier shared access).

## 3. Register aliases

**Correct within claim.** `argReg` implements the System V integer order
(`rdi rsi rdx rcx r8 r9`, `Stapel` 283–290) with probes at both ends
(`argReg_sonde_rdi`, 292; `argReg_sonde_r9`, 296), pairwise distinctness
(299–308), and the stack spillover rule (`argReg_ab_sechs`, 312–315; stack
index `argStapelIdx`, 319–320 with bound `argStapel_schranke`, 325–330).
`Codec` register codes match the architectural order (`Codec` 13–22), and
`ControlFlow.setLowByte` correctly preserves upper bits for the 8-bit SETcc
rule (30–47) while CUTS records that 32-bit clearing is NOT modelled
(457–458) — an honest boundary, not a silent inheritance.

**Real gaps:**

1. **`argReg` vs gate clobbers is unchecked.** The 4th integer argument is
   `rcx` (`Stapel`, 287), and the syscall/gate convention destroys `rcx`
   and `r11` (`Syscall.schreibAbi`, `Syscall.lean` 55–59;
   `IMAGE-ABI` secs. 5, 8, 12; `EMITTER-INVENTAR` gate row). No theorem
   relates `argReg` to `SysAbi.ein/aus/clobber`, and `GateData.regs`
   (`FremdRuf`, 41–46) are abstract indices, never platform registers. The
   pending C2 direction (`WORK-ALLOCATION` C2: distinct in-registers,
   out-register unclobbered, clobbers incl. `rcx`/`r11`) is exactly the
   missing check; until it lands, a gate stub that parks a live 4th argument
   in `rcx` across the trap has no Lean refusal. **P0** (owner: GateStub C2;
   do not duplicate `SysAbi.gut` — reuse it).
2. **Two register files with no mapping.** `X86.Register` (`Typen`, 13–16)
   and `SysReg` (`Syscall`, 27–30) name the same 16 registers in different
   types; no function maps one to the other. Any gate-stub proof must bridge
   them without forking a third file. **P1** (owner: GateStub C2).
3. **No `rsp`/`rbp` exclusion theorem.** `argReg` never returns `rsp`/`rbp`/
   `rbx`/callee-saved names, but no lemma states it. Minor; the validator
   will need `argReg i ≠ some rsp ∧ ≠ some rbp` for the frame-safety case.
   **P2** (one-line lemma, owner: whoever proves the `rsp`↔`Rahmen` bridge).
4. **Width aliases at call boundaries are unproved.** Narrow argument/result
   widths (zero/sign extension, upper-32 clearing) have no call-ABI rule;
   `Stapel` moves whole words and `ControlFlow` CUTS defers narrow widths to
   A1. A caller that passes a 32-bit value in `edi` and a callee that reads
   `rdi` needs the extension rule at the boundary. **P1** (owner: narrow
   bridge; `NarrowOps` exists but its call-boundary application is unwritten).

## 4. Faults and costs

**Correct within claim — and the distinction is load-bearing.**
`Ausfuehrung.schritt` returns `none` for bad length or failed permission on
every form (67–132), and `Zugriffe` proves each refusal admits no successful
step (`zugriff_*_versagt_kein_erfolg`, 466–527) with the POTENTIAL vs
REALISED framing stated up front (CUTS 637–639). `SpillPrivate.spillPrivatOk`
is explicitly validator admission, never a hardware fault (CUTS 361), with
all three refusals proved (42–57). `ControlFlow.direktZielOk` is likewise
admission, not a fault (171–185). No helper confuses the three categories
(hardware fault / profile admission refusal / source stop).

**Real gaps:**

1. **No fault-to-source-stop mapping.** A target `none` (bad length, failed
   permission, faulting CMOV-memory read kept on the untaken path —
   `ControlFlow` 117–124) has no proved mapping to any `FortschrittG` stop
   class (`hardware`, `flag`, `budget`, `nieZurueck`). The helpers correctly
   refuse loudly; the chain does not yet say which source stop each refusal
   preserves. Hardware faults and profile admission refusals must stay
   distinct here (a refused image is not a trapped execution). **P1** (owner:
   per-form fault correspondence, wave-B obligation per `IMAGE-ABI` sec. 14).
2. **No cost rule for call/stack forms.** `call32`/`ret`/`push64`/`pop64`
   have no `KostenG`/`Budget` accounting, and gate costs live in
   `GateData.kosten` while constraining no answer (`FremdRuf` header). The
   `CostSummary` schema (C3, lane 347, candidate pending) owns the framework
   with `budget_simulation` stated OPEN; call-site attempt bounds (notably
   unbounded CAS-retry vs constant shape, cf. `LockedOps` policy) must not be
   conflated with source steps. **P1** (owner: C3 + per-site bounds; no
   constant bound for retry shapes).
3. **CMOV-memory fault is proved, its cost/order is not.** The
   no-speculation fact is correctly narrow (fault kept, nothing about timing
   or TSO visibility claimed). Any optimiser motion of a faulting CMOV needs
   the fault-preservation proof plus the TSO footprint (`Zugriffe` load row)
   — neither exists yet. **P2** (owner: optimisation certificate).

## 5. Source call logs and order

**Correct within claim.** `AufrufOpt` works over the REAL source model
(`RufEreignisF`, `rufAt`, `RufSchrittG`, `FolgeLog`/`FolgeG`) with actual
values at every event (file header, lines 5–13). The ghost pair carries
identity, actual `rho`/`v`/`s0`/`s1` (32–37); the splice preserves `FolgeLog`
under computed `Bool` side conditions, both channels (57–84); the step
classification is by case analysis over the real step relation (99–113); the
entry duty is derived from a successful `rufAt` outcome (149–174); and the
joint witness co-occurs on a reached run of a table-writing program
(`geistRekon_zeuge`, 191–253: `setze` writes `konto`, `pruefe` ghost pair
logged, `konto[0]` 0→5, order leg holds). The `Folge` static check it feeds
conservatively clears the armed bit on indirect calls, compounds, locks and
loops (`Folge.lean` 69–81), so the lemmas cannot be misread as covering those.

**Real gaps (all stated in its CUTS — legitimately incomplete, not false):**

1. **No body-splice simulation.** There is no function splicing a callee body
   at a call site and no inlined-steps-against-`rufAt` theorem (CUTS 256–262).
   What exists is the checked ghost reconstruction the certificate must
   re-emit. Any consumer that physically inlines must still prove the splice;
   citing `geistRekon_folge` alone for a spliced body overclaims. **P0**
   (owner: lowering/certificate; needs 287 interface).
2. **`nachOk` is stated, not derived.** Only the entry half (`vorOk`) is
   proved from `rufAt`; `ensures` over the actual result between entry and
   return worlds (`InlinePflicht.nachOk`, 139–144) awaits its derivation
   (CUTS 263–266). Contracts apply at actual values and sites — the field
   already has the right shape, but the proof is missing. **P0** (owner:
   AufrufOpt follow-up or certificate lane).
3. **Indirect calls have no ghost form** (`callInd`/`bindCallInd`; CUTS 272),
   matching the target side having no indirect-call form (`Typen` has only
   `call32`/`ret`). Lowering an indirect call today has neither a ghost
   obligation nor a target instruction — it must be refused, not silently
   treated as direct. **P0** (owner: indirect-control work with GateStub C2 +
   provenance certificates; cf. sec. 6).
4. **Duty discharge is carried, not proved** (`hp`/`hr` with lock/resource
   sets, CUTS 267–271). Callee-duties-subset-caller against the caller’s
   declared writes footprint/lock floor is a validator-side check that does
   not exist yet. Holder/quiescent invariants are not available inside
   writers — the check must not assume them. **P1** (owner: validator).

## 6. Indirect entry provenance

**Correct within claim.** `ControlFlow.direktZiel` is computed from decoded
length only, never an emitter annotation (19–22), with reuse equations for
the three existing direct forms (189–218) and three concrete refusals plus
one acceptance (306–323, 428–431). `Byteschritt.fetchDekodiert` refuses
truncated/non-canonical/inaccessible/length-inconsistent inputs (49–56) and
`byteschritt` takes only the state, so a forged `Decodiert` cannot inject an
instruction (66–76). `Bild.eintraege` are checked inputs; the decoded-start
producer is OPEN (CUTS 462–464) — correctly not invented.

**Real gaps:**

1. **No indirect-target rule exists.** Jump tables, register/memory indirect
   branches, returns-as-provenance, and `entry fn` values (N575–N577) have no
   certificate form; `ControlFlow` CUTS says so explicitly (459–461) and
   `Typen` has no indirect `Befehl`. `IMAGE-ABI` sec. 6 requires either a
   shipped-and-rechecked certificate or refusal. **P0** (owner:
   image/indirect-control work; `Relokation` site classes + GateStub C2 +
   EntryState C4 jointly).
2. **`ret` is a machine step, not a provenance.** `Ausfuehrung` `ret` pops
   any readable word into `rip` (127–132) and `Zugriffe` records its read
   footprint (58, 336–354) — both correct as stated. Neither proves the
   target is a live caller frame or a listed terminal state (`IMAGE-ABI`
   sec. 6 requires it). Reading `schritt_ret_erfolg` as control-flow
   integrity overclaims. **P0** (owner: call-save discipline + validator
   tracking; needs the `rsp`↔`Rahmen` bridge of sec. 2).
3. **Call targets are unchecked at step time — correctly.** `call32` sets
   `rip` without checking the target’s executability or entry status; the
   fault surfaces at fetch (`Byteschritt`) and admission at the validator
   (`direktZielOk`). This layering is sound provided no consumer reads the
   step equation as an admission. The audit records it so a future motion
   lemma does not drop the fetch/admission premises. **P2** (documentation
   only; no code change).
4. **`entry fn` provenance tracking is unwritten.** N575–N577 discipline
   (where the value stands, no Gabbro caller taking one, one whole hand-over
   outside loops) plus M140 (no forged pointer) needs the value tracked from
   creation (named designator or gate answer) to each indirect site. The
   source checker enforces the shape; the x86 side has no tracking theorem.
   **P0** (owner: GateStub C2 + image work).

## 7. Return and generic gates without OS assumptions

**Correct within claim, and OS-free as required.** `Stapel.sichereErgebnis`/
`ladeErgebnis` (332–339) are just `write64`/`read64` at a caller address with
the round-trip needing readability (341–349) — a memory obligation, not a
return protocol. `FremdRuf.GateData` keeps dispatch labels, register bindings
and costs as program DATA constraining no answer (header + 37–46), and the
per-gate theorems speak in the gate’s own effect terms. `Syscall.SysAbi.gut`
checks distinct in-registers, distinct parameters, out-not-clobbered (63–69)
with the `write` ABI pinning `rcx`/`r11` clobbers (55–59). No helper bakes in
a platform dispatch table, a kernel behaviour, or an `os_bindung_*` premise —
the historical software premises stay gap records per `IMAGE-ABI` sec. 12 and
qualify no image. The `clone` register behaviour (only `rcx`/`r11` destroyed)
is likewise a gap record, not silicon (`IMAGE-ABI` sec. 8).

**Real gaps:**

1. **Caller-side stub correspondence is C-only.** The checked
   declaration (N063–N066/`bindungsregel`), the malformed-stub refusals
   (C186 region-without-`or R`; C187 stack-gate-without-trampoline-regs) and
   the `tor.*`/`faden.*`/`arena.*` template instances are proved against the
   abstract model and the C emission; **every x86-byte instance is OPEN**
   (`IMAGE-ABI` secs. 9, 17; `QUELLBRUECKE` sec. 6). A C lemma does not
   discharge an x86 site. **P0** (owner: template x86 instances, wave-B).
2. **Callee-side obligation (c) has no supplier.** `IMAGE-ABI` sec. 11
   requires, per listed gate/foreign site: (a) checked declaration, (b)
   proved x86 stub correspondence, (c) a supplied Lean-proved callee contract
   at the ACTUAL arguments/results/effects. (c) exists nowhere today; gate
   names, `assume` items and `os_bindung_*` premises discharge nothing.
   Until supplied, using images are refused by final validation. **P0**
   (owner: binding/kernel-logic contracts in Gabbro+Lean; generic mechanism,
   per-target data).
3. **Return channels need the same treatment as calls.** Fallible gates
   (`-> T or R`, `tor.fehlbar`/`bindAxiomElse`), region answers
   (`tor.region` with `ensures … <= lenof(result)` over a singly-bound name),
   `-> never` bodies (`bindAxiom`/`Endblock` arms never fall off), and the
   `N572 child`-region handoff plus `tor.trampolin`/`tor.kind` child path are
   all C-level facts awaiting x86 instances and entry predicates. The
   `AufrufOpt` reason channel (`grund`) covers source-side ghost order only.
   **P0/P1** (owner: GateStub C2 for caller half; EntryState C4 for child and
   `-> never` terminal states; callee side per (2)).
4. **Foreign bodies are refused until proved — keep it that way.**
   `IMAGE-ABI` sec. 10: an `extern fn` site without proved x86 template
   correspondence is refused; the declaration alone admits nothing. No helper
   contradicts this. The audit flags it because it is the most likely place
   for a future lane to weaken under schedule pressure. **Standing guard, no
   owner.**

## 8. Prioritized repairs and missing bridges

**P0 — blocks any call-ABI closure claim:**

1. `rsp` ↔ `Rahmen` linkage + call-boundary alignment enforcement at `call32`
   sites (sec. 2.1). Needs: dynamic-to-static frame mapping, per-site
   16-alignment proof, guard/overflow policy hook (EntryState C4).
2. Indirect-target certificates + `entry fn` provenance tracking (secs. 6.1,
   6.4). Needs: `Bild` start producer, GateStub C2 caller checks, per-site
   target-set proofs or refusal; M140/N575–N577 enforced at the site.
3. `ret`/terminal provenance with live-caller tracking (sec. 6.2) +
   callee-save convention per image (sec. 2.2). Needs: call-save discipline
   at every call/return pair; C187 shape generalised to ordinary calls.
4. Ghost coverage for indirect calls or explicit lowering refusal (sec. 5.3)
   + `nachOk` derivation (sec. 5.2). Needs: AufrufOpt follow-up; no silent
   direct-treatment of `callInd`/`bindCallInd`.
5. x86 stub correspondence per gate form + callee-side obligation (c) per
   site (sec. 7.1–7.2), including `child`-region/trampoline/`-> never`
   terminal paths. C lemmas are regression evidence only.

**P1 — needed before performance or motion work:**

6. `SysReg` ↔ `Register` mapping + `argReg`-vs-clobber disjointness
   (sec. 3.1–3.2). Owner: GateStub C2; reuse `SysAbi.gut`, do not re-state it.
7. Fault → `FortschrittG` stop mapping per form (sec. 4.1), keeping hardware
   faults distinct from admission refusals. Owner: per-form correspondence.
8. Cost accounting for call/stack/gate forms + retry-shape bounds (sec. 4.2).
   Owner: CostSummary C3; no constant bound for unbounded retry.
9. Red-zone/guard policy per image (sec. 2.3); narrow width-alias rules at
   call boundaries (sec. 3.4). Owners: EntryState C4; narrow bridge.

**P2 — hygiene:**

10. `argReg ≠ rsp/rbp` lemma; fetch/admission premise threading for motion
    lemmas; SCFG-side spill application (waits 287); tearing/atomicity stays
    OPEN with `kein_atomarer_zugriff`/`keine_ablauf_spur` as the guardrails.

## 9. Probe evidence (all in-tree, with lines)

Positive (accepts what must accept):

- `Stapel.rahmenZeuge_ok` (533–534): `rahmenOk {0x2000, 32} = true` by
  `decide`. `rahmenZeuge_ausgerichtet` (537–539): 16-aligned top.
  `rahmen_schreibLese_zeuge` (557–580): slot-1 save of 42 reads back with an
  observable byte change. `argReg_sonde_rdi`/`_r9` (292, 296).
- `Ausfuehrung.probe_ruf_kehr` (804–806): `call +32` stores 4101 at 8184 and
  `ret` restores `(4101, 8192)`. `probe_schub_liest_alt` (809–811): `push
  rsp` stores OLD top 8192. `probe_nimm_rsp_gewinnt` (826–828): `pop rsp`
  takes 7, discarding the increment. `zeuge_speicher_aendert_sich` (787–789):
  reached store-changing run.
- `Zugriffe.probe_zugriff_ruf_wert` (619–622): extracted call word is ACTUAL
  next RIP 4101. `probe_zugriff_schub_wert` (613–616), `probe_zugriff_nimm`
  (631–634), reached witness (591–597).
- `ControlFlow.ziel_anfang_akzeptiert` (428–431): disp 0 admitted at next
  start. `cmov_speicher_zeuge` (279–300): flag-selected word stored and read
  back with observable change.
- `SpillPrivate.spillPrivatOk_positiv` (60): private in-frame slot admitted.
  `spill_fill_kommutiert_zeuge` (188–218) and `spill_tso_zeuge` (327–347):
  both-orders agreement with observable foreign change, spill bytes untouched.
- `AufrufOpt.geistRekon_zeuge` (191–253): ghost pair + contract value +
  memory change + order leg co-occur on a reached run.

Negative (refuses what must refuse):

- `Stapel.zeuge_ausserhalb_verweigert` (583–585): slot 4 of 4 saves nothing.
  `rahmen_unaligned_verweigert` (588–590): base `0x2001` fails `rahmenOk`.
- `Zugriffe` refusal family (466–527): bad length / failed load / store /
  push / pop / call / ret each admit no successful step.
- `ControlFlow.ziel_mitte_verweigert` (306–309), `ziel_daten_verweigert`
  (311–316), `ziel_aussen_verweigert` (318–323); `cmovMem_feheler_bleibt`
  (117–124): faulting CMOV-memory refuses even when untaken.
- `SpillPrivate` admission refusals (42–57) and joint refusals (70–87):
  address-taken / extent-named / out-of-frame slots never admitted.
- `AufrufOpt` CUTS boundary as negative scope: indirect calls have no ghost
  form (272) — lowering one as direct is outside the proved obligation.

## 10. What this audit did not do

- No re-verification of arithmetic/flags, memory ranges, decode boundaries,
  final image, weak memory, invariant lifetime, dynamic regions, float/SIMD,
  budget/observations, source footprint, or end-to-end trust beyond the
  call-ABI consumer edges cited above. Those belong to sibling audit lanes
  404–409, 411–415.
- No `lean-bau`/`lean-probe` execution: this lane adds no Lean file, so no
  proof gate is affected. All cited theorems are merged, reviewed helpers;
  line numbers are as-read at audit time and may drift on later merges.

*CUTS of this document: prose review evidence only. No decoder, encoder,
validator, refinement, cost-transfer, or final-image acceptance is proved
here. Every machine-behaviour claim is tied to the `Typen`/`Speicher`
vocabulary and the sections named beside it; anything beyond the pilot
`Befehl` subset, beyond ordinary coherent RAM, or beyond the listed entries
is an explicit gap in sec. 8. Hardware assumptions mean silicon-only
behaviour; every software-behaviour premise is named as such.*
