# Independent optimiser and full-binary closure review (lane 294)

*Owner: lane 294. Scope: review only — no Lean code, no Rust code, no model,
goal, parser, checker, emitter, ledger or MARKE change. Read LEAN-ZUERST.md
and WELLE-A.md owner tables before treating any name below as a claim.*

*Reviewed at commit `f4958150` (lane file pins `muse/294`). Status of the
three audited documents at that commit: merged wave-A designs after
coordinator review (lanes 275, 276, 277 with their review repairs).
`grammatik/Grammatik/X86/` contains exactly `Typen.lean`, `Wort.lean`,
`Speicher.lean` plus the unwired Rust mirror. No `Ausfuehrung.lean`,
`Codec.lean`, `IR.lean`, `TSO.lean`, validator, refinement theorem or closed
chain exists. Every "desired" below is prose; every "proved" is cited.*

## 0. Verdict up front

1. **No unsound admission found in the reviewed text.** For each of the nine
   starter families (constant/copy propagation, DCE, CSE/redundant loads,
   inlining, register allocation, peepholes, LICM, bounded unrolling, SIMD)
   and the two cross-cutting obligations (FP order/rounding; stops, atomics,
   locks, costs, progress), the legality conditions of `IR-VALIDIERUNG.md`
   §3 refuse every unsound instance this review constructed. The six
   counterexamples of §4 are admitted under the *naive* reading and refused
   under the document's actual clauses; they are evidence the refusals are
   load-bearing, not evidence of a hole.
2. **Two total refusals are correctly shaped as refusals, not as pending
   admissions.** SIMD validation is refused in full until a generic
   vector-correspondence rule covering fault order, visibility, tearing and
   FP control status is actually proved (`IR-VALIDIERUNG.md` §3 item 9,
   §7 item 9, §8 checklist); budget-exhaustion-stop preservation is OPEN
   until a ghost source-budget accounting correspondence (or proved
   separation with transfer) is proved (§3 item 11). Neither is weakened
   for coverage.
3. **Full-binary closure is correctly stated and unproved.** The delivered
   schema (`QUELLBRUECKE.md` §4) binds the FULL source-computed unit, takes
   decoded final bytes plus layout/relocations/entries through a proved
   checker, derives (not assumes) the per-access refinement via a generic
   validator-soundness theorem, and covers runtime, entries, ABI and the
   loaded mapping (`IMAGE-ABI.md` §§5, 10, 11). None of it is implemented:
   §5 tables desired against proved.
4. **Findings are explicitness and scope items, not soundness holes** (§6):
   the asm-body lowering refusal is unnamed in `IR-VALIDIERUNG.md`; the
   delivered theorem covers fragment-default units only; the source-budget
   link it must transfer through does not exist even unoptimised
   (`Budget.lean` C1/C5).

## 1. What was read

- `dokumente/x86/IR-VALIDIERUNG.md` (765 lines, lane 275 + second review),
  `dokumente/x86/IMAGE-ABI.md` (675 lines, lane 276 + second review),
  `dokumente/x86/QUELLBRUECKE.md` (613 lines, lane 277 + review repair),
  `dokumente/x86/TSO-GX-BRUECKE.md` (682 lines, lane 274 + review repair),
  `dokumente/x86/EMITTER-INVENTAR.md` (§§1, 9, 12 for pilot scope, asm,
  width tables), `dokumente/x86/BYTE-PILOT.md` (canonical encoding
  contract), `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§0–5 (active
  target chain, T1–T5, instruction families, W/GX reuse).
- Lean ground actually read: `X86/Typen.lean` (87 lines: `Befehl`
  constructors 53–68, `Speicher` 41–45, `Flags.af : Option Bool` 27–34,
  `Decodiert` 70–73, CUTS 81–86); `X86/Wort.lean` header + `maske/trunc/
  addB/subB/xorB` (modular at declared width, ADD/SUB AF defined, XOR AF
  `none`); `X86/Speicher.lean` header + `lesbar8/schreibbar8/read64`
  (per-byte permission checks); `Budget.lean` (`Op.cost` 103–106,
  `totalCost` 109–111, `runOps` 128–132, `runOps_within` 147,
  `runOps_exceeds` 167, premises P1 63–65, cuts C1 70–73, C5 532–548);
  `Folge.lean` (`Folge` 55–59, `fNach` 69–81, `fB` 116–135,
  `FolgeOk` 188–189, `FolgeLog` 207–209, `FolgeG` 214–218).
- Lean locations relied on through the lane-274/277 audits (not re-read
  line by line here, cited as such): `Zielsatz/Spec.lean`
  (`HardwareAnnahmen`, `FortschrittG`, `ZeitAbX`, `PrueferX`,
  `AkzeptiertSpecX`, `NutzerPflichtA`, `SchwachX`, `ZielX`/`ZielFX`,
  `GabbroZiel`); `Speichermodell/Sicht.lean` (`sb_erlaubt`,
  `sb_sc_verboten`); `Speichermodell/MaschineW.lean` (`SchrittW` lies/
  ungelesen/frisch/rmw); `Speichermodell/AtomarW.lean`
  (`schwach_ist_gX`); `KostenG.lean` (`kostenTief`); `Gleitkomma.lean` /
  `GleitkommaBits.lean` (source IEEE model); `Semantik.lean` (`einpassen`
  refuses unrepresentable answers).

## 2. Starter families: preservation audit

Notation per family: DOC = the legality condition as written; CHECK =
against which Lean semantics it was tested; VERDICT. Counterexamples
live in §4 and are referenced as CE-n.

### 2.1 Constant / copy propagation (§3 item 1)

DOC: every replaced use cites a validator-recomputed `avail` fact;
definition dominates use on every CFG path (recomputed dominators); no
intervening redefinition; width and signedness/unknown-ness preserved;
an `unknown`-signed source keeps its `narrow` guard.
CHECK: value substitution is pure-op congruence over arbitrary values;
the `narrow` guard is the `M101`/`M135` checked cast (per-function
unsigned scope `vorzeichenlose_namen_hier`, inventory §4), i.e. a
compare-plus-branch with a second exit edge, not a pure op.
VERDICT: sound as specified. The guard-deletion shape (propagate a
range fact to erase the `narrow`) is refused twice: propagation may
not delete the guard, and the CFG-map check (§2.2) preserves every
exit edge. No CE admitted.

### 2.2 Dead-code elimination, including faults (§3 item 2)

DOC: removed op must be pure (no memory token, no atomic, no call, no
check/assume, no stop/trap, no FP op that can trap under the bound
mode) AND validator-confirmed dead; stores/loads never dead by
liveness alone; trapping ops (divide, FP with traps, bounds-checked
access) are NOT pure even if their value is dead; stop classes
(`hardware` vs `logik`, `Budget` stops) unchanged by construction.
CHECK: `FortschrittG` stop kinds (hardware, flag, budget, `nieZurueck`);
`Budget.lean` `runOps_exceeds` (deleted ops shift exhaustion timing —
see CE-1, which is why item 11 keeps budget OPEN rather than closing
it here); fault delivery is a `hardware`-class outcome, never an
unobservable.
VERDICT: sound as specified. The fault-deletion shape (remove a dead
divide-by-zero, CE-2 analogue at DCE level) and the guard-deletion
shape (remove a dead `narrow`) are both refused: the first by the
purity list, the second by the exit-edge rule.

### 2.3 CSE / redundant loads (§3 item 3)

DOC: pure expressions need validator-recomputed identity only; LOADS
need additionally same object/width/alignment, no intervening token op
on possibly-overlapping objects (validator re-threads the token,
`unknown-overlap ⇒ refuse`), AND one global interleaving condition —
proved exclusive ownership, held-lock stability (lock held continuously
plus every writer in the unit writes only under the same lock, checked
from whole-unit effect exports), or immutability — because no
thread-local token fact rules out another thread's write. Atomics,
MMIO/device, volatile, foreign-observable memory ineligible without an
exact per-access concurrent equivalence theorem; no shared motion
across publication, fence, or acquire/release on local-disjointness
evidence alone.
CHECK: TSO bridge counterexample B (a G step's lowering interleaves:
per-access mapping mandatory) and counterexample C (tearing has no
single W message: alignment/extent proof mandatory); `HavocA` rely
quantifies over every atomic value; OBS-5 (unrecorded oracle reads see
last-write memory — local drain insufficient).
VERDICT: sound as specified, and the strongest clause in the document.
CE-3 (hoist above the publishing acquire) and CE-4 (reuse across an
asm store) are refused by 3(c) and by the token-plus-footprint rule
respectively. Two precisifications are owed (see §6.2, §6.4): name the
asm-body refusal, and check spill-address escape against call args.

### 2.4 Selective inlining (§3 item 4)

DOC: explicit block map with fresh SSA renames (validator-checked
capture-freedom); callee duties ⊆ caller duties at the site
(`requires`/`ensures` preserved in order, `writes` footprint subset,
lock floor respected); recursion guarded by decreases/depth discipline;
call-log preservation via explicit GHOST-EVENT reconstruction (callee
identity, actual argument values, return value, reason-channel
outcome) in source call-log order, for direct AND indirect calls;
contracts hold at entry/return with actual values, so identical
contracts without ghost events are refused.
CHECK: `Folge.lean`: `FolgeLog` demands the DIRECTLY older log entry
behind every ordered event be a `vor` return; `fNach` clears the armed
bit on compound statements, indirect calls, locks, loops
(`Folge.lean` 69–81); `FolgeOk` forces every `ruf` signature into
`ind` so no entry escapes through a function pointer (188–189).
VERDICT: sound as specified. The ghost-event requirement is exactly
the `FolgeG` shape lifted through the transform, and the indirect-call
inclusion matches the `ind` discipline. The preservation proof itself
is OPEN (IR CUTS + §8 checklist), which the document states.

### 2.5 Register allocation and private spills (§3 item 5)

DOC: colouring map with validator-recomputed liveness; spill slots
FRESH private objects (frame, never address-taken, never named by any
source extent); spills thread the token as ordinary frame accesses;
callee-saved registers saved/restored on every path; flags clobbered
only where dead. Proof burden discharged once generically against the
TSO-bridge memory relation (freshness ⇒ disjointness ⇒ commutation
with every interleaving).
CHECK: TSO bridge O-spill (`GetrenntK`: never in another thread's
footprint, never in `Tg`, never oracle/device-observed); O-align
(byte→carrier mapping); IMAGE-ABI §8 (spills are validated
loads/stores to thread-private slots; over-wide slots, overlapping
frames, clobbered caller-saved restores refused).
VERDICT: sound as specified. CE-5 (16-byte fused spill over two live
carriers) is refused by the width/slot rule and independently by
O-align. One Verbindlichkeit is implicit: "never address-taken" must be
decided over call arguments and gate out-params too, where `N571`
(no `requires` extent names the slot) already refuses the gate shape
checker-side (§6.4).

### 2.6 Peephole lowering / instruction selection (§3 item 6)

DOC: each window cites a reviewed register rule; side conditions
re-decided (widths, flag liveness, displacement fits signed-32, no
memory-token op inside a pure rule's window); per-rule generic proof
over arbitrary operands including flags touched, fault behaviour
(`div` traps preserved), and validator-recomputed cost annotation.
CHECK: `Wort.lean` keeps CF (unsigned carry from `toNat`) distinct
from OF (sign-bit overflow) by construction; `Flags.af = none` is
undefined, never false (`Typen.lean` 27–34); pilot covers only
64-bit add/sub/xor/cmp — every narrower/multiply/divide/shift form is
an unproved extension, so no rule can cite it yet.
VERDICT: sound as specified, and currently almost vacuous in the best
sense: the rule register has no members and the pilot admits only the
forms it admits. Strength-reduction shapes (`imul`→`shl`, CE-6) are
refused until a rule proves flag/fault identity per width.

### 2.7 LICM (§3 item 7)

DOC: validator-recomputed invariance; speculative hoisting of a
possibly-faulting op past its guard REFUSED unless proved
non-faulting over hoisted inputs from source-computed, rechecked
range evidence; memory-token motion only under item-3 interleaving
evidence; atomics/locks/calls/checks never hoist; header/back-edge
structure preserved.
CHECK: hoisting `x / n` above `n != 0` turns an untaken path into a
`hardware`-class stop (CE-2); `FortschrittG` stop classes are checked
data, never optimised away.
VERDICT: sound as specified. The fault-hoist (CE-2) is the canonical
refusal and the document makes it one.

### 2.8 Bounded loop unrolling (§3 item 8)

DOC: explicit factor `k` + trip-count evidence (constant bound or
guarded remainder path preserved as part of the map); body duplicated
with fresh names; remainder-join `phi` nodes complete; token ops
duplicated in order, never fused; loop-carried values threaded;
no new back edge; bounded prefix terminates iff the first `k`
iterations did.
CHECK: fusion of two token ops into one wider access would change
tearing/visibility (TSO counterexample C); the no-fusion rule plus
per-copy token threading forbids exactly that.
VERDICT: sound as specified.

### 2.9 Selective independent-lane SIMD (§3 item 9)

DOC: validator-decided lane independence (stride ≥ width,
extent-checked; gather/scatter REFUSED in the starter profile);
lane count × element width = vector width with alignment evidence
from the TSO atomicity table; FP lanes keep per-lane rounding and
exception/NaN behaviour identical (no reassociation, no fast-math);
no cross-lane token op; tail preserved unless proved multiple; plus
four independently-refusing obligations — (a) fault order, (b)
visibility order vs concurrent observers (shared vector stores refused
until the TSO bridge decides the rule), (c) tearing equivalence
(full-vector atomicity only where the bridge table grants it),
(d) FP control/mask word and sticky-flag identity in lane order;
CONDITIONAL REFUSAL: no SIMD admitted on a pending theorem; every SIMD
certificate refused until a generic vector-correspondence rule is
actually proved (the pure non-trapping integer candidate over proved
private-or-immutable memory is first in the proof queue, accepted only
after its proof).
CHECK: pilot has no vector form at all; TSO bridge has no vector
table; FP mapping belongs to lane 278 (FLOAT-ZEIT, unmerged).
VERDICT: sound as specified — the clause admits nothing today, which
is the correct posture. CE-3b (lane-visibility inversion) shows why
lane-disjointness alone could never suffice.

### 2.10 Cross-cutting FP (§3 item 10)

DOC: rounding mode and evaluation order are checked state; no
reassociation, no silent FMA fusion, no narrowing/widening, no motion
across a rounding-mode scope boundary (validator carries the scope
from layer C); SIMD keeps lane associativity; the lane-278 IEEE
mapping is the reference; anything it does not cover is refused.
CHECK: source IEEE model exists (`Gleitkomma*.lean`); target mapping
does not (no FP form in `Typen.lean`, lane 278 unmerged).
VERDICT: sound as specified; admits nothing today beyond scalar
shapes the mapping will cover.

### 2.11 Cross-cutting stops/atomics/locks/costs/progress (§3 item 11)

DOC: stops never deleted/introduced/reclassified; atomic ordering only
ever equal; RMW success/failure distinctness kept; no motion across
fences/lock ops; acquire/release pairs preserved on every path; no
motion into/out of locked regions except pure SSA ops under the token
rule with the lock held at both ends; ranks/floors rechecked; costs in
three strictly separated levels (a) re-summed declared costs as a
mismatch check only, (b) opaque measured work, (c) machine-work bound
OPEN with lane 278 — plus the ghost source-budget accounting
correspondence (or proved separation with transfer) for
budget-exhaustion stops, OPEN; declining never weakens a bound; CFG
maps preserve every exit edge; DCE never removes a spin/wait load;
lowering-internal straight-line steps stutter only under the §4.3
progress argument.
CHECK: `Budget.lean` proves the arithmetic of bounds
(`runOps_within`, `runOps_exceeds`, `per_pass_respected`) over DECLARED
op lists — and cuts the link to execution twice: C1 (no verified link
from `Stmt`/`Block` to its op list; threading a budget through
`execStmt`/`execBlock` is cut) and C5 (`SeqElem` assignment is
declared, resource threading untracked, no `execStmt` link). So even
unoptimised, no theorem connects a deleted/duplicated op to a preserved
exhaustion stop. CE-1 makes the arithmetic concrete.
VERDICT: sound as specified precisely because it claims nothing about
budget stops beyond re-summing. The OPEN is load-bearing (see §6.3).

## 3. Extra invariant optimisations (LEAN-ZUERST.md § narrowed list)

The five named opportunities were each tested against the scoped-
invariant discipline (invariants hold where proved: at returns, behind
`vor` returns, under held locks as observed by the holder — never
inside a running writer or an arbitrary held section; no inferred
`ensures`; no local-only token argument for shared memory):

1. **Proved range-check removal.** Admissible only with source-computed
   range evidence proved AT the actual location (`N463`/`N571` family:
   the gate's `ensures … <= lenof(result)` over a name bound once;
   constant-clause fixed-size bindings). Evidence from a lock
   invariant or an owed invariant may justify removal only where that
   invariant is claimed: not inside a running writer (the writer
   itself mutates the carrier mid-loop — entry invariant does not
   survive the loop's own stores), not in another thread, not across a
   release. The CE-4b shape (remove a bounds check inside the writer's
   own mutating loop on entry-invariant evidence) must be refused;
   IR §3 items 3/7/11 give the validator the clauses to refuse it
   (interleaving evidence, non-faulting evidence at hoisted inputs,
   exit-edge preservation).
2. **Strength reduction.** Integer `i * 8` → `i << 3` (or add-chains)
   changes flag setting (CF vs OF shape per `Wort.lean`: they are
   computed differently by construction) and, for checked arithmetic,
   the hardware-stop point. Admissible only as a register rule with a
   per-width flag/fault identity lemma over arbitrary operands (§3
   item 6) — none exists; refused until then. FP reduction (`a*2` →
   `a+a`) additionally changes rounding/NaN payload and is refused
   under item 10 until the lane-278 mapping covers it.
3. **Ownership-based alias separation.** Admissible only from
   source-computed exclusivity (checker-decided thread-privacy, fresh
   spill/region freshness, or held-lock stability with whole-unit
   writer discipline per §3 item 3). A function-local "no other
   mention" argument is a local-only token argument for possibly
   shared memory and proves nothing against another thread's write
   (TSO counterexample B). Refused without the cited evidence.
4. **Stable protected loads.** A load may be reused across program
   points only while the covering lock is held continuously AND every
   writer in the unit is proved to write under the same lock. Reuse
   across an unlock, or hoisting above the acquire that publishes the
   object (CE-3), changes the GX execution read. Refused by §3 items
   3/7.
5. **Private-memory SIMD.** The first-in-queue candidate (pure
   non-trapping integer lanes over validator-proved private-or-
   immutable memory with proved tail handling) is prioritised for
   proof and refused until its proof closes (§3 item 9 conditional
   refusal, §7 item 9). Correct posture; CE-3b shows the visibility
   half that private-memory scoping alone does not discharge for
   shared objects.

## 4. Full-binary closure audit

### 4.1 The validator binds the entire source unit

`QUELLBRUECKE.md` §4 (after the 2026-10-01 review repair) takes NO
independent refinement premise in the delivered theorem
(`schluss_x86`): the per-access refinement is DERIVED inside the chain
from validator acceptance via the generic `valX86_sound`, never
assumed; the `hR` premise lives only in the labelled-internal
composition lemma. The unit enters by FULL computed identity
(`hE : E = einheitAllg u P hn`), not by `E.P = P` alone, so `starts`,
`S`, `Q`, `sp0`, `gestartet` cannot be attacker-chosen metadata.
`valX86` binds that full unit (`valX86 E bild`, never `valX86 P
bild`). Delimitation (stated in §§1.2, 3, 4, and honestly): beyond
the fragment defaults (`S := leer`, `Q := axWahr`, parameterless
`entry` roots, zero memory) the generalisation — compute every
metadata field from source or prove field-by-field identity — is open
work. The schema therefore closes fragment-default units only; tables,
statics/globals, shared atomics in bridged units, arenas, gates/
foreign bodies, linking, handler entries, floats/time remain enumerated
gaps (§3 items 1–11). No clause lets a general unit through on
fragment evidence.

### 4.2 Final relocated decoded executable bytes

`IMAGE-ABI.md` §§1, 4: the validation input is the exact byte string;
decode boundaries are validated OUTPUT (decoder walks mapped virtual
ranges producing `(address, Befehl, length)` triples); instruction
length belongs to validated decoding, never to an emitter annotation;
relative targets are computed from the virtual next-RIP, never from a
file offset; patched sites are re-decoded with correspondence
re-checked; any byte not covered by exactly one instruction, data
object or explicit padding is refused; overlapping/ambiguous/
unsupported decodings refused. The second-review repair (data-field
relocation class) makes declared function-pointer/static-address
tables and constant pools legitimate sites of their kind instead of
misreading them as violations — while keeping the class-specific
checks (width, alignment, target rule: code pointers to decoded
instruction starts in executable bytes or listed entries). A proof
about a mnemonic list alone is insufficient (stated in §1 and plan
§0–1). No mnemonic-only shortcut exists in the text.

### 4.3 Runtime, entries, ABI, loaded mapping

Coverage (`IMAGE-ABI.md` §10): the validated image is the WHOLE
executable — emitted unit, generated driver, compiled-in binding code,
runtime, and handwritten pieces alike; an inventoried reason exempts
nothing from validation. Entries (§5): hosted `main`/`nolibc` hooks,
module init/exit, bare-metal `_start` + AP trampoline + stacks,
per-`start` thread roots with guard pages, interrupt/hardware entries
with save/restore/mask discipline, the clone-child trampoline path —
each with a checked entry-state predicate; a manifest row without
validated save/restore bytes admits nothing. ABI (§§7–8): gate
register maps against declarations (C186/C187 refuse malformed
stubs), foreign arity/prototype in the validator, aggregate layout
from the Lean front end (C `_Static_assert` pins have no standing),
`entry fn` value discipline (N575–N577), no int→ptr (M140), 16-byte
call alignment, red-zone discipline per image, spill/call-saved rules.
Loader contract (§11): checked image in exactly one of modes F/P;
segments mapped with exactly checked bytes/permissions (W^X, no
widening through shared pages); relocations applied exactly as
checked with re-decode on the loaded mapping; entries/starts as
generated; NO tool-correctness premise and NO software booked as
hardware (silicon-only assumptions: execution of mapped bytes per the
admitted profile, named device behaviour, named timing bounds).
External-body rule (§11, three conjuncts): (a) checked declaration,
(b) proved x86 stub correspondence, (c) SUPPLIED Lean-proved contract
obligation at the actual call — a gate name, an `assume`, or any named
premise alone discharges nothing; the `os_bindung_*` family and the
storage/page-return assumptions are gap records qualifying no image
(§12); where (c) cannot be supplied the path is OPEN and the image
refused. The emitted gate sequences' C-level template proofs do not
transfer silently (§9: every template's x86-byte instance is an
unproved wave-B obligation).

### 4.4 No assumed-simulation shortcut

Checked three ways: (i) the delivered theorem derives refinement via
`valX86_sound` (§4 review repair); (ii) `IR-VALIDIERUNG.md` §2.4 binds
both ends to the source (`lowerOk(E, G0)`, per-step `check_C`,
`layoutOk(Gn, B, Img)`) with no free initial graph, no duty-only
binding, no assumed refinement; (iii) the TSO bridge targets W
per-access with option-inclusion proved per event (counterexamples
A/B/C refute the SC shortcut, the block-transaction shortcut, and the
single-message tearing shortcut respectively). Nothing in the three
documents asks the reader to assume the desired simulation.

## 5. Concrete counterexamples (what the refusals exclude)

Each CE gives the source shape, the unsound transform, the divergent
observable, and the refusing clause. None is admitted by the reviewed
text; each would be admitted under the naive reading named beside it.

**CE-1 — DCE/CSE changes a budget-exhaustion stop (naive reading:
"stops untouched ⇒ preserved").** Source block costs `[1,1,1]`
(`totalCost = 3`, `Budget.lean` 109–111) under `perPass = 2`. Source
run: `runOps 2 2 [1,1,1]` stops `.budget "per_pass.ops" … 2`
(`runOps_exceeds`). Optimiser deletes the copy (`1+1+1` → `1+0+1` as
in IR §6): cost `[1,1]`, run reports `.ok 0` (`runOps_within`). Same
stop classes everywhere (no stop added/removed/reclassified), yet the
observable outcome differs (budget stop vs success). Refused as a
preservation claim by §3 item 11 (ghost budget correspondence OPEN);
IR §6/C1 records exactly this (`validator-resummed … NOT a proof that
budget-exhaustion stops are preserved`). Desired: ghost accounting
correspondence; proved: nothing.

**CE-2 — LICM hoists a fault above its guard (naive reading:
"invariant inputs ⇒ hoist").** `wenn n != 0 { y = x / n } sonst { y
= 0 }`; hoist `x / n` above the branch. At `n = 0` the source takes
the else (no fault); the hoisted program takes a `hardware`-class
stop. Refused by §3 item 7 (speculative hoisting of a possibly-
faulting op past its guard refused without proved non-faulting
evidence over the hoisted inputs, rechecked from source-computed
facts).

**CE-3 — CSE/load hoist crosses the publishing acquire (naive reading:
"disjoint local objects ⇒ reorder").** T0: `lock L { v = *p }`;
reuse `v` after unlock, or hoist `*p` above `acquire L` where another
thread publishes `p` under `L`. The reused/hoisted read sees the
pre-publication GX execution; the source read sees the published one.
Refused by §3 item 3(c) (no shared motion across publication/
acquire/release on local-disjointness evidence alone) and §3 item 7
(memory-token motion needs ownership/lock/immutability evidence).
**CE-3b — SIMD lane-visibility inversion (naive reading:
"lane-disjoint ⇒ vectorise").** Scalar sequence stores lanes 0,1 to a
shared object; concurrent observer may see lane 1 before lane 0 after
vectorisation where scalar order was observable. Refused by §3 item 9
(b)(c) and, until the vector-correspondence rule is proved, by the
conditional refusal of ALL SIMD validation.

**CE-4 — CSE across an inline-asm store (naive reading: "no SCFG token
op between ⇒ reuse").** `a = *O; asm volatile ("…" ::: "memory");
b = *O` with the asm body storing `O`; reuse `a` for `b`. The second
load observes the asm store in every real execution. Refused in
substance by the token/footprint rule — but the asm-body lowering
refusal that forces it is UNNAMED in `IR-VALIDIERUNG.md` (finding
§6.2): `FnRumpf::Asm` free text (inventory §9: unbounded by
construction) has no SCFG op form, so `lowerOk` must refuse any
function containing one; the document should say so explicitly.
**CE-4b — range-check removal inside the writer's own mutating loop
(naive reading: "entry invariant ⇒ remove").** Entry invariant `I`
over table `T` proved at function entry; loop body writes `T` while
holding the lock; check `i < len` removed on `I` evidence. The loop's
own stores invalidate `I` mid-loop; the removed check faults (or
silently overruns) where the source stopped. Refused by the
at-the-actual-location scoping (§3 items 3/7/11; LEAN-ZUERST.md
"no assumption that an invariant holds inside a running writer").

**CE-5 — register-allocation spill fusion/tear (naive reading:
"spills are private ⇒ any shape").** Two live 8-byte values spilled
to adjacent frame slots fused into one 16-byte vector spill, or one
8-byte spill split across a frame boundary. A concurrent observer
(another thread via a leaked address, a handler on the same stack
without red-zone discipline) sees a torn half-state no single W
message corresponds to (TSO counterexample C). Refused by §3 item 5
(slot width/privacy/freshness) and IMAGE-ABI §8 (over-wide slots,
overlapping frames refused).

**CE-6 — peephole strength reduction changes flags/faults (naive
reading: "same value ⇒ same window").** `imul r, 8` → `shl r, 3`:
identical modular value, different CF/OF setting (`Wort.lean` keeps
them distinct by construction) and, for checked arithmetic, different
hardware-stop behaviour; FP `a*2.0` → `a+a`: different rounding/NaN
payload. Refused by §3 item 6 (per-rule flag/fault identity over
arbitrary operands) and item 10 (no FP reassociation). No such rule
exists; the register is empty.

## 6. Findings (explicitness and scope — no soundness hole)

1. **No unsound admission.** Every CE above is refused by a named
   clause in the current text, including after the two second-review
   repairs (SIMD conditional refusal; budget-stop OPEN; premise-bypass
   removal and data-relocation classes in IMAGE-ABI).
2. **Asm lowering refusal unnamed (minor explicitness gap).**
   `IR-VALIDIERUNG.md` never names `FnRumpf::Asm` bodies. Since SCFG
   has no asm op form and the token design makes memory dependence
   syntactically visible, any function containing an asm body must
   fail `lowerOk` until a per-template machine-checked admission
   exists (template register `gabbro schablonen --tor`). Recommend one
   sentence in §1.3/§7 naming it. CE-4 is the witness that the
   sentence matters.
3. **Budget transfer rests on a link that does not exist even
   unoptimised.** `Budget.lean` C1/C5 cut the `Stmt`/`Block`→op-list→
   `exec` link; `totalCost`/`runOps` reason over declared lists only.
   The ghost source-budget correspondence of §3 item 11 must therefore
   bridge two gaps at once (declared-list arithmetic to execution,
   then execution through the transform). The document is honest about
   the second; it should cite C1/C5 for the first so no reader treats
   `runOps_within` as an execution theorem.
4. **Spill-privacy wording should name the escape check.** "Never
   address-taken" (§3 item 5) is decided over the whole transformed
   graph including call arguments and gate out-params; the gate case
   is already refused checker-side (`N571`: no `requires` extent names
   a spill slot). One cross-reference suffices.
5. **Scope delimitation to keep.** The delivered schema closes
   fragment-default units only (`einheitAllg` defaults,
   `QUELLBRUECKE.md` §§1.2/3/4). Tables, globals, bridged shared
   atomics, arenas, gates/foreign bodies, linking, handler entries,
   floats/time, and all of §5's per-program artefacts stay outside the
   trust path. Any status reporting must keep this boundary.

## 7. Claim ledger for this review

- May be said: the three reviewed documents specify a sound
  optimisation-validation architecture and a sound full-binary closing
  schema (refusals where needed, OPEN obligations where unproved); the
  six counterexamples show the refusals are necessary; the only Lean
  facts this review relies on are the pilot vocabulary, the
  word/memory helpers, `Budget.lean`'s arithmetic-plus-cuts, and
  `Folge.lean`'s order discipline.
- May NOT be said: that any optimisation is proved sound, that any
  image is validated, that `valX86_sound`/`schluss_x86` or any rule/
  motion lemma exists (all are phase-B proposals), or that the goal
  theorem covers a program the validator has not accepted. No Lean
  file is added or changed by this lane; no theorem, no axiom, no
  build claim beyond the untouched baseline.

## 8. Desired schema vs proved implementation

| Piece | Desired (prose) | Proved (Lean) |
|---|---|---|
| Pilot vocabulary | canonical types | YES: `X86/Typen.lean` (`Befehl` subset, byte `Speicher`, `af = none` undefined) |
| Integer/flag helpers | modular ops + CF/OF distinction | YES (helpers+lemmas): `X86/Wort.lean` |
| Byte memory | permission-checked LE access + frame facts | YES: `X86/Speicher.lean` |
| Instruction execution | pilot state transitions + memory-changing witnesses | NO: lane 272 unmerged |
| Decoder/round-trip | canonical bytes + generic consumption | NO: lane 279 unmerged, contract `BYTE-PILOT.md` only |
| SCFG + certificates + rule register | syntax, `lowerOk`/`check_C`/`layoutOk`, per-rule lemmas | NO: spec `IR-VALIDIERUNG.md` only |
| Source lowering/duties binding | Lean-computed `LowerMap`/`DutyExport`, full-unit computation | NO: audit `QUELLBRUECKE.md` only |
| Per-access TSO→W/GX | `D-tso/D-access/D-lower`, L-read/write/view/step/run | NO: design `TSO-GX-BRUECKE.md` only |
| Image/ABI/loader checking | byte-image/entry/relocation validator | NO: contract `IMAGE-ABI.md` only |
| FP/time mapping | IEEE bit facts, trap/mask scope, machine-work bound (c) | NO: lane 278 unmerged |
| Optimiser families (9 + invariant extras) | generic checked rules + preservation proofs | NO: legality spec only; SIMD totally refused; budget correspondence OPEN |
| Closing theorem | `valX86_sound` + `schluss_x86` over every source/image | NO: schema only |

*CUTS (this review proves nothing): no Lean definition, lemma, checker
Bool, decoder, validator, refinement or cost-transfer result is given
here. All implementation-status claims are by reading the tree at
`f4958150` (`X86/` holds three files; lanes 272/279/282–293 unmerged).
File/claim checks are by reading the cited definitions; no `cargo`/`lake`
run is owed by this docs-only task (baseline untouched). Open until
proved: every row of §8 marked NO, the §6 precisifications, and the
per-lane deliverables of wave A/B that this review does not pre-empt.*
