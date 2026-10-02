# MUSE-REPORT-692: Observable defined and undefined RFLAGS

## Task
Lane 692: model a precise raw RFLAGS representation with sound
defined/undefined effect rows for selected integer/shift/mul/div
forms, plus a byte-facing PUSHFQ observer (POPFQ restore with
CPL/IOPL gating), reusing canonical arithmetic and proving
adapters for producer abstractions. Joint fetched run plus
planted refusals required.

## What was done
New module `grammatik/Grammatik/X86/ArchitecturalFlags.lean`
(~1540 lines, all `by`-proved, no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`), plus the additive umbrella import in
`grammatik/Grammatik.lean`. Nothing else touched.

- §2 Raw model: `rbit`, `Steuer` (cpl/iopl/ifBit/vm), `ArchZustand`
  (kern + raw word + control), `liestStatus`, `archOK`, projection
  `projiziert` with `projiziert_flags`.
- §3 Defined AF per width: `trunc_nibble` (truncation keeps the low
  nibble, via `and_maske_nibble` + `maske_nibble`), `afAddB`/`afSubB`
  equal to canonical `afAdd`/`afSub`, NEG/CMP rows.
- §4 Effect rows: `AluOp` + `definiert` table; relations
  `addErlaubt`/`subErlaubt`/`negErlaubt`/`logikErlaubt`/
  `mulErlaubtU`/`mulErlaubtS`/`divErlaubt`/`schiebErlaubt` reusing
  accepted snapshots and validity relations; adapters
  (`mulU_hat_roh`, `mulS_hat_roh`, `logik_hat_roh`,
  `schiebAdapter`) and free-choice witnesses (`mulU_sf_frei`,
  `logik_af_frei`, `div_alles_frei`, `schieb_of_frei`).
- §5 Consumer admission: `verbrauchOK` table with pins,
  `add/sub/neg/logik/mul/shift-einsVerbrauch_sicher`,
  `divVerbrauch_verweigert`, derived `rohAf_frei`.
- §6 PUSHFQ/POPFQ: one-byte adapters (`pushfqByte`/`popfqByte`,
  lengths pinned), `pushfqWort` (VM/RF cleared, status preserved),
  Table 1-12 case masks with load/preserve/IF/IOPL facts,
  `popfqWort_bit` master equation, both steps with success
  equations, frame/readback/arch lemmas, v8086/stack/foreign-byte
  refusals; pilot `decode` refuses 0x9C/0x9D by `decide`.
- §6c Joint witnesses: `pushfq_lauf_zeuge` (fetched add sets
  `rax` with defined AF; fetched PUSHFQ saves the cleared image to
  changed stack memory with RF cleared; two MUL undefined choices),
  `pushfq_af_unterscheidet`, `pushfq_popfq_rundgang`,
  `popfq_if_gating_zeuge`, concrete dead/unreadable-stack refusals.

## Verification
- Last `./lean-probe`: `== 0 error(s)`, exit 0.
- Last `./lean-bau`: `Build completed successfully (467 jobs)`,
  `✔ [466/467] Built Grammatik`.
- `#print axioms` for all 71 theorems: within
  `[propext, Classical.choice, Quot.sound]` (standard triple);
  most are `[propext]` or `[propext, Quot.sound]`.

## Provenance checked (Intel SDM 325462-093US, Sep 2026, local
`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`)
ADD entry "OF, SF, ZF, AF, CF, PF set according to the result"
(Vol. 2A 3-14); NEG CF rule; MUL/IMUL/DIV/IDIV/SHL/SAR flag rows;
PUSHFQ entry (Vol. 2B 4-528, VM/RF cleared, none affected); POPFQ
Table 1-12 (Vol. 2B 4-407); EFLAGS init/reserved bits and Figure
3-8 positions (Vol. 1 3.4.3).

## Open / not claimed (see file CUTS)
FP/FPU rows; INC/DEC, ADC/SBB, CMPXCHG/XADD, BT, SAHF/LAHF;
16-bit POPFQ, VME/PVI rows, task-switch/real-address rows;
pending-interrupt delivery (only the IF bit); TSO/concurrency;
wiring into `decodeExt`/`schritt` (adapters are the boundary for
owners 660/672); no source/checker/Spec/goal claim; silicon
behavior stays a named assumption.

## Findings for the coordinator
1. Two producer abstractions adapted, not trusted: `mulFlagsU`'s
   SF/ZF/PF preservation and DIV's whole-snapshot preservation are
   exhibited as single admissible members of the free relations.
2. Toolchain notes: `interval_cases` unavailable (used omega
   disjunction + `decide`); nested multi-line structure literals
   fail to parse (single-line nested records + helper defs used);
   `decide` needs closed goals (free store variables break it --
   closed `witStore` used); `obtain` clears its source in this
   toolchain; `rw`'s auto-rfl is reducible-only (explicit closers
   needed after guard rewrites).
3. `decode [0x9C]`/`[0x9D]` both refuse by `decide`, so the
   adapters provably never shadow the pilot decoder.
