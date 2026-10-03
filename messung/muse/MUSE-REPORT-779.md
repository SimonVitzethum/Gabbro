# MUSE-REPORT-779: Hardware completion — XCHG ordering need

## Task
Lane 779: cover XCHG exactly where the source order needs it, with barrier
semantics and the refusal of bare-XCHG-as-optimisation elsewhere. Owned files
only: `grammatik/Grammatik/X86/XchgOrderNeed.lean`, `grammatik/Grammatik.lean`
(import line), this report.

## What was done
New module `grammatik/Grammatik/X86/XchgOrderNeed.lean` (~540 lines), reusing
canonical `TSOZustand`, `read64`/`write64`, `Fuss`, `dispWort`,
`rexByte`/`modrmMem`/`modrmReg`, `leBytes32`/`parseLe32`. No second evaluator,
no source/checker/Spec/goal/emitter change, no new numbers, no MARKE changes.

Manual provenance (clone-local `.tmp/HARDWARE-REFERENCES/`, Intel SDM
325462-093US Sep 2026): XCHG Vol. 2D 6-31/6-32 (opcodes REX.W+87 /r and
REX.W+90+rd, Operation TEMP:=DEST/DEST:=SRC/SRC:=TEMP, Flags None, memory
operand asserts LOCK# automatically regardless of LOCK prefix/IOPL, 90H NOP
alias), LOCK prefix Vol. 2A 3-565/3-566 (XCHG always asserts LOCK#), bus
locking Vol. 3A 11.1.2.2 (LOCK assumed for XCHG), memory ordering Vol. 3A
11.2.3.8/11.2.3.9 (total order of locked instructions; no load/store
reordered with a locked instruction; XCHG examples 11-8/11-9/11-10).

### Definitions
- `XchgForm`: `.mem base src disp` (ordering-carrying word exchange) and
  `.reg dst src` (register-only, no order).
- `brauchtOrdnung`: true exactly on `.mem`.
- `xchgZulaessig`: true exactly on `.mem` (bare register XCHG refused as an
  optimisation target).
- `XchgZustand`: register file + flags over canonical `TSOZustand`.
- `xchgAddr`: base-plus-displacement address from a register file.
- `xchgSchritt`: memory form swaps atomically in canonical memory exactly
  when the own buffer is empty (barrier), flags untouched; register form is
  a pure register swap with no barrier. All other cases `none`.
- `encodeXchg` / `xchgLen` / `rexXchgBits` / `decodeXchg`: canonical REX.W +
  0x87 rows (ModRM mod=2 + disp32 with SIB exactly when needed; mod=3 for
  registers). LOCK-prefixed, 90+rd-alias and truncated neighbours refuse.
- `xchgFuss`: eight `Fuss` bytes for memory, `[]` for registers.
- Witness: `xwReg` (rbp=8192, rcx=7), `xwFlags`, `xwTso0/1/2` (core 1
  issues byte 5 at 100 and flushes it), `xchgA`, `xwM`, `xwS`, `xwS'`.

### Theorems
- `rexXchgBits_rexByte`, `xchg_opcode_ok`, `xchg_modrmReg_felder`,
  `xchg_modrmMem_felder`, `roundtrip_xchg_reg`, `roundtrip_xchg_mem`
  (codec round trips; checked data, not fidelity).
- `XchgOrderNeed_verbindung`: successful memory exchange installs the swap
  (memory holds register value, register holds old word), flags unchanged,
  own buffer stays empty (fence-ready), form carries order, new word reads
  back. Every premise used.
- `xchg_mem_verweigert_bei_puffer` (barrier gate),
  `xchg_mem_verweigert_ohne_leserecht`,
  `xchg_mem_verweigert_ohne_schreibrecht` (permission refusals),
  `xchg_mem_bedarf`, `xchg_reg_kein_bedarf` (admission exactly on memory),
  `xchg_reg_ohne_schranke` (bare XCHG gives no barrier, so it must never
  stand where order is needed),
  `xchg_mem_fuss`, `xchg_reg_fuss_leer`, `encodeXchg_len`,
  `decodeXchg_lock_verweigert`, `decodeXchg_alias90_verweigert`,
  `decodeXchg_abgeschnitten_verweigert`.
- Witness facts `xw_issue`, `xw_flush`, `xw_tso_aendert`, `xw_erreichbar`,
  `xw_hbuf`, `xw_hrd`, `xw_hles`, `xw_hwr`, `xw_schritt`,
  `xw_mem_aendert`, `xw_dekodiert`.
- `XchgOrderNeed_verbindung_zeuge`: all premises jointly inhabited on a
  non-degenerate reached run (TSO issue+flush changes byte 100; the swap
  changes byte 8192 from 0 to 7); conclusions obtained by applying the main
  theorem.

## Build result
- `./lean-probe grammatik/Grammatik/X86/XchgOrderNeed.lean`: 0 errors; axioms
  within propext/Classical.choice/Quot.sound (no sorry/admit/axiom/
  native_decide/unsafe).
- `./lean-bau`: exit 0, 0 errors, 485 jobs, `Built Grammatik`.

## Open (see CUTS)
Round trip is not silicon fidelity; barrier is local to the acting core (no
foreign drain, no multi-lock total order, no W/GX simulation); sub-64-bit
widths, explicit LOCK prefix row, 90+rd alias row, segment overrides, HLE,
split-lock/tearing/timing, fairness, interrupts/devices stay open.

## Task remarks
Nothing in the task appears wrong. One scoping note: "refusal of
bare-XCHG-as-optimisation" is modelled as admission (`xchgZulaessig` false on
the register form) plus the proved no-barrier fact (`xchg_reg_ohne_schranke`),
not as a compiler pass change — no optimiser files were touched per the
lane constraints.
