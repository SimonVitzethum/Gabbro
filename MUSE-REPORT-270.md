# MUSE-REPORT-270: Integer and flag semantics

Lane 270 (wave A). Branch `muse/270`. Model: opencode-go/muse-spark-1.3-contributor.
No delegation, no other model calls.

## What was done

Implemented `grammatik/Grammatik/X86/Wort.lean` (407 lines, new file) over the
REAL canonical types from `Grammatik/X86/Typen.lean` (`Wort = BitVec 64`,
`Flags`, `Bedingung`, `Breite`). No independent register/instruction/state
types were created. One umbrella import line (`import Grammatik.X86.Wort`)
was appended to `grammatik/Grammatik.lean` — the only edit outside the owned
file. Signatures for lane 272 are in `.tmp/INTERFACE.md` (gitignored scratch).

### Definitions

- Width core: `maske`, `trunc`, `addB`, `subB`, `xorB`, `zext`, `signBit`,
  `sext` (skeleton kept; all take a `Breite`, so no zero-width words exist).
- Tests: `negB`, `sfTest` (top bit via `testBit 63`), `zfTest` (`== 0`),
  `bitAt`, `popCount8`, `parityEven` (EVEN parity of `toNat % 256`).
- Carry/overflow core: `cfAdd` (`2^64 ≤ x+y`), `cfSub` (borrow),
  `ofAdd`/`ofSub` (pure sign-bit functions of `Bool` args, so CF and OF
  cannot be confused), `afAdd`/`afSub` (nibble boundary).
- Exported: `add64`, `sub64`, `xor64 : Wort → Wort → Wort × Flags`
  (ADD/SUB: AF `some`; XOR: CF/OF `false`, AF `none`), and
  `bedingung : Bedingung → Flags → Bool` (all 16 constructors, Intel mapping).

### Theorems (every premise used; `decide` tactic only for concrete probes)

- Values: `add64_wert`, `sub64_wert`, `xor64_wert`.
- Flag meanings: `add64_cf`, `add64_of`, `sub64_cf`, `sub64_of`,
  `add64_sf/zf/pf/af`, `sub64_sf/zf/pf/af`, `xor64_sf/zf/pf`,
  `xor64_cf`, `xor64_of`, `xor64_af`.
- Condition table: `bedingung_o/no/b/ae/e/ne/be/a/s/ns/p/np/l/ge/le/g`.
- Widths: `maske_nat`, `maske_b64`, `trunc_b64`, `addB_b64`, `subB_b64`,
  `xorB_b64`, `zext_b64`.
- Boundary probes (`by decide`, concrete only): `probe_add_carry_no_overflow`
  (CF without OF), `probe_add_overflow_no_carry` (OF without CF),
  `probe_sub_zero`, `probe_sub_borrow`, `probe_parity`, `probe_sext`,
  `probe_xor_self`, `probe_bedingung_lt` (`1 - 2`: `l` holds, `g`/`a` fail,
  `b` holds).

### Checks

- `./lean-probe grammatik/Grammatik/X86/Wort.lean`: 0 errors.
- `./lean-bau` (last full run): `exit 0`, 0 error lines,
  `Build completed successfully (367 jobs)`, `Wort` built in 414 ms.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. `#print axioms` for
  the main theorems: at most `propext`, `Classical.choice`, `Quot.sound`
  (`maske_nat` axiom-free). CUTS block at end of file.
- No `_zeuge` companions: no theorem quantifies over program syntax
  (`Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args`) and the task names
  no `ZEUGE:` target; the wave's witness demand is met by the eight
  concrete operand probes above (no memory/state witness belongs here —
  lane 272 owns state transitions and the memory-changing witness).

## What remains open (see CUTS in the file)

No execution/decoder/encoding, no narrow-width flag snapshots, no
memory/state/TSO/source-correspondence/ABI/cost/image claims. The nibble-AF
model, the even-parity PF reading and the condition table are stated, not
verified against hardware. The bridge (lane 277) must still preserve source
range/fault semantics.

## Notes on the task (nothing believed wrong)

- One elaboration detail: the `Flags` field `of` collides with the `of`
  keyword, so `{ of := … }` structure syntax does not parse; the three
  helpers use `Flags.mk` (order `cf pf af zf sf of`). Documented in
  `.tmp/INTERFACE.md` for lane 272. No statement was weakened.
- `decide` appears as a *term* inside computable `Bool` definitions
  (`cfAdd`, `cfSub`, `afAdd`, `afSub`), matching existing project style
  (4 precedents in `Grammatik/*.lean`); the `decide` *tactic* is used only
  for the finite concrete probes of §9, per the task.
