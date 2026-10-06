/-
  File:      Grammatik/X86/SystemEvaluators.lean
  Subject:   Evaluators for the system rows that `SystemDecode` decodes
             but must refuse (no accepted evaluator exists there).

  Lane 1375: nine rows -- five admitted hint/cache NOPs (PREFETCHW,
  PREFETCHWT1, CLTS, INVD/WBINVD, WBNOINVD) and four decoded refusals
  (SYSENTER/SYSEXIT, LMSW/SMSW) whose MSR/CR0 state is unmodelled.
  PREFETCHh already has its accepted evaluator (`HwMemTypesWC`, never
  redefined here); the deferred `SysExtra` nine of `SystemDecode`
  (MSR/DF/debug state) stay with their own lanes (see CUTS).
-/
import Grammatik.X86.Hw.Familien.HwSystemForms
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder
import Grammatik.X86.TSO.Kern.TSO

namespace Gabbro.Grammatik.X86

/-- Evaluated system rows: five admitted NOPs plus four decoded
    refusals (MSR/CR0 state unmodelled, never admitted silently). -/
inductive SysEvalArt where
  | prefetchW | prefetchWT1
  | clts | invd | wbinvd | wbnoinvd
  | sysenter | sysexit | msw
  deriving DecidableEq, Repr

/-- Encoded length of each evaluated row (opcode-table lengths). -/
def sysEvalLaenge : SysEvalArt → Nat
  | .prefetchW => 3 | .prefetchWT1 => 3
  | .clts => 2 | .invd => 2 | .wbinvd => 2 | .wbnoinvd => 3
  | .sysenter => 2 | .sysexit => 2 | .msw => 3

/-- Length pins: every row carries its opcode-table length. -/
theorem sysEvalLaenge_pins :
    sysEvalLaenge .prefetchW = 3 ∧ sysEvalLaenge .prefetchWT1 = 3 ∧
      sysEvalLaenge .clts = 2 ∧ sysEvalLaenge .invd = 2 ∧
      sysEvalLaenge .wbinvd = 2 ∧ sysEvalLaenge .wbnoinvd = 3 ∧
      sysEvalLaenge .sysenter = 2 ∧ sysEvalLaenge .sysexit = 2 ∧
      sysEvalLaenge .msw = 3 := by
  decide

/-! ## 2. Byte decode: exact-length shapes only.

  Fixed two-byte rows: CLTS 0F 06, INVD 0F 08, WBINVD 0F 09,
  SYSENTER 0F 34, SYSEXIT 0F 35. Three-byte rows: PREFETCHW
  0F 0D /1 and PREFETCHWT1 0F 0D /2 with a MEMORY ModRM (mod=3
  refuses: the register form is no memory hint), LMSW/SMSW
  0F 01 /6//4 with a MEMORY ModRM (mod=3 refuses, so the
  RDTSCP/XGETBV/SWAPGS register rows are never shadowed),
  WBNOINVD F3 0F 09. SIB/displacement tails refuse (exact-length
  shapes only, the `decodePrefetch1287` precedent); truncated
  inputs refuse. -/

/-- Byte decode of the nine evaluated rows. The tail is always `[]`. -/
def sysEvalDecode : List Byte → Option (SysEvalArt × List Byte)
  | [b0, b1] =>
    if byteNat b0 == 15 && byteNat b1 == 6 then some (.clts, [])
    else if byteNat b0 == 15 && byteNat b1 == 8 then some (.invd, [])
    else if byteNat b0 == 15 && byteNat b1 == 9 then some (.wbinvd, [])
    else if byteNat b0 == 15 && byteNat b1 == 52 then
      some (.sysenter, [])
    else if byteNat b0 == 15 && byteNat b1 == 53 then
      some (.sysexit, [])
    else none
  | [b0, b1, m] =>
    if byteNat b0 == 15 && byteNat b1 == 13 &&
        (byteNat m / 8) % 8 == 1 && byteNat m / 64 != 3 then
      some (.prefetchW, [])
    else if byteNat b0 == 15 && byteNat b1 == 13 &&
        (byteNat m / 8) % 8 == 2 && byteNat m / 64 != 3 then
      some (.prefetchWT1, [])
    else if byteNat b0 == 15 && byteNat b1 == 1 &&
        ((byteNat m / 8) % 8 == 4 || (byteNat m / 8) % 8 == 6) &&
        byteNat m / 64 != 3 then some (.msw, [])
    else if byteNat b0 == 243 && byteNat b1 == 15 &&
        byteNat m == 9 then some (.wbnoinvd, [])
    else none
  | _ => none

/-- Every admitted row decodes to its row. -/
theorem sysEvalDecode_clts :
    sysEvalDecode [natByte 15, natByte 6] = some (.clts, []) := by
  decide
theorem sysEvalDecode_invd :
    sysEvalDecode [natByte 15, natByte 8] = some (.invd, []) := by
  decide
theorem sysEvalDecode_wbinvd :
    sysEvalDecode [natByte 15, natByte 9] = some (.wbinvd, []) := by
  decide
theorem sysEvalDecode_wbnoinvd :
    sysEvalDecode [natByte 243, natByte 15, natByte 9] =
      some (.wbnoinvd, []) := by
  decide
theorem sysEvalDecode_sysenter :
    sysEvalDecode [natByte 15, natByte 52] = some (.sysenter, []) := by
  decide
theorem sysEvalDecode_sysexit :
    sysEvalDecode [natByte 15, natByte 53] = some (.sysexit, []) := by
  decide
theorem sysEvalDecode_prefetchW :
    sysEvalDecode [natByte 15, natByte 13, natByte 14] =
      some (.prefetchW, []) := by
  decide
theorem sysEvalDecode_prefetchWT1 :
    sysEvalDecode [natByte 15, natByte 13, natByte 22] =
      some (.prefetchWT1, []) := by
  decide
theorem sysEvalDecode_msw :
    sysEvalDecode [natByte 15, natByte 1, natByte 48] =
      some (.msw, []) := by
  decide

/-- Register forms refuse: no memory hint without a memory ModRM. -/
theorem sysEvalDecode_prefetch_register_verweigert :
    sysEvalDecode [natByte 15, natByte 13, natByte 201] = none := by
  decide
theorem sysEvalDecode_msw_register_verweigert :
    sysEvalDecode [natByte 15, natByte 1, natByte 208] = none := by
  decide

/-- Neighbour rows of the shared groups are never shadowed. -/
theorem sysEvalDecode_rdtscp_verweigert :
    sysEvalDecode [natByte 15, natByte 1, natByte 249] = none := by
  decide
theorem sysEvalDecode_falsches_reg_verweigert :
    sysEvalDecode [natByte 15, natByte 13, natByte 0] = none ∧
      sysEvalDecode [natByte 15, natByte 1, natByte 56] = none := by
  decide

/-- Truncated inputs refuse. -/
theorem sysEvalDecode_leer : sysEvalDecode [] = none := rfl
theorem sysEvalDecode_esc_abgeschnitten :
    sysEvalDecode [natByte 15] = none := by
  decide
theorem sysEvalDecode_prefetch_abgeschnitten :
    sysEvalDecode [natByte 15, natByte 13] = none := by
  decide
theorem sysEvalDecode_wbnoinvd_abgeschnitten :
    sysEvalDecode [natByte 243, natByte 15] = none := by
  decide

/-! ## 3. Encoder and round trip.

  The encoder writes the canonical bytes (ModRM mod0/reg/rm6 for
  the two prefetch hints, mod0/reg6/rm0 for the MSW pair); decoding
  inverts encoding on every row. -/

/-- Canonical encoder: one byte string per evaluated row. -/
def sysEvalEncode : SysEvalArt → List Byte
  | .prefetchW => [natByte 15, natByte 13, natByte 14]
  | .prefetchWT1 => [natByte 15, natByte 13, natByte 22]
  | .clts => [natByte 15, natByte 6]
  | .invd => [natByte 15, natByte 8]
  | .wbinvd => [natByte 15, natByte 9]
  | .wbnoinvd => [natByte 243, natByte 15, natByte 9]
  | .sysenter => [natByte 15, natByte 52]
  | .sysexit => [natByte 15, natByte 53]
  | .msw => [natByte 15, natByte 1, natByte 48]

/-- Decoding inverts encoding on every row. -/
theorem sysEvalRoundTrip (r : SysEvalArt) :
    sysEvalDecode (sysEvalEncode r) = some (r, []) := by
  cases r <;> rfl

/-- Encoded lengths match the opcode table. -/
theorem sysEvalEncode_laengen :
    (sysEvalEncode .prefetchW).length = 3 ∧
      (sysEvalEncode .prefetchWT1).length = 3 ∧
      (sysEvalEncode .clts).length = 2 ∧
      (sysEvalEncode .invd).length = 2 ∧
      (sysEvalEncode .wbinvd).length = 2 ∧
      (sysEvalEncode .wbnoinvd).length = 3 ∧
      (sysEvalEncode .sysenter).length = 2 ∧
      (sysEvalEncode .sysexit).length = 2 ∧
      (sysEvalEncode .msw).length = 3 := by
  decide

/-! ## 4. Extended chain over the capstone chain.

  `kapDecodeSysEval` runs the old chain first and the system
  evaluator decoder only where the old chain refuses, so dispatch
  stays disjoint by construction. A maintainer extends the existing
  `kapDecode` of `HwKapsteinDecoder.lean` with a `syseval` arm in
  last position (after the `avx2` arm); the agreement theorems below
  state exactly what that extension must satisfy. -/

/-- Extended decoded row: an old-chain row or a system evaluator row. -/
inductive SysEvalKette where
  | alt : KapDekodiert → SysEvalKette
  | eval : SysEvalArt → SysEvalKette
  deriving DecidableEq, Repr

/-- Extended chain: the old chain first, the evaluator rows only where
    it refuses. No old row is shadowed. -/
def kapDecodeSysEval : List Byte → Option (SysEvalKette × List Byte) :=
  fun bs =>
    match kapDecode bs with
    | some (k, rest) => some (.alt k, rest)
    | none =>
      match sysEvalDecode bs with
      | some (r, rest) => some (.eval r, rest)
      | none => none

/-- Exact agreement: on every byte string the old chain decodes, the
    extended chain takes the old row with the old tail. -/
theorem kapDecodeSysEval_alt (bs : List Byte) (k : KapDekodiert)
    (rest : List Byte) (h : kapDecode bs = some (k, rest)) :
    kapDecodeSysEval bs = some (.alt k, rest) := by
  unfold kapDecodeSysEval
  rw [h]

/-- Where both chains refuse, the extended chain refuses. -/
theorem kapDecodeSysEval_nichts (bs : List Byte)
    (h1 : kapDecode bs = none) (h2 : sysEvalDecode bs = none) :
    kapDecodeSysEval bs = none := by
  unfold kapDecodeSysEval
  rw [h1, h2]

/-- The old chain refuses every new row (no shadowing either way:
    the new rows are taken exactly once, by the new arm). -/
theorem kapDecode_nimmt_clts_nicht :
    kapDecode [natByte 15, natByte 6] = none := by decide
theorem kapDecode_nimmt_invd_nicht :
    kapDecode [natByte 15, natByte 8] = none := by decide
theorem kapDecode_nimmt_wbinvd_nicht :
    kapDecode [natByte 15, natByte 9] = none := by decide
theorem kapDecode_nimmt_wbnoinvd_nicht :
    kapDecode [natByte 243, natByte 15, natByte 9] = none := by decide
theorem kapDecode_nimmt_sysenter_nicht :
    kapDecode [natByte 15, natByte 52] = none := by decide
theorem kapDecode_nimmt_sysexit_nicht :
    kapDecode [natByte 15, natByte 53] = none := by decide
theorem kapDecode_nimmt_prefetchW_nicht :
    kapDecode [natByte 15, natByte 13, natByte 14] = none := by decide
theorem kapDecode_nimmt_prefetchWT1_nicht :
    kapDecode [natByte 15, natByte 13, natByte 22] = none := by decide
theorem kapDecode_nimmt_msw_nicht :
    kapDecode [natByte 15, natByte 1, natByte 48] = none := by decide
theorem kapDecode_nimmt_syseval_leer_nicht :
    kapDecode [] = none := by decide

/-- Every new row decodes through the extended chain. -/
theorem kapSysEval_clts :
    kapDecodeSysEval [natByte 15, natByte 6] =
      some (.eval .clts, []) := by
  simp only [kapDecodeSysEval, kapDecode_nimmt_clts_nicht,
    sysEvalDecode_clts]
theorem kapSysEval_invd :
    kapDecodeSysEval [natByte 15, natByte 8] =
      some (.eval .invd, []) := by
  simp only [kapDecodeSysEval, kapDecode_nimmt_invd_nicht,
    sysEvalDecode_invd]
theorem kapSysEval_wbinvd :
    kapDecodeSysEval [natByte 15, natByte 9] =
      some (.eval .wbinvd, []) := by
  simp only [kapDecodeSysEval, kapDecode_nimmt_wbinvd_nicht,
    sysEvalDecode_wbinvd]
theorem kapSysEval_wbnoinvd :
    kapDecodeSysEval [natByte 243, natByte 15, natByte 9] =
      some (.eval .wbnoinvd, []) := by
  simp only [kapDecodeSysEval, kapDecode_nimmt_wbnoinvd_nicht,
    sysEvalDecode_wbnoinvd]
theorem kapSysEval_sysenter :
    kapDecodeSysEval [natByte 15, natByte 52] =
      some (.eval .sysenter, []) := by
  simp only [kapDecodeSysEval, kapDecode_nimmt_sysenter_nicht,
    sysEvalDecode_sysenter]
theorem kapSysEval_sysexit :
    kapDecodeSysEval [natByte 15, natByte 53] =
      some (.eval .sysexit, []) := by
  simp only [kapDecodeSysEval, kapDecode_nimmt_sysexit_nicht,
    sysEvalDecode_sysexit]
theorem kapSysEval_prefetchW :
    kapDecodeSysEval [natByte 15, natByte 13, natByte 14] =
      some (.eval .prefetchW, []) := by
  simp only [kapDecodeSysEval, kapDecode_nimmt_prefetchW_nicht,
    sysEvalDecode_prefetchW]
theorem kapSysEval_prefetchWT1 :
    kapDecodeSysEval [natByte 15, natByte 13, natByte 22] =
      some (.eval .prefetchWT1, []) := by
  simp only [kapDecodeSysEval, kapDecode_nimmt_prefetchWT1_nicht,
    sysEvalDecode_prefetchWT1]
theorem kapSysEval_msw :
    kapDecodeSysEval [natByte 15, natByte 1, natByte 48] =
      some (.eval .msw, []) := by
  simp only [kapDecodeSysEval, kapDecode_nimmt_msw_nicht,
    sysEvalDecode_msw]
theorem kapSysEval_leer : kapDecodeSysEval [] = none := by
  simp only [kapDecodeSysEval, kapDecode_nimmt_syseval_leer_nicht,
    sysEvalDecode_leer]

/-! ## 5. Evaluator legs on the accepted outcome vocabulary.

  The legs reuse the accepted `SysSnapAusgang` outcome, `kernMitRegRip`
  and `ArchFehler` unchanged (never redefined). Admitted rows advance
  RIP and change nothing else (hint/cache NOPs, no fault, no memory
  or buffer effect); absent prefetch features fault #UD; CPL/vm
  violations fault #GP; the MSR/CR0 rows refuse (their state is
  unmodelled, never admitted silently).

  Silicon assumptions (clone-local Intel SDM snapshot
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
  - S-PREFETCHW: 0F 0D /1 is "merely a hint and does not affect
    program behavior", #UD only with LOCK, in every mode
    (Vol. 2B 4-416/4-417). LOCK shapes refuse at decode, so no leg
    runs under LOCK. Absent enumeration faults #UD (the detection
    section puts the CPUID bit on the execution path).
  - S-PREFETCHWT1: 0F 0D /2 is likewise "merely a hint"
    (Vol. 2D 8-2/8-3), gated on its own enumeration bit.
  - S-CLTS: 0F 06 clears TS in CR0 (Vol. 2A 3-152); #GP(0) outside
    CPL 0 and in virtual-8086 mode. The TS bit itself is NOT tracked
    (no CR0 in the model): the leg is a gated RIP advance, the
    cleared bit a named gap (CUTS).
  - S-INVD/S-WBINVD/S-WBNOINVD: privileged cache writeback/flush
    (Vol. 2A 3-483/3-484, Vol. 2D 6-2/6-4); #GP(0) outside CPL 0 and
    in virtual-8086 mode. Caches are unmodelled, so at the coherent
    memory level the effect is invisible: gated RIP advance, buffers
    untouched. Timing/serialisation stay named assumptions.
  No OS is assumed: the two enumeration bits ride the event as
  explicit caller inputs (environment answers, user logic). -/

/-- Feature inputs: the two prefetch enumeration bits. Absent forms
    are the architectural #UD, never silent NOPs. -/
structure SysEvalEingaben where
  featW : Bool
  featWT1 : Bool
  deriving DecidableEq, Repr

/-- One evaluator event: the row plus its explicit inputs. -/
structure SysEvalEreignis where
  form : SysEvalArt
  eingaben : SysEvalEingaben
  deriving DecidableEq, Repr

/-- Dispatcher: the leg its row names over stored control. -/
def sysEvalSnapSchritt (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEvalEreignis) : SysSnapAusgang :=
  let k := m.kerne c
  match ev.form with
  | .prefetchW =>
    if ev.eingaben.featW then
      .ok (kernMitRegRip k k.register
        (k.rip + BitVec.ofNat 64 (sysEvalLaenge .prefetchW))) st m.mem
    else .fehler .ud
  | .prefetchWT1 =>
    if ev.eingaben.featWT1 then
      .ok (kernMitRegRip k k.register
        (k.rip + BitVec.ofNat 64 (sysEvalLaenge .prefetchWT1))) st m.mem
    else .fehler .ud
  | .clts =>
    if st.steuer.vm then .fehler .gp
    else if st.steuer.cpl = 0 then
      .ok (kernMitRegRip k k.register
        (k.rip + BitVec.ofNat 64 (sysEvalLaenge .clts))) st m.mem
    else .fehler .gp
  | .invd =>
    if st.steuer.vm then .fehler .gp
    else if st.steuer.cpl = 0 then
      .ok (kernMitRegRip k k.register
        (k.rip + BitVec.ofNat 64 (sysEvalLaenge .invd))) st m.mem
    else .fehler .gp
  | .wbinvd =>
    if st.steuer.vm then .fehler .gp
    else if st.steuer.cpl = 0 then
      .ok (kernMitRegRip k k.register
        (k.rip + BitVec.ofNat 64 (sysEvalLaenge .wbinvd))) st m.mem
    else .fehler .gp
  | .wbnoinvd =>
    if st.steuer.vm then .fehler .gp
    else if st.steuer.cpl = 0 then
      .ok (kernMitRegRip k k.register
        (k.rip + BitVec.ofNat 64 (sysEvalLaenge .wbnoinvd))) st m.mem
    else .fehler .gp
  | .sysenter => .verweigert
  | .sysexit => .verweigert
  | .msw => .verweigert

/-- PREFETCHW with its feature bit advances RIP past 3 bytes and
    changes nothing else. -/
theorem sysEval_prefetchW_ok (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (h : ev.eingaben.featW = true) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      sysEvalSnapSchritt m c st
        { ev with form := .prefetchW } = .ok k' st' m.mem ∧
        k'.rip = (m.kerne c).rip + BitVec.ofNat 64 3 ∧ st' = st := by
  refine ⟨kernMitRegRip (m.kerne c) (m.kerne c).register
    ((m.kerne c).rip + BitVec.ofNat 64 (sysEvalLaenge .prefetchW)),
    st, ?_, rfl, rfl⟩
  simp [sysEvalSnapSchritt, h]

/-- PREFETCHW without its feature bit is #UD. -/
theorem sysEval_prefetchW_ud (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (h : ev.eingaben.featW = false) :
    sysEvalSnapSchritt m c st { ev with form := .prefetchW } =
      .fehler .ud := by
  simp [sysEvalSnapSchritt, h]

/-- PREFETCHWT1 with its feature bit advances RIP past 3 bytes. -/
theorem sysEval_prefetchWT1_ok (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (h : ev.eingaben.featWT1 = true) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      sysEvalSnapSchritt m c st
        { ev with form := .prefetchWT1 } = .ok k' st' m.mem ∧
        k'.rip = (m.kerne c).rip + BitVec.ofNat 64 3 ∧ st' = st := by
  refine ⟨kernMitRegRip (m.kerne c) (m.kerne c).register
    ((m.kerne c).rip + BitVec.ofNat 64 (sysEvalLaenge .prefetchWT1)),
    st, ?_, rfl, rfl⟩
  simp [sysEvalSnapSchritt, h]

/-- PREFETCHWT1 without its feature bit is #UD. -/
theorem sysEval_prefetchWT1_ud (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (h : ev.eingaben.featWT1 = false) :
    sysEvalSnapSchritt m c st { ev with form := .prefetchWT1 } =
      .fehler .ud := by
  simp [sysEvalSnapSchritt, h]

/-- CLTS at CPL 0 outside v86 advances RIP past 2 bytes. -/
theorem sysEval_clts_ok (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (hvm : st.steuer.vm = false) (h0 : st.steuer.cpl = 0) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      sysEvalSnapSchritt m c st { ev with form := .clts } =
        .ok k' st' m.mem ∧
        k'.rip = (m.kerne c).rip + BitVec.ofNat 64 2 ∧ st' = st := by
  refine ⟨kernMitRegRip (m.kerne c) (m.kerne c).register
    ((m.kerne c).rip + BitVec.ofNat 64 (sysEvalLaenge .clts)),
    st, ?_, rfl, rfl⟩
  simp [sysEvalSnapSchritt, hvm, h0]

/-- CLTS above CPL 0 is #GP. -/
theorem sysEval_clts_gp (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (hvm : st.steuer.vm = false) (h : ¬ st.steuer.cpl = 0) :
    sysEvalSnapSchritt m c st { ev with form := .clts } =
      .fehler .gp := by
  simp [sysEvalSnapSchritt, hvm, h]

/-- CLTS in virtual-8086 mode is #GP. -/
theorem sysEval_clts_gp_vm (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (hvm : st.steuer.vm = true) :
    sysEvalSnapSchritt m c st { ev with form := .clts } =
      .fehler .gp := by
  simp [sysEvalSnapSchritt, hvm]

/-- INVD at CPL 0 outside v86 advances RIP past 2 bytes. -/
theorem sysEval_invd_ok (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (hvm : st.steuer.vm = false) (h0 : st.steuer.cpl = 0) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      sysEvalSnapSchritt m c st { ev with form := .invd } =
        .ok k' st' m.mem ∧
        k'.rip = (m.kerne c).rip + BitVec.ofNat 64 2 ∧ st' = st := by
  refine ⟨kernMitRegRip (m.kerne c) (m.kerne c).register
    ((m.kerne c).rip + BitVec.ofNat 64 (sysEvalLaenge .invd)),
    st, ?_, rfl, rfl⟩
  simp [sysEvalSnapSchritt, hvm, h0]

/-- INVD above CPL 0 is #GP. -/
theorem sysEval_invd_gp (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (hvm : st.steuer.vm = false) (h : ¬ st.steuer.cpl = 0) :
    sysEvalSnapSchritt m c st { ev with form := .invd } =
      .fehler .gp := by
  simp [sysEvalSnapSchritt, hvm, h]

/-- INVD in virtual-8086 mode is #GP. -/
theorem sysEval_invd_gp_vm (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (hvm : st.steuer.vm = true) :
    sysEvalSnapSchritt m c st { ev with form := .invd } =
      .fehler .gp := by
  simp [sysEvalSnapSchritt, hvm]

/-- WBINVD at CPL 0 outside v86 advances RIP past 2 bytes. -/
theorem sysEval_wbinvd_ok (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (hvm : st.steuer.vm = false) (h0 : st.steuer.cpl = 0) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      sysEvalSnapSchritt m c st { ev with form := .wbinvd } =
        .ok k' st' m.mem ∧
        k'.rip = (m.kerne c).rip + BitVec.ofNat 64 2 ∧ st' = st := by
  refine ⟨kernMitRegRip (m.kerne c) (m.kerne c).register
    ((m.kerne c).rip + BitVec.ofNat 64 (sysEvalLaenge .wbinvd)),
    st, ?_, rfl, rfl⟩
  simp [sysEvalSnapSchritt, hvm, h0]

/-- WBINVD above CPL 0 is #GP. -/
theorem sysEval_wbinvd_gp (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (hvm : st.steuer.vm = false) (h : ¬ st.steuer.cpl = 0) :
    sysEvalSnapSchritt m c st { ev with form := .wbinvd } =
      .fehler .gp := by
  simp [sysEvalSnapSchritt, hvm, h]

/-- WBINVD in virtual-8086 mode is #GP. -/
theorem sysEval_wbinvd_gp_vm (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (hvm : st.steuer.vm = true) :
    sysEvalSnapSchritt m c st { ev with form := .wbinvd } =
      .fehler .gp := by
  simp [sysEvalSnapSchritt, hvm]

/-- WBNOINVD at CPL 0 outside v86 advances RIP past 3 bytes. -/
theorem sysEval_wbnoinvd_ok (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (hvm : st.steuer.vm = false) (h0 : st.steuer.cpl = 0) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      sysEvalSnapSchritt m c st { ev with form := .wbnoinvd } =
        .ok k' st' m.mem ∧
        k'.rip = (m.kerne c).rip + BitVec.ofNat 64 3 ∧ st' = st := by
  refine ⟨kernMitRegRip (m.kerne c) (m.kerne c).register
    ((m.kerne c).rip + BitVec.ofNat 64 (sysEvalLaenge .wbnoinvd)),
    st, ?_, rfl, rfl⟩
  simp [sysEvalSnapSchritt, hvm, h0]

/-- WBNOINVD above CPL 0 is #GP. -/
theorem sysEval_wbnoinvd_gp (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (hvm : st.steuer.vm = false) (h : ¬ st.steuer.cpl = 0) :
    sysEvalSnapSchritt m c st { ev with form := .wbnoinvd } =
      .fehler .gp := by
  simp [sysEvalSnapSchritt, hvm, h]

/-- WBNOINVD in virtual-8086 mode is #GP. -/
theorem sysEval_wbnoinvd_gp_vm (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis)
    (hvm : st.steuer.vm = true) :
    sysEvalSnapSchritt m c st { ev with form := .wbnoinvd } =
      .fehler .gp := by
  simp [sysEvalSnapSchritt, hvm]

/-- The MSR/CR0 rows admit nothing: SYSENTER needs its MSRs. -/
theorem sysEval_sysenter_verweigert (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis) :
    sysEvalSnapSchritt m c st { ev with form := .sysenter } =
      .verweigert := by
  simp [sysEvalSnapSchritt]

/-- SYSEXIT needs its MSRs: refused. -/
theorem sysEval_sysexit_verweigert (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis) :
    sysEvalSnapSchritt m c st { ev with form := .sysexit } =
      .verweigert := by
  simp [sysEvalSnapSchritt]

/-- LMSW/SMSW need CR0: refused. -/
theorem sysEval_msw_verweigert (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis) :
    sysEvalSnapSchritt m c st { ev with form := .msw } =
      .verweigert := by
  simp [sysEvalSnapSchritt]

/-! ## 6. The producer plug on the coherent machine.

  `adapterSysEval` instantiates `HwAdapter` over evaluator events in
  the style of `adapterSystem` (`HwMulDivWidth.lean` shape): snapshot
  control rides the event (the coherent machine stores none); an
  admitted leg installs core data and memory while both profiles and
  every buffer stay untouched by construction; faults and refusals
  admit no successor state. -/

/-- The evaluator plug: one checked evaluator step. -/
def adapterSysEval : HwAdapter (SysSteuer × SysEvalEreignis) :=
  ⟨fun m c p =>
    match sysEvalSnapSchritt m c p.1 p.2 with
    | .ok k' _ mem' =>
      some { m with kerne := fun d =>
        if d = c then k' else m.kerne d, mem := mem' }
    | _ => none⟩

/-- Agreement: the plug succeeds exactly where the snap step
    succeeds, with the successor core data re-embedded. -/
theorem adapterSysEval_ok (m : HwMaschine) (c : Nat)
    (p : SysSteuer × SysEvalEreignis) (k' : HwKern)
    (st' : SysSteuer) (mem' : Speicher)
    (h : sysEvalSnapSchritt m c p.1 p.2 = .ok k' st' mem') :
    adapterSysEval.schritt m c p =
      some { m with kerne := fun d =>
        if d = c then k' else m.kerne d, mem := mem' } := by
  simp [adapterSysEval, h]

/-- A faulting leg admits nothing through the plug. -/
theorem adapterSysEval_fehler (m : HwMaschine) (c : Nat)
    (p : SysSteuer × SysEvalEreignis) (f : ArchFehler)
    (h : sysEvalSnapSchritt m c p.1 p.2 = .fehler f) :
    adapterSysEval.schritt m c p = none := by
  simp [adapterSysEval, h]

/-- A refused leg admits nothing through the plug. -/
theorem adapterSysEval_verweigert (m : HwMaschine) (c : Nat)
    (p : SysSteuer × SysEvalEreignis)
    (h : sysEvalSnapSchritt m c p.1 p.2 = .verweigert) :
    adapterSysEval.schritt m c p = none := by
  simp [adapterSysEval, h]

/-- Every admitted plug step preserves well-formedness: only core
    data and memory move, profiles are untouched. -/
theorem adapterSysEval_wf (m : HwMaschine) (c : Nat)
    (p : SysSteuer × SysEvalEreignis) (m' : HwMaschine)
    (hwf : HwWf m)
    (h : adapterSysEval.schritt m c p = some m') :
    HwWf m' := by
  unfold adapterSysEval at h
  cases hs : sysEvalSnapSchritt m c p.1 p.2 with
  | ok k' st' mem' =>
    simp [hs] at h
    cases h
    exact hwf
  | fehler f => simp [hs] at h
  | verweigert => simp [hs] at h

/-- Every admitted plug step keeps every buffer: no evaluator leg
    drains the TSO store buffer (the S-SERIAL analogue for this
    family: prefetch hints are explicitly unordered with fences and
    locks, cache flushes retire without touching the store path). -/
theorem adapterSysEval_puffer (m : HwMaschine) (c d : Nat)
    (p : SysSteuer × SysEvalEreignis) (m' : HwMaschine)
    (h : adapterSysEval.schritt m c p = some m') :
    m'.puffer d = m.puffer d := by
  unfold adapterSysEval at h
  cases hs : sysEvalSnapSchritt m c p.1 p.2 with
  | ok k' st' mem' =>
    simp [hs] at h
    cases h
    rfl
  | fehler f => simp [hs] at h
  | verweigert => simp [hs] at h

/-- SYSENTER admits no plug step. -/
theorem adapterSysEval_sysenter (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis) :
    adapterSysEval.schritt m c (st, { ev with form := .sysenter }) =
      none :=
  adapterSysEval_verweigert _ _ _
    (sysEval_sysenter_verweigert _ _ _ _)

/-- SYSEXIT admits no plug step. -/
theorem adapterSysEval_sysexit (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis) :
    adapterSysEval.schritt m c (st, { ev with form := .sysexit }) =
      none :=
  adapterSysEval_verweigert _ _ _
    (sysEval_sysexit_verweigert _ _ _ _)

/-- LMSW/SMSW admit no plug step. -/
theorem adapterSysEval_msw (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEvalEreignis) :
    adapterSysEval.schritt m c (st, { ev with form := .msw }) =
      none :=
  adapterSysEval_verweigert _ _ _
    (sysEval_msw_verweigert _ _ _ _)

/-! ## 7. Execution: decoded bytes reach the coherent machine.

  Core 0 runs PREFETCHW and core 1 runs WBINVD on the accepted
  `sysWitStart` machine (CPL-0 control, accepted IDT/TSS/stack
  memory, empty buffers); CPL-3 CLTS and bit-less PREFETCHW refuse
  beside the run; SYSENTER admits nothing at either level. The TSO
  stage issues a buffered store the owner forwards but the foreign
  core does not see until the drain -- the drain changes ACTUAL
  shared memory from 0 to 42. -/

/-- Witness inputs: both prefetch enumeration bits present. -/
def sysEvalWitEingaben : SysEvalEingaben := ⟨true, true⟩

/-- Core RIP out of an evaluator outcome. -/
def evalRipOut : SysSnapAusgang → Option Adresse
  | .ok k' _ _ => some k'.rip
  | _ => none

/-- Fault class out of an evaluator outcome. -/
def evalKlasseOut : SysSnapAusgang → Option ArchFehler
  | .fehler f => some f
  | _ => none

/-- Shared-memory byte out of an evaluator outcome. -/
def evalMemOut (o : SysSnapAusgang) (a : Adresse) : Option Byte :=
  match o with
  | .ok _ _ mem' => some (mem'.bytes a)
  | _ => none

/-- Core-0 run: PREFETCHW with its feature bit. -/
def sysEvalWitO_prefetchW :=
  sysEvalSnapSchritt sysWitStart.hw 0 sysWitSteuer
    ⟨.prefetchW, sysEvalWitEingaben⟩

/-- Core-1 run: WBINVD at CPL 0. -/
def sysEvalWitO_wbinvd :=
  sysEvalSnapSchritt sysWitStart.hw 1 sysWitSteuer
    ⟨.wbinvd, sysEvalWitEingaben⟩

/-- CLTS at CPL 3 (high-privilege control). -/
def sysEvalWitO_cltsHoch :=
  sysEvalSnapSchritt sysWitHochM.hw 0 (sysWitHochM.sys 0)
    ⟨.clts, sysEvalWitEingaben⟩

/-- PREFETCHW without its feature bit. -/
def sysEvalWitO_prefetchWohne :=
  sysEvalSnapSchritt sysWitStart.hw 0 sysWitSteuer
    ⟨.prefetchW, { sysEvalWitEingaben with featW := false }⟩

/-- SYSENTER at the snap level. -/
def sysEvalWitO_sysenter :=
  sysEvalSnapSchritt sysWitStart.hw 0 sysWitSteuer
    ⟨.sysenter, sysEvalWitEingaben⟩

/-- PREFETCHW advances core-0 RIP past 3 bytes. -/
theorem sysEvalWit_prefetchW_rip :
    evalRipOut sysEvalWitO_prefetchW =
      some (BitVec.ofNat 64 0x1003) := by
  decide

/-- WBINVD advances core-1 RIP past 2 bytes. -/
theorem sysEvalWit_wbinvd_rip :
    evalRipOut sysEvalWitO_wbinvd =
      some (BitVec.ofNat 64 0x1002) := by
  decide

/-- The hint leaves shared memory alone. -/
theorem sysEvalWit_prefetchW_mem :
    evalMemOut sysEvalWitO_prefetchW
      (BitVec.ofNat 64 16336) = some (BitVec.ofNat 8 0) := by
  decide

/-- CLTS at CPL 3 is #GP. -/
theorem sysEvalWit_clts_gp :
    evalKlasseOut sysEvalWitO_cltsHoch = some .gp := by
  decide

/-- PREFETCHW without its feature bit is #UD. -/
theorem sysEvalWit_prefetchW_ud :
    evalKlasseOut sysEvalWitO_prefetchWohne = some .ud := by
  decide

/-- SYSENTER is refused at the snap level. -/
theorem sysEvalWit_sysenter :
    sysEvalWitO_sysenter = .verweigert :=
  sysEval_sysenter_verweigert sysWitStart.hw 0 sysWitSteuer
    ⟨.sysenter, sysEvalWitEingaben⟩

/-- Witness data cell on the accepted stack page. -/
def sysEvalWitAdr : Adresse := BitVec.ofNat 64 16336

/-- Witness TSO start: accepted memory, empty buffers. -/
def sysEvalWitTso0 : TSOZustand := tsoAnsicht sysWitStart.hw

/-- Core 0 issues byte 42 at the data cell. -/
def sysEvalWitTso1 : Option TSOZustand :=
  issueByte sysEvalWitTso0 0 sysEvalWitAdr (BitVec.ofNat 8 42)

/-- Core 0 observes its own byte (forwarding). -/
def sysEvalWitEigen : Option (Option Byte) :=
  match sysEvalWitTso1 with
  | some s => some (loadByte s 0 sysEvalWitAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def sysEvalWitFremd : Option (Option Byte) :=
  match sysEvalWitTso1 with
  | some s => some (loadByte s 1 sysEvalWitAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def sysEvalWitTso2 : Option TSOZustand :=
  match sysEvalWitTso1 with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def sysEvalWitNachFlush : Option (Option Byte) :=
  match sysEvalWitTso2 with
  | some s => some (some (s.mem.bytes sysEvalWitAdr))
  | none => none

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem sysEvalWit_weiterleitung :
    sysEvalWitEigen = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem sysEvalWit_fremd_alt :
    sysEvalWitFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem sysEvalWit_spuelung_aendert_speicher :
    sysEvalWitNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- Joint witness: every new row decodes through the extended chain,
    PREFETCHW advances core 0 without touching memory, WBINVD
    advances core 1, CPL-3 CLTS is #GP, bit-less PREFETCHW is #UD,
    SYSENTER is refused at both levels, and a buffered store is
    owner-forwarded then drained 0-to-42 into actual shared memory.
    Non-degenerate: the drain changes actual shared memory. -/
theorem sysEval_zeuge :
    kapDecodeSysEval [natByte 15, natByte 13, natByte 14] =
      some (.eval .prefetchW, []) ∧
      kapDecodeSysEval [natByte 15, natByte 13, natByte 22] =
        some (.eval .prefetchWT1, []) ∧
      kapDecodeSysEval [natByte 15, natByte 6] =
        some (.eval .clts, []) ∧
      kapDecodeSysEval [natByte 15, natByte 8] =
        some (.eval .invd, []) ∧
      kapDecodeSysEval [natByte 15, natByte 9] =
        some (.eval .wbinvd, []) ∧
      kapDecodeSysEval [natByte 243, natByte 15, natByte 9] =
        some (.eval .wbnoinvd, []) ∧
      kapDecodeSysEval [natByte 15, natByte 52] =
        some (.eval .sysenter, []) ∧
      kapDecodeSysEval [natByte 15, natByte 53] =
        some (.eval .sysexit, []) ∧
      kapDecodeSysEval [natByte 15, natByte 1, natByte 48] =
        some (.eval .msw, []) ∧
      evalRipOut sysEvalWitO_prefetchW =
        some (BitVec.ofNat 64 0x1003) ∧
      evalRipOut sysEvalWitO_wbinvd =
        some (BitVec.ofNat 64 0x1002) ∧
      evalMemOut sysEvalWitO_prefetchW
        (BitVec.ofNat 64 16336) = some (BitVec.ofNat 8 0) ∧
      evalKlasseOut sysEvalWitO_cltsHoch = some .gp ∧
      evalKlasseOut sysEvalWitO_prefetchWohne = some .ud ∧
      sysEvalWitO_sysenter = .verweigert ∧
      adapterSysEval.schritt sysWitStart.hw 0
        (sysWitSteuer, ⟨.sysenter, sysEvalWitEingaben⟩) = none ∧
      sysEvalWitEigen = some (some (BitVec.ofNat 8 42)) ∧
      sysEvalWitFremd = some (some (BitVec.ofNat 8 0)) ∧
      sysEvalWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      SysWf sysWitStart := by
  exact ⟨kapSysEval_prefetchW, kapSysEval_prefetchWT1, kapSysEval_clts,
    kapSysEval_invd, kapSysEval_wbinvd, kapSysEval_wbnoinvd,
    kapSysEval_sysenter, kapSysEval_sysexit, kapSysEval_msw,
    sysEvalWit_prefetchW_rip, sysEvalWit_wbinvd_rip,
    sysEvalWit_prefetchW_mem, sysEvalWit_clts_gp,
    sysEvalWit_prefetchW_ud, sysEvalWit_sysenter,
    adapterSysEval_sysenter sysWitStart.hw 0 sysWitSteuer
      ⟨.sysenter, sysEvalWitEingaben⟩, sysEvalWit_weiterleitung,
    sysEvalWit_fremd_alt, sysEvalWit_spuelung_aendert_speicher,
    sysWitStart_wf⟩

/- CUTS:
   Proved here: byte decode rows for the nine evaluated system
   shapes (five admitted hint/cache NOPs plus four decoded MSR/CR0
   refusals, exact-length shapes, register forms and truncated
   inputs refused, neighbour RDTSCP/XGETBV/CLFLUSH rows never
   shadowed), the canonical encoder with round trip and exact
   lengths, the extended chain `kapDecodeSysEval` with exact
   agreement on every byte string the old chain decodes and
   one-taking of every new row (old-chain refusal pinned per row),
   evaluator legs on the accepted outcome vocabulary reusing
   `SysSnapAusgang`, `kernMitRegRip` and `ArchFehler` unchanged
   (admitted legs advance RIP only; absent prefetch features are
   #UD; CPL/vm violations are #GP; MSR/CR0 rows refuse), the
   `HwAdapter` plug with exact snap agreement, buffer preservation
   and well-formedness preservation, plug-level refusal of the
   MSR/CR0 rows, and a reached two-core run (PREFETCHW on core 0,
   WBINVD on core 1, memory provably unchanged by the hint)
   beside CPL/feature refusals and a TSO issue/forward/drain that
   changes ACTUAL shared memory 0-to-42 with owner-only forwarding.
   NOT proved here, and not claimed:
   - No hardware correspondence beyond self-consistency: the opcode
     map and privilege/fault classes are transcribed from the
     clone-local Intel snapshot
     `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
     (provenance, never a proof). No AMD manual is in the clone, so
     no AMD fact is claimed; the rows are defined identically on
     both vendors (common architecture, enumeration bits ride the
     event as caller inputs).
   - PREFETCHh already has its accepted evaluator (`HwMemTypesWC`
     `decodePrefetch1287`/`wcAdapter_prefetch_nop`, never redefined
     here); the `SysExtra` nine of `SystemDecode` (INT3/INT1 debug
     delivery, CLD/STD over the unmodelled DF bit, RDMSR/WRMSR/
     RDPMC/RDTSCP/XGETBV over unmodelled MSR/counter/XCR0 state)
     stay with their own lanes.
   - SIB/displacement address tails refuse (exact-length shapes
     only, the accepted prefetch precedent); the formed effective
     address is not computed. The prefetch memory operand is never
     faulted (hint semantics); permission/canonical checks on it
     stay OPEN.
   - CLTS clears no tracked bit (no CR0 in the model): the leg is a
     gated RIP advance and the cleared TS bit is a named gap.
     INVD/WBINVD/WBNOINVD retire with no modelled cache effect;
     writeback-to-memory identity, serialisation, timing, fence
     interaction beyond the proved buffer equations, the INVD
     post-BIOS platform refusal and WBNOINVD enumeration stay
     named assumptions, never theorems.
   - SYSENTER/SYSEXIT (SEP MSRs) and LMSW/SMSW (CR0) decode and are
     refused; their semantics stay OPEN. SMSW register forms
     (mod=3) are not decoded (OPEN). Flags the architecture calls
     undefined stay FREE: no leg constrains any flag.
   - The bridge to W/GX ordering is OPEN (the proved buffer
     equations are the machine side only).
   - Maintainer note: to wire these rows into the built chain, add a
     `syseval` arm for `sysEvalDecode` in last position of
     `kapDecode` (`HwKapsteinDecoder.lean`, after the `avx2` arm);
     the `kapSysEval_*` theorems state the required behaviour. The
     merge gate's `lean-layout --apply` moves this module to
     `Befehle/System/` (rule `^System\w+$`) and rewrites the import.
-/

#print axioms sysEvalRoundTrip
#print axioms kapDecodeSysEval_alt
#print axioms kapDecodeSysEval_nichts
#print axioms sysEval_prefetchW_ok
#print axioms sysEval_clts_ok
#print axioms sysEval_sysenter_verweigert
#print axioms adapterSysEval_ok
#print axioms adapterSysEval_wf
#print axioms adapterSysEval_puffer
#print axioms sysEval_zeuge
#print axioms sysEvalLaenge_pins

end Gabbro.Grammatik.X86
