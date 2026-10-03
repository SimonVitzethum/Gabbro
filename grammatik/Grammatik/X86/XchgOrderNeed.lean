/-
  File:      Grammatik/X86/XchgOrderNeed.lean
  Subject:   XCHG ordering need: barrier-carrying memory exchange exactly
             where source order needs it, refusal of bare-XCHG-as-optimisation.

  Lane 779. Manual provenance (clone-local snapshot `.tmp/HARDWARE-REFERENCES/`):
  Intel SDM 325462-093US Sep 2026, XCHG Vol. 2D 6-31/6-32 (opcodes REX.W+87 /r
  and REX.W+90+rd, Operation TEMP:=DEST/DEST:=SRC/SRC:=TEMP, Flags None,
  memory operand asserts LOCK# automatically regardless of LOCK prefix/IOPL,
  90H XCHG (E)AX,(E)AX is NOP alias), LOCK prefix Vol. 2A 3-565/3-566
  (XCHG always asserts LOCK#), Bus locking Vol. 3A 11.1.2.2 (LOCK assumed
  for XCHG), memory ordering Vol. 3A 11.2.3.8/11.2.3.9 (total order of locked
  instructions, no reordering of loads/stores with earlier/later locked
  instructions; XCHG examples 11-8/11-9/11-10), single-access rule
  (aligned quadword appears as single access; any locked instruction is an
  indivisible load/store sequence regardless of alignment). Reuses canonical
  `Zustand`-free TSO target state (`TSOZustand`), `read64`/`write64`,
  `Fuss`, `dispWort`, `rexByte`/`modrmMem`/`modrmReg`, `leBytes32`.
  No second evaluator for older forms, no source/checker/goal change.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- XCHG 64-bit word forms: memory exchange (ordering-carrying) and
    register-only exchange (no memory order, never an optimisation). -/
inductive XchgForm where
  | mem (base src : Register) (disp : BitVec 32)
  | reg (dst src : Register)
  deriving DecidableEq, Repr

/-- Ordering need: exactly the memory form carries source order.
    The register-only form needs no order (pure register rename). -/
def brauchtOrdnung : XchgForm → Bool
  | .mem _ _ _ => true
  | .reg _ _ => false

/-- Admission as an ordering operation: only the memory form.
    A bare register XCHG is refused as an optimisation target. -/
def xchgZulaessig : XchgForm → Bool
  | .mem _ _ _ => true
  | .reg _ _ => false

/-- XCHG machine state: register file plus flags over the canonical
    TSO target state. Memory lives only in `tso.mem`. -/
structure XchgZustand where
  reg : Register → Wort
  flags : Flags
  tso : TSOZustand

/-- Effective address of the memory form from a register file. -/
def xchgAddr (r : Register → Wort) (base : Register)
    (disp : BitVec 32) : Adresse :=
  r base + dispWort disp

/-! ## 1. Barrier-carrying atomic exchange over canonical TSO memory.

    The memory form bypasses the acting core's store buffer and swaps
    atomically in canonical memory, exactly when that core's buffer is
    empty (the locked-instruction barrier of Vol. 3A 11.2.3.9: no load
    or store is reordered with an earlier/later locked instruction;
    XCHG with a memory operand is implicitly locked, Vol. 2D 6-31).
    Flags are untouched (XCHG entry: Flags Affected None). Any other
    case is `none`, never a silent tear. The register form swaps two
    registers purely and carries no barrier. -/

/-- One XCHG step. Memory form: atomic swap under an empty own buffer;
    register form: pure register swap. -/
def xchgSchritt (f : XchgForm) (c : Nat) (s : XchgZustand) :
    Option XchgZustand :=
  match f with
  | .mem base src d =>
    if (s.tso.puffer c).isEmpty then
      let a := xchgAddr s.reg base d
      match read64 s.tso.mem a with
      | none => none
      | some alt =>
        match write64 s.tso.mem a (s.reg src) with
        | none => none
        | some m' =>
          some ⟨regSet s.reg src alt, s.flags, ⟨m', s.tso.puffer⟩⟩
    else none
  | .reg dst src =>
    some ⟨regSet (regSet s.reg dst (s.reg src)) src (s.reg dst), s.flags,
      s.tso⟩

/-! ## 2. Canonical byte codec (REX.W + 87 /r, Vol. 2D 6-31).

    Memory form: REX.W, opcode 0x87, ModRM mod=2 base-plus-disp32
    (SIB 0x24 exactly when the base needs it, mirroring the pilot).
    Register form: REX.W, 0x87, ModRM mod=3. The REX.W+90+rd alias
    row and the explicit LOCK-prefixed (F0) row are NOT claimed here
    and refuse with `none` (see CUTS). -/

/-- Canonical encoding of one XCHG word form. -/
def encodeXchg : XchgForm → List Byte
  | .mem base src d =>
    let head := [rexByte (regHigh src) (regHigh base), natByte 135,
      modrmMem (regLow src) (regLow base)]
    if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
    else head ++ leBytes32 d
  | .reg dst src =>
    [rexByte (regHigh src) (regHigh dst), natByte 135,
      modrmReg (regLow src) (regLow dst)]

/-- Consumed length of one XCHG form. -/
def xchgLen : XchgForm → Nat
  | .mem base _ _ => if regLow base == 4 then 8 else 7
  | .reg _ _ => 3

/-- Accepted REX.W prefix bits for the XCHG rows: W=1, X=0, i.e.
    0x48/0x49/0x4C/0x4D (canonical subset, mirroring the pilot). -/
def rexXchgBits : Byte → Option (Nat × Nat)
  | b =>
    if byteNat b == 72 then some (0, 0)
    else if byteNat b == 73 then some (0, 1)
    else if byteNat b == 76 then some (1, 0)
    else if byteNat b == 77 then some (1, 1)
    else none

/-- Byte decoder for the two canonical XCHG rows. LOCK-prefixed (F0),
    90+rd alias and truncated rows refuse with `none`. -/
def decodeXchg : List Byte → Option (XchgForm × List Byte)
  | r :: o :: m :: rest =>
    match rexXchgBits r with
    | none => none
    | some (rh, bh) =>
      if byteNat o != 135 then none
      else if byteNat m / 64 == 2 then
        match codeReg (rh * 8 + (byteNat m / 8) % 8),
            codeReg (bh * 8 + byteNat m % 8) with
        | some src, some base =>
          if byteNat m % 8 == 4 then
            match rest with
            | sib :: r0 =>
              if byteNat sib != 36 then none
              else match parseLe32 r0 with
                | none => none
                | some (d, rest') => some (.mem base src d, rest')
            | [] => none
          else match parseLe32 rest with
            | none => none
            | some (d, rest') => some (.mem base src d, rest')
        | _, _ => none
      else if byteNat m / 64 == 3 then
        match codeReg (rh * 8 + (byteNat m / 8) % 8),
            codeReg (bh * 8 + byteNat m % 8) with
        | some src, some dst => some (.reg dst src, rest)
        | _, _ => none
      else none
  | _ => none

/-! ## 3. Codec round trip (checked data, not hardware fidelity).

    A round trip alone proves no silicon correspondence; §5 connects
    the admitted bytes to the barrier-carrying step. -/

/-- The REX classifier inverts the canonical REX byte on both bits. -/
theorem rexXchgBits_rexByte (rh bh : Nat) (h1 : rh < 2) (h2 : bh < 2) :
    rexXchgBits (rexByte rh bh) = some (rh, bh) := by
  cases rh with
  | zero =>
    cases bh with
    | zero => decide
    | succ b =>
      cases b with
      | zero => decide
      | succ _ => omega
  | succ n =>
    cases n with
    | zero =>
      cases bh with
      | zero => decide
      | succ b =>
        cases b with
        | zero => decide
        | succ _ => omega
    | succ _ => omega

/-- Opcode byte 0x87 survives the byte round trip. -/
theorem xchg_opcode_ok : byteNat (natByte 135) = 135 := by decide

/-- The register-direct ModRM byte decodes as mod=3 with both fields. -/
theorem xchg_modrmReg_felder (rl rm : Nat) (h1 : rl < 8) (h2 : rm < 8) :
    byteNat (modrmReg rl rm) / 64 = 3 ∧
    (byteNat (modrmReg rl rm) / 8) % 8 = rl ∧
    byteNat (modrmReg rl rm) % 8 = rm := by
  unfold modrmReg
  rw [byteNat_natByte_any]
  refine ⟨by omega, by omega, by omega⟩

/-- The memory ModRM byte decodes as mod=2 with both fields. -/
theorem xchg_modrmMem_felder (rl rm : Nat) (h1 : rl < 8) (h2 : rm < 8) :
    byteNat (modrmMem rl rm) / 64 = 2 ∧
    (byteNat (modrmMem rl rm) / 8) % 8 = rl ∧
    byteNat (modrmMem rl rm) % 8 = rm := by
  unfold modrmMem
  rw [byteNat_natByte_any]
  refine ⟨by omega, by omega, by omega⟩

/-- Round trip for the register row: decode inverts encode. -/
theorem roundtrip_xchg_reg (dst src : Register) (suffix : List Byte) :
    decodeXchg (encodeXchg (.reg dst src) ++ suffix) =
      some ((.reg dst src), suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for the memory row, both SIB and non-SIB shapes. -/
theorem roundtrip_xchg_mem (base src : Register) (d : BitVec 32)
    (suffix : List Byte) :
    decodeXchg (encodeXchg (.mem base src d) ++ suffix) =
      some ((.mem base src d), suffix) := by
  cases base <;> cases src <;>
    simp [encodeXchg, decodeXchg, codeReg, regCode, regHigh, regLow,
      rexByte, rexXchgBits, modrmMem, parseLe32_leBytes32]

/-! ## 4. Barrier equations: swap, flags, fence readiness.

    Vol. 2D 6-31/6-32 (Operation is the swap, Flags Affected None,
    memory operand locks automatically) and Vol. 3A 11.2.3.9 (no load
    or store is reordered with a locked instruction). -/

/-- A successful memory exchange installs the swap: canonical memory
    holds the register value, the register holds the old word, flags
    are untouched, the own buffer stays empty (fence-ready), the form
    carries order, and the new word reads back. Every premise is used:
    `hbuf` for the barrier, `hrd` for the old value, `hles` for the
    read-back, `hwr` for the installed word, `hstep` for the step. -/
theorem XchgOrderNeed_verbindung (base src : Register) (d : BitVec 32)
    (c : Nat) (s s' : XchgZustand) (alt : Wort) (m' : Speicher)
    (hbuf : s.tso.puffer c = [])
    (hrd : read64 s.tso.mem (xchgAddr s.reg base d) = some alt)
    (hles : lesbar8 s.tso.mem (xchgAddr s.reg base d) = true)
    (hwr : write64 s.tso.mem (xchgAddr s.reg base d) (s.reg src) = some m')
    (hstep : xchgSchritt (.mem base src d) c s = some s') :
    s'.tso.mem = m' ∧ s'.reg src = alt ∧ s'.flags = s.flags ∧
    s'.tso.puffer c = [] ∧ zaunBereit s'.tso c = true ∧
    brauchtOrdnung (.mem base src d) = true ∧
    xchgZulaessig (.mem base src d) = true ∧
    read64 s'.tso.mem (xchgAddr s.reg base d) = some (s.reg src) := by
  have hempty : (s.tso.puffer c).isEmpty = true := by rw [hbuf]; rfl
  simp only [xchgSchritt, hempty, hrd, hwr] at hstep
  cases hstep
  refine ⟨rfl, regSet_gleich _ _ _, rfl, hbuf, ?_, rfl, rfl, ?_⟩
  · rw [zaunBereit_iff_leer]
    exact hbuf
  · exact read64_nach_write64 _ _ _ _ hwr hles

/-- The memory form refuses under a pending own store: the barrier is
    a gate, never a silent reorder. -/
theorem xchg_mem_verweigert_bei_puffer (base src : Register)
    (d : BitVec 32) (c : Nat) (s : XchgZustand)
    (h : s.tso.puffer c ≠ []) :
    xchgSchritt (.mem base src d) c s = none := by
  have hempty : (s.tso.puffer c).isEmpty = false := by
    cases hbuf : s.tso.puffer c with
    | nil => exact absurd hbuf h
    | cons _ _ => rfl
  simp [xchgSchritt, hempty]

/-- Ordering admission: exactly the memory form carries source order;
    the bare register form is refused as an optimisation target. -/
theorem xchg_mem_bedarf (base src : Register) (d : BitVec 32) :
    brauchtOrdnung (.mem base src d) = true ∧
    xchgZulaessig (.mem base src d) = true :=
  ⟨rfl, rfl⟩

/-- Bare-XCHG refusal: the register form needs no order and is never
    admitted as an ordering operation. -/
theorem xchg_reg_kein_bedarf (dst src : Register) :
    brauchtOrdnung (.reg dst src) = false ∧
    xchgZulaessig (.reg dst src) = false :=
  ⟨rfl, rfl⟩

/-- Bare XCHG gives no barrier: the register step succeeds even with a
    full own buffer, so it must never stand where order is needed. -/
theorem xchg_reg_ohne_schranke (dst src : Register) (c : Nat)
    (s : XchgZustand) :
    xchgSchritt (.reg dst src) c s =
      some ⟨regSet (regSet s.reg dst (s.reg src)) src (s.reg dst),
        s.flags, s.tso⟩ :=
  rfl

/-! ## 5. Footprint, permissions and neighbour refusals.

    The memory form touches exactly the eight footprint bytes
    (`Fuss`); the register form touches no memory. Failed permissions
    refuse with `none` (page-fault shape, never an invented halt).
    LOCK-prefixed, 90+rd-alias and truncated neighbours refuse. -/

/-- Realised footprint: the eight word bytes for memory, none for
    registers. -/
def xchgFuss (f : XchgForm) (r : Register → Wort) : List Adresse :=
  match f with
  | .mem base _ d => Fuss (xchgAddr r base d)
  | .reg _ _ => []

/-- The memory footprint is the eight word bytes. -/
theorem xchg_mem_fuss (base src : Register) (d : BitVec 32)
    (r : Register → Wort) :
    xchgFuss (.mem base src d) r = Fuss (xchgAddr r base d) :=
  rfl

/-- The register form has an empty footprint. -/
theorem xchg_reg_fuss_leer (dst src : Register) (r : Register → Wort) :
    xchgFuss (.reg dst src) r = [] :=
  rfl

/-- Without read permission the memory step refuses. -/
theorem xchg_mem_verweigert_ohne_leserecht (base src : Register)
    (d : BitVec 32) (c : Nat) (s : XchgZustand)
    (hbuf : (s.tso.puffer c).isEmpty = true)
    (h : read64 s.tso.mem (xchgAddr s.reg base d) = none) :
    xchgSchritt (.mem base src d) c s = none := by
  simp [xchgSchritt, hbuf, h]

/-- Without write permission the memory step refuses (the failed
    comparison still needs the write cycle, Vol. 2D 6-31/6-32 shape:
    no locked read without a locked write). -/
theorem xchg_mem_verweigert_ohne_schreibrecht (base src : Register)
    (d : BitVec 32) (c : Nat) (s : XchgZustand) (alt : Wort)
    (hbuf : (s.tso.puffer c).isEmpty = true)
    (hrd : read64 s.tso.mem (xchgAddr s.reg base d) = some alt)
    (hwr : write64 s.tso.mem (xchgAddr s.reg base d) (s.reg src) = none) :
    xchgSchritt (.mem base src d) c s = none := by
  simp [xchgSchritt, hbuf, hrd, hwr]

/-- Every XCHG encoding fits the 15-byte instruction cap. -/
theorem encodeXchg_len (f : XchgForm) :
    1 ≤ (encodeXchg f).length ∧ (encodeXchg f).length ≤ 15 := by
  cases f with
  | reg _ _ => exact show 1 ≤ 3 ∧ 3 ≤ 15 from ⟨by decide, by decide⟩
  | mem base src d =>
    cases base <;>
      (first
        | exact show 1 ≤ 7 ∧ 7 ≤ 15 from ⟨by decide, by decide⟩
        | exact show 1 ≤ 8 ∧ 8 ≤ 15 from ⟨by decide, by decide⟩)

/-- LOCK-prefixed neighbour refuses (explicit LOCK row stays open). -/
theorem decodeXchg_lock_verweigert :
    decodeXchg [natByte 240, natByte 72, natByte 135] = none :=
  rfl

/-- REX.W+90+rd alias neighbour refuses (alias row stays open). -/
theorem decodeXchg_alias90_verweigert :
    decodeXchg [natByte 72, natByte 144, natByte 195] = none :=
  rfl

/-- Truncated prefix refuses. -/
theorem decodeXchg_abgeschnitten_verweigert :
    decodeXchg [natByte 72, natByte 135] = none :=
  rfl

/-! ## 6. Joint witness: reached, memory-changing, barrier-carrying.

    Core 1 issues byte 5 at address 100 and flushes it (a reached TSO
    run with a memory-changing step); core 0 then swaps word 0 at
    address 8192 (`rbp` plus disp 0) with register `rcx` holding 7.
    Canonical memory observably changes at 8192 (0 becomes 7) while
    flags and the foreign flushed byte are untouched. -/

/-- Witness register file: `rbp` holds 8192, `rcx` holds 7. -/
def xwReg : Register → Wort
  | .rbp => BitVec.ofNat 64 8192
  | .rcx => BitVec.ofNat 64 7
  | _ => BitVec.ofNat 64 0

/-- Witness flags: all clear, auxiliary undefined. -/
def xwFlags : Flags := ⟨false, false, none, false, false, false⟩

/-- Witness TSO start: zeroed fully-permissive memory, buffers empty. -/
def xwTso0 : TSOZustand := ⟨zeugenSpeicher, fun _ => []⟩

/-- After core 1 issues byte 5 at address 100. -/
def xwTso1 : TSOZustand :=
  ⟨zeugenSpeicher,
    pufferSetze xwTso0.puffer 1 [⟨(100 : Adresse), (5 : Byte)⟩]⟩

/-- After core 1 flushes that byte into canonical memory. -/
def xwTso2 : TSOZustand :=
  ⟨{ zeugenSpeicher with
      bytes := fun x => if x = (100 : Adresse) then (5 : Byte)
        else zeugenSpeicher.bytes x },
    pufferSetze xwTso1.puffer 1 []⟩

/-- Witness exchange address: `rbp` plus disp 0. -/
def xchgA : Adresse := xchgAddr xwReg .rbp (BitVec.ofNat 32 0)

/-- Witness post-swap memory: the register value installed at `xchgA`. -/
def xwM : Speicher :=
  { xwTso2.mem with bytes := writeBytes xwTso2.mem xchgA (xwReg .rcx) }

/-- Witness pre-state over the reached TSO memory. -/
def xwS : XchgZustand := ⟨xwReg, xwFlags, xwTso2⟩

/-- Witness post-state: swapped register, installed word, same flags. -/
def xwS' : XchgZustand :=
  ⟨regSet xwReg .rcx (BitVec.ofNat 64 0), xwFlags, ⟨xwM, xwTso2.puffer⟩⟩

/-- The witness issue computes as claimed. -/
theorem xw_issue :
    issueByte xwTso0 1 (100 : Adresse) (5 : Byte) = some xwTso1 :=
  rfl

/-- The witness flush computes as claimed. -/
theorem xw_flush : flushKern xwTso1 1 = some xwTso2 :=
  rfl

/-- The reached TSO run changes canonical memory (byte 100). -/
theorem xw_tso_aendert : xwTso0.mem.bytes 100 ≠ xwTso2.mem.bytes 100 := by
  decide

/-- The witness TSO run is reached through issue and flush. -/
theorem xw_erreichbar : TSOErreichbar xwTso0 xwTso2 :=
  .schritt (.schritt .start (.issue _ _ _ _ _ xw_issue))
    (.flush _ _ _ xw_flush)

/-- The witness barrier premise: core 0's buffer is empty. -/
theorem xw_hbuf : xwS.tso.puffer 0 = [] :=
  rfl

/-- The witness read premise: the word at `xchgA` is zero. -/
theorem xw_hrd :
    read64 xwS.tso.mem (xchgAddr xwS.reg .rbp (BitVec.ofNat 32 0)) =
      some (BitVec.ofNat 64 0) :=
  rfl

/-- The witness readability premise. -/
theorem xw_hles :
    lesbar8 xwS.tso.mem (xchgAddr xwS.reg .rbp (BitVec.ofNat 32 0)) = true :=
  rfl

/-- The witness install premise: `rcx` (7) installs at `xchgA`. -/
theorem xw_hwr :
    write64 xwS.tso.mem (xchgAddr xwS.reg .rbp (BitVec.ofNat 32 0))
      (xwS.reg .rcx) = some xwM :=
  rfl

/-- FETCHED SWAP: the witness exchange step computes as claimed. -/
theorem xw_schritt :
    xchgSchritt (.mem .rbp .rcx (BitVec.ofNat 32 0)) 0 xwS = some xwS' :=
  rfl

/-- The swap observably changes canonical memory at `xchgA`. -/
theorem xw_mem_aendert :
    xwS.tso.mem.bytes xchgA ≠ xwS'.tso.mem.bytes xchgA := by
  decide

/-- The witness bytes decode to the memory form with no rest. -/
theorem xw_dekodiert :
    decodeXchg (encodeXchg (.mem .rbp .rcx (BitVec.ofNat 32 0))) =
      some ((.mem .rbp .rcx (BitVec.ofNat 32 0)), []) := by
  have h := roundtrip_xchg_mem .rbp .rcx (BitVec.ofNat 32 0) []
  simpa using h

/-! ## Joint witness (`_zeuge`): every premise jointly inhabited.

    All premises of `XchgOrderNeed_verbindung` together on a
    non-degenerate reached run: the TSO run reaches through a
    memory-changing issue/flush, and the swap itself observably
    changes canonical memory. -/
theorem XchgOrderNeed_verbindung_zeuge :
    ∃ (base src : Register) (d : BitVec 32) (c : Nat)
      (s s' : XchgZustand) (alt : Wort) (m' : Speicher),
      s.tso.puffer c = [] ∧
      read64 s.tso.mem (xchgAddr s.reg base d) = some alt ∧
      lesbar8 s.tso.mem (xchgAddr s.reg base d) = true ∧
      write64 s.tso.mem (xchgAddr s.reg base d) (s.reg src) = some m' ∧
      xchgSchritt (.mem base src d) c s = some s' ∧
      (s'.tso.mem = m' ∧ s'.reg src = alt ∧ s'.flags = s.flags ∧
        s'.tso.puffer c = [] ∧ zaunBereit s'.tso c = true ∧
        brauchtOrdnung (.mem base src d) = true ∧
        xchgZulaessig (.mem base src d) = true ∧
        read64 s'.tso.mem (xchgAddr s.reg base d) = some (s.reg src)) ∧
      s.tso.mem.bytes (xchgAddr s.reg base d) ≠
        s'.tso.mem.bytes (xchgAddr s.reg base d) ∧
      xwTso0.mem.bytes 100 ≠ xwTso2.mem.bytes 100 ∧
      TSOErreichbar xwTso0 s.tso := by
  refine ⟨.rbp, .rcx, BitVec.ofNat 32 0, 0, xwS, xwS',
    BitVec.ofNat 64 0, xwM, xw_hbuf, xw_hrd, xw_hles, xw_hwr,
    xw_schritt, ?_, xw_mem_aendert, xw_tso_aendert, xw_erreichbar⟩
  exact XchgOrderNeed_verbindung .rbp .rcx _ 0 xwS xwS' _ xwM
    xw_hbuf xw_hrd xw_hles xw_hwr xw_schritt

/- CUTS:
   - Codec round trips (`roundtrip_xchg_reg`, `roundtrip_xchg_mem`)
     are checked data, NOT hardware fidelity: no silicon claim follows
     from decode/encode agreement alone.
   - `xchgSchritt` reuses the ONE canonical `TSOZustand` memory and the
     accepted `read64`/`write64`/`Fuss`; no second evaluator, no new
     memory, no source/checker/goal change.
   - The barrier is LOCAL to the acting core's buffer (Vol. 3A
     11.2.3.9 shape): no foreign-buffer drain, no total-order claim
     over several locked instructions, no W/GX simulation and no
     linearisation of G steps.
   - Widths below 64 bits, LOCK-prefixed XCHG, the REX.W+90+rd alias
     row (including the 90H NOP alias), segment overrides, HLE
     hints and fault details beyond explicit `none` refusal stay open
     (`decodeXchg_lock_verweigert`, `decodeXchg_alias90_verweigert`).
   - No alignment demand beyond what `read64`/`write64` decide; no
     split-lock, atomicity-tearing or timing/cycle claim.
   - No fairness, progress, interrupt, device, MMIO or DMA model.
-/

#print axioms brauchtOrdnung
#print axioms xchgZulaessig
#print axioms xchgSchritt
#print axioms encodeXchg
#print axioms rexXchgBits_rexByte
#print axioms roundtrip_xchg_reg
#print axioms roundtrip_xchg_mem
#print axioms XchgOrderNeed_verbindung
#print axioms xchg_mem_verweigert_bei_puffer
#print axioms xchg_mem_bedarf
#print axioms xchg_reg_kein_bedarf
#print axioms xchg_reg_ohne_schranke
#print axioms xchg_mem_fuss
#print axioms xchg_reg_fuss_leer
#print axioms xchg_mem_verweigert_ohne_leserecht
#print axioms xchg_mem_verweigert_ohne_schreibrecht
#print axioms encodeXchg_len
#print axioms decodeXchg_lock_verweigert
#print axioms decodeXchg_alias90_verweigert
#print axioms decodeXchg_abgeschnitten_verweigert
#print axioms xw_issue
#print axioms xw_flush
#print axioms xw_tso_aendert
#print axioms xw_erreichbar
#print axioms xw_hbuf
#print axioms xw_hrd
#print axioms xw_hles
#print axioms xw_hwr
#print axioms xw_schritt
#print axioms xw_mem_aendert
#print axioms xw_dekodiert
#print axioms XchgOrderNeed_verbindung_zeuge

end Gabbro.Grammatik.X86
