/-
  File:      Grammatik/X86/BitCount.lean
  Subject:   Fixed-width population count over the canonical words (lane 419).

  Extension helpers for the SAME x86-64 target: population count at the
  four pilot widths over the REAL canonical `Wort` (BitVec 64) from
  `Grammatik/X86/Typen.lean`, reusing `trunc` and `bitAt` from
  `Grammatik/X86/Wort.lean`. No new word/register/state types, no
  `Befehl` change. This file proves pure fixed-width ARITHMETIC (counts
  and bounds over `toNat` bits), never physical-CPU behaviour: the
  silicon correspondence for any future POPCNT form stays OPEN.
-/
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- Population count of the low `k` bits of `n` (structural recursion). -/
def popCountAux : Nat → Nat → Nat
  | _, 0 => 0
  | n, k + 1 => bitAt n k + popCountAux n k

/-- Fixed-width population count: set bits among the low `b.bits` bits. -/
def popCount (b : Breite) (w : Wort) : Nat :=
  popCountAux (trunc b w).toNat b.bits

/-- Population-count result word: the count as a 64-bit word. -/
def popWort (b : Breite) (w : Wort) : Wort :=
  BitVec.ofNat 64 (popCount b w)

/-- The auxiliary count never exceeds the bit budget. -/
theorem popCountAux_schranke (n k : Nat) : popCountAux n k ≤ k := by
  induction k with
  | zero => simp [popCountAux]
  | succ k ih =>
    simp only [popCountAux]
    unfold bitAt
    split <;> omega

/-! ## 1. Width bounds and the result word value. -/

/-- Every pilot width holds at most 64 bits. -/
theorem bits_schranke (b : Breite) : b.bits ≤ 64 := by
  cases b <;> decide

/-- The fixed-width count never exceeds the named width. -/
theorem popCount_schranke (b : Breite) (w : Wort) :
    popCount b w ≤ b.bits := by
  unfold popCount
  exact popCountAux_schranke _ _

/-- The count fits in one word: at most 64. -/
theorem popCount_wort_schranke (b : Breite) (w : Wort) :
    popCount b w ≤ 64 := by
  have h1 := popCount_schranke b w
  have h2 := bits_schranke b
  omega

/-- The result word denotes exactly the count (no wrap: the count is
    below `2 ^ 64`). -/
theorem popWort_wert (b : Breite) (w : Wort) :
    (popWort b w).toNat = popCount b w := by
  unfold popWort
  rw [BitVec.toNat_ofNat]
  have h := popCount_wort_schranke b w
  have hlt : popCount b w < 2 ^ 64 := by omega
  exact Nat.mod_eq_of_lt hlt

/-! ## 2. The defined/undefined flag contract.

    The architectural POPCNT contract (stated executable semantics, not
    verified against silicon): ZF is DEFINED (set exactly when the count
    is zero); CF, OF, SF and PF are UNDEFINED (left unconstrained behind
    the validity relation, never forced false); AF is `none` (undefined,
    never false). `Flags` stores all but AF as `Bool`, so returning a
    `Flags` with arbitrary CF/OF/SF/PF would state hardware truth this
    file does not have; instead snapshots keep the incoming undefined
    bits (an explicit modelling choice, §3) and the relation pins only
    the destination value, ZF and AF. -/

/-- Defined zero flag: set exactly when the count is zero. -/
def popNull (b : Breite) (w : Wort) : Bool :=
  decide (popCount b w = 0)

/-- Validity for a POPCNT result: destination holds the count, ZF is
    the defined zero test, AF is undefined; CF/OF/SF/PF are
    unconstrained (existentially, never forced false). -/
def PopcntGueltig (b : Breite) (w dst : Wort) (f : Flags) : Prop :=
  dst = popWort b w ∧ f.zf = popNull b w ∧ f.af = none

/-- The zero flag means a zero count. -/
theorem popNull_heisst (b : Breite) (w : Wort) :
    popNull b w = true ↔ popCount b w = 0 := by
  simp [popNull]

/-- The result word is zero exactly when the count is zero (so ZF also
    reads the result word). -/
theorem popWort_null (b : Breite) (w : Wort) :
    popWort b w = 0 ↔ popCount b w = 0 := by
  have hval := popWort_wert b w
  have hzero : (0 : Wort).toNat = 0 := by decide
  constructor
  · intro h
    rw [h] at hval
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    omega

/-! ## 3. Flag snapshot, feature admission and the register step.

    The snapshot pins exactly the defined bits (ZF, AF `none`) and KEEPS
    the incoming CF/OF/SF/PF: preservation is an explicit modelling
    choice for undefined bits, not hardware truth, proved below to
    satisfy `PopcntGueltig`. `PopcntMerkmal` is validator admission (a
    `Bool`), NOT an invented hardware fault: a refused image is refused
    (`verweigert`), never executed -- and a refusal is not a `hardware`
    stop either. The step handles ONLY this future form, reusing the
    canonical `laengeOk`/`ripNach`/`regSet` shapes; the pilot `schritt`
    forms are untouched. -/

/-- POPCNT flag snapshot over incoming flags: ZF pinned, AF undefined,
    CF/OF/SF/PF kept. -/
def popcntFlags (f : Flags) (b : Breite) (w : Wort) : Flags :=
  { f with zf := popNull b w, af := none }

/-- The snapshot satisfies the validity relation. -/
theorem popcntFlags_gueltig (f : Flags) (b : Breite) (w : Wort) :
    PopcntGueltig b w (popWort b w) (popcntFlags f b w) := by
  simp [popcntFlags, PopcntGueltig]

/-- A valid snapshot always exists (undefined flags arbitrary). -/
theorem popcnt_gueltig_existenz (b : Breite) (w : Wort) :
    ∃ f : Flags, PopcntGueltig b w (popWort b w) f :=
  ⟨popcntFlags (Flags.mk false false none false false false) b w,
    popcntFlags_gueltig _ b w⟩

/-- Undefined bits stay undefined: two valid snapshots differ in CF. -/
theorem popcnt_unbestimmt_unbeschraenkt (b : Breite) (w : Wort) :
    ∃ f1 f2 : Flags,
      PopcntGueltig b w (popWort b w) f1 ∧
      PopcntGueltig b w (popWort b w) f2 ∧ f1.cf ≠ f2.cf := by
  refine ⟨popcntFlags (Flags.mk true false none false false false) b w,
    popcntFlags (Flags.mk false false none false false false) b w,
    popcntFlags_gueltig _ b w, popcntFlags_gueltig _ b w, by simp [popcntFlags]⟩

/-- Undefined stays undefined even at zero: a valid snapshot of the
    zero count may still carry CF. No peephole may read CF after POPCNT. -/
theorem unbestimmt_bleibt_unbestimmt (b : Breite) (w : Wort) :
    ∃ f : Flags, PopcntGueltig b w (popWort b w) f ∧ f.cf = true :=
  ⟨popcntFlags (Flags.mk true false none false false false) b w,
    popcntFlags_gueltig _ b w, rfl⟩

/-- Validator-side CPU feature record for the POPCNT form (data only:
    decided admission, never a hardware probe). -/
structure PopcntMerkmal where
  popcnt : Bool
  deriving DecidableEq, Repr

/-- Decided admission: the POPCNT form is admitted exactly when the
    feature record carries it. -/
def popcntZugelassen (m : PopcntMerkmal) : Bool := m.popcnt

/-- The guard reads the feature record. -/
theorem popcntZugelassen_heisst (m : PopcntMerkmal) :
    popcntZugelassen m = m.popcnt := rfl

/-- A missing feature is refused by the decided guard. -/
theorem zugelassen_verweigert_ohne_merkmal (m : PopcntMerkmal)
    (h : m.popcnt = false) : popcntZugelassen m = false := by
  simp [popcntZugelassen, h]

/-- Decoded future-form instruction: destination, source, width and
    checked length data. Wiring into `Befehl` stays with the Typen owner;
    this type exposes exactly how the one target semantics grows. -/
structure BitCountDecodiert where
  dst : Register
  src : Register
  breite : Breite
  laenge : Nat
  deriving DecidableEq, Repr

/-- Step outcome: successor, feature refusal, or decode refusal. -/
inductive BitCountErgebnis where
  | ok (nach : Zustand)
  | verweigert
  | misslungen

/-- Single future-form step; the feature check is never folded away. -/
def popcntSchritt (m : PopcntMerkmal) (d : BitCountDecodiert)
    (s : Zustand) : BitCountErgebnis :=
  match laengeOk d.laenge with
  | false => .misslungen
  | true =>
    match m.popcnt with
    | false => .verweigert
    | true =>
      .ok { s with
        register := regSet s.register d.dst (popWort d.breite (s.register d.src)),
        rip := ripNach s.rip d.laenge,
        flags := popcntFlags s.flags d.breite (s.register d.src) }

/-! ## Step equations for the future form.

    Each equation pins the full successor or the refusal; every premise
    is used. A refused image is never executed: `verweigert` carries no
    state. -/

/-- Admitted step: the destination holds the count with the §2 snapshot. -/
theorem bc_ok (m : PopcntMerkmal) (d : BitCountDecodiert) (s : Zustand)
    (hok : laengeOk d.laenge = true) (hfeat : m.popcnt = true) :
    popcntSchritt m d s = .ok { s with
      register := regSet s.register d.dst (popWort d.breite (s.register d.src)),
      rip := ripNach s.rip d.laenge,
      flags := popcntFlags s.flags d.breite (s.register d.src) } := by
  unfold popcntSchritt
  rw [hok, hfeat]

/-- Feature refusal: a missing feature refuses the image, never a value. -/
theorem bc_verweigert (m : PopcntMerkmal) (d : BitCountDecodiert)
    (s : Zustand) (hok : laengeOk d.laenge = true)
    (hfeat : m.popcnt = false) :
    popcntSchritt m d s = .verweigert := by
  unfold popcntSchritt
  rw [hok, hfeat]

/-- A bad decode length refuses every form, unconditionally. -/
theorem bc_laenge_misslungen (m : PopcntMerkmal) (d : BitCountDecodiert)
    (s : Zustand) (h : laengeOk d.laenge = false) :
    popcntSchritt m d s = .misslungen := by
  unfold popcntSchritt
  rw [h]

/-- A refused image traps in the step: guard and step agree. -/
theorem verweigert_heisst_verweigert (m : PopcntMerkmal)
    (d : BitCountDecodiert) (s : Zustand)
    (hok : laengeOk d.laenge = true)
    (hzu : popcntZugelassen m = false) :
    popcntSchritt m d s = .verweigert := by
  have hfeat : m.popcnt = false := by
    simp [popcntZugelassen] at hzu
    exact hzu
  exact bc_verweigert m d s hok hfeat

/-- Without the feature no step is a success: the refusal is not an
    `ok` with cleared flags. -/
theorem ohne_merkmal_kein_ok (m : PopcntMerkmal) (d : BitCountDecodiert)
    (s : Zustand) (h : m.popcnt = false)
    (hok : laengeOk d.laenge = true) (z : BitCountErgebnis)
    (hstep : popcntSchritt m d s = z) :
    ∀ (t : Zustand), z ≠ .ok t := by
  rw [bc_verweigert m d s hok h] at hstep
  subst z
  intro t hcon
  cases hcon

/-! ## 4. Joint witnesses: computed counts through real steps and memory.

    All probes reuse the canonical witness memory/flags from
    `Speicher.lean`/`Ausfuehrung.lean`. Step results are projected to
    plain values before `decide` (states contain functions, so full
    state equality is not decidable); the general equations of §3
    already pin the full states. Sparse (one bit), dense (all bits),
    narrow-truncated and zero counts are pinned positively; the missing
    feature and a bad length are pinned as refusals. -/

/-- Step projection: destination value and ZF of an `ok` outcome. -/
def bcOkWerte (d : BitCountDecodiert) : BitCountErgebnis → Option (Wort × Bool)
  | .ok z => some (z.register d.dst, z.flags.zf)
  | _ => none

/-- Step projection: whether the outcome is the feature refusal. -/
def bcIstVerweigert : BitCountErgebnis → Bool
  | .verweigert => true
  | _ => false

/-- Witness registers: RCX holds the sparse word `1`. -/
def bcRegSparse : Register → Wort := fun q =>
  if q = Register.rcx then 1
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for the sparse count. -/
def bcZustandSparse : Zustand :=
  { register := bcRegSparse, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugenSpeicher }

/-- Witness registers: RCX holds the dense word (all bits set). -/
def bcRegDense : Register → Wort := fun q =>
  if q = Register.rcx then 0xFFFFFFFFFFFFFFFF
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for the dense count. -/
def bcZustandDense : Zustand :=
  { register := bcRegDense, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugenSpeicher }

/-- Witness registers: RCX holds zero. -/
def bcRegNull : Register → Wort := fun q =>
  if q = Register.rcx then 0
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for the zero count. -/
def bcZustandNull : Zustand :=
  { register := bcRegNull, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugenSpeicher }

/-- Value probes: sparse, dense, narrow-truncated and zero counts. -/
theorem probe_zaehlung :
    popCount .b64 1 = 1 ∧ popCount .b64 0xFFFFFFFFFFFFFFFF = 64 ∧
    popCount .b8 0xFF = 8 ∧ popCount .b8 0x1FF = 8 ∧
    popCount .b64 0 = 0 := by
  decide

/-- Sparse step probe: `popcount(1) = 1`, ZF clear. -/
theorem probe_sparse_schritt :
    bcOkWerte ⟨.rax, .rcx, .b64, 3⟩
      (popcntSchritt ⟨true⟩ ⟨.rax, .rcx, .b64, 3⟩ bcZustandSparse) =
      some (1, false) := by
  decide

/-- Dense step probe: `popcount(allOnes) = 64`, ZF clear. -/
theorem probe_dense_schritt :
    bcOkWerte ⟨.rax, .rcx, .b64, 3⟩
      (popcntSchritt ⟨true⟩ ⟨.rax, .rcx, .b64, 3⟩ bcZustandDense) =
      some (64, false) := by
  decide

/-- Zero step probe: `popcount(0) = 0`, ZF set. -/
theorem probe_null_schritt :
    bcOkWerte ⟨.rax, .rcx, .b16, 3⟩
      (popcntSchritt ⟨true⟩ ⟨.rax, .rcx, .b16, 3⟩ bcZustandNull) =
      some (0, true) := by
  decide

/-- Feature-refusal probe: without the feature the image is refused. -/
theorem probe_merkmal_verweigert :
    bcIstVerweigert
      (popcntSchritt ⟨false⟩ ⟨.rax, .rcx, .b64, 3⟩ bcZustandSparse) =
      true := by
  decide

/-- Length-refusal probe: a zero length is no step. -/
theorem probe_laenge_verweigert :
    bcOkWerte ⟨.rax, .rcx, .b64, 0⟩
      (popcntSchritt ⟨true⟩ ⟨.rax, .rcx, .b64, 0⟩ bcZustandSparse) =
      none := by
  decide

/-- The witness memory after storing the sparse count `1` at address zero. -/
def bcSpeicherNachSparse : Speicher :=
  { zeugenSpeicher with bytes := writeBytes zeugenSpeicher 0 (popWort .b64 1) }

/-- The witness memory after also storing the dense count `64` at address 8. -/
def bcSpeicherNachBeide : Speicher :=
  { bcSpeicherNachSparse with
    bytes := writeBytes bcSpeicherNachSparse 8 (popWort .b64 0xFFFFFFFFFFFFFFFF) }

/-- Joint witness: the computed sparse and dense counts go through real
    memory (both stores permission-checked, both read back, the first
    store observably changes memory), jointly with their ZF facts. The
    stored words are nonzero, so the memory change is a real
    memory-changing execution. -/
theorem bitcount_speicher_zeuge :
    popWort .b64 1 = 1 ∧ popWort .b64 0xFFFFFFFFFFFFFFFF = 64 ∧
    popNull .b64 1 = false ∧ popNull .b64 0 = true ∧
    ∃ m1 m2 : Speicher,
      write64 zeugenSpeicher 0 (popWort .b64 1) = some m1 ∧
      read64 m1 0 = some 1 ∧
      zeugenSpeicher.bytes 0 ≠ m1.bytes 0 ∧
      write64 m1 8 (popWort .b64 0xFFFFFFFFFFFFFFFF) = some m2 ∧
      read64 m2 8 = some 64 := by
  refine ⟨by decide, by decide, by decide, by decide,
    bcSpeicherNachSparse, bcSpeicherNachBeide, ?_, ?_, ?_, ?_, ?_⟩
  · have hwr : write64 zeugenSpeicher 0 (popWort .b64 1) =
        some bcSpeicherNachSparse := by
      unfold write64
      have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
      rw [if_pos hc]
      rfl
    exact hwr
  · have hwr : write64 zeugenSpeicher 0 (popWort .b64 1) =
        some bcSpeicherNachSparse := by
      unfold write64
      have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
      rw [if_pos hc]
      rfl
    have hrd := read64_nach_write64 zeugenSpeicher _ 0 (popWort .b64 1)
      hwr rfl
    have hval : popWort .b64 1 = 1 := by decide
    rw [hval] at hrd
    exact hrd
  · have hhit := writeBytesN_hit zeugenSpeicher 0 (popWort .b64 1)
      8 0 (by decide) (by decide)
    rw [addrOff_null (0 : Adresse)] at hhit
    show BitVec.ofNat 8 0 ≠ writeBytes zeugenSpeicher 0 (popWort .b64 1) 0
    unfold writeBytes
    rw [hhit]
    decide
  · have hwr : write64 bcSpeicherNachSparse 8
        (popWort .b64 0xFFFFFFFFFFFFFFFF) = some bcSpeicherNachBeide := by
      unfold write64
      have hc : schreibbar8 bcSpeicherNachSparse 8 = true := rfl
      rw [if_pos hc]
      rfl
    exact hwr
  · have hwr : write64 bcSpeicherNachSparse 8
        (popWort .b64 0xFFFFFFFFFFFFFFFF) = some bcSpeicherNachBeide := by
      unfold write64
      have hc : schreibbar8 bcSpeicherNachSparse 8 = true := rfl
      rw [if_pos hc]
      rfl
    have hrd := read64_nach_write64 bcSpeicherNachSparse _ 8
      (popWort .b64 0xFFFFFFFFFFFFFFFF) hwr rfl
    have hval : popWort .b64 0xFFFFFFFFFFFFFFFF = 64 := by decide
    rw [hval] at hrd
    exact hrd

/- CUTS:
   - Arithmetic only: `popCount`/`popWort` are pure counts over `toNat`
     bits with a proved width bound; no claim about physical POPCNT
     silicon, its latency/throughput, or any measured speed.
   - No instruction encoding or decoding: nothing here claims which
     bytes encode a POPCNT form; Codec owns that, and wiring the future
     form into `Befehl`/`schritt`/decoder/image stays OPEN with the
     Typen owner. `BitCountDecodiert.laenge` is checked input data.
   - No source correspondence: no source lowering, range-proof transfer
     or duty reuse is established (bridge lane's business).
   - No cost transfer: counts carry no timing; budget simulation is not
     modelled.
   - No TSO/concurrency bridge: all facts are sequential over one word
     or one `Speicher`; per-access granularity, alignment/tearing and
     the GX refinement stay with the TSO lane.
   - No hardware verification: the ZF-defined/rest-undefined contract,
     the fixed widths and the feature-gated admission are STATED
     executable semantics, not verified against silicon.
   - No operand-zero characterisation: `count = 0 ↔ trunc = 0` would
     need the mask bound `(trunc b w).toNat < 2 ^ b.bits`, which is not
     proved here; ZF is pinned to the count and the result word only.
   - This file adds no new source-language construct or checker rule:
     no diagnostic, poison-probe, example or CLI numbers are taken.
-/

#print axioms popCountAux_schranke
#print axioms bits_schranke
#print axioms popCount_schranke
#print axioms popCount_wort_schranke
#print axioms popWort_wert
#print axioms popNull_heisst
#print axioms popWort_null
#print axioms popcntFlags_gueltig
#print axioms popcnt_gueltig_existenz
#print axioms popcnt_unbestimmt_unbeschraenkt
#print axioms unbestimmt_bleibt_unbestimmt
#print axioms popcntZugelassen_heisst
#print axioms zugelassen_verweigert_ohne_merkmal
#print axioms bc_ok
#print axioms bc_verweigert
#print axioms bc_laenge_misslungen
#print axioms verweigert_heisst_verweigert
#print axioms ohne_merkmal_kein_ok
#print axioms probe_zaehlung
#print axioms probe_sparse_schritt
#print axioms probe_dense_schritt
#print axioms probe_null_schritt
#print axioms probe_merkmal_verweigert
#print axioms probe_laenge_verweigert
#print axioms bitcount_speicher_zeuge

end Gabbro.Grammatik.X86
