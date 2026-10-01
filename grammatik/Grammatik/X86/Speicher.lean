/-
  Byte memory semantics for the direct x86-64 validation pilot (lane 271).

  Permission-checked little-endian byte reads/writes over the canonical
  `Speicher` of `Grammatik.X86.Typen`. Addresses are 64-bit modular values;
  every frame/read-back fact states its no-wrap condition explicitly.
  Eight-byte accesses are per-byte event lists; no atomicity claim is made
  for unaligned concurrent use (that is the TSO bridge lane's business).
-/
import Grammatik.X86.Typen

namespace Gabbro.Grammatik.X86

/-- Byte address: 64-bit modular addition of a natural offset. -/
def addrOff (a : Adresse) (i : Nat) : Adresse := a + BitVec.ofNat 64 i

/-- Little-endian byte `i` of a 64-bit word. -/
def wortByte (v : Wort) (i : Nat) : Byte :=
  BitVec.ofNat 8 ((v.toNat / 256 ^ i) % 256)

/-- Read permission for all eight bytes starting at `a`. -/
def lesbar8 (m : Speicher) (a : Adresse) : Bool :=
  m.lesbar (addrOff a 0) && m.lesbar (addrOff a 1) &&
  m.lesbar (addrOff a 2) && m.lesbar (addrOff a 3) &&
  m.lesbar (addrOff a 4) && m.lesbar (addrOff a 5) &&
  m.lesbar (addrOff a 6) && m.lesbar (addrOff a 7)

/-- Write permission for all eight bytes starting at `a`. -/
def schreibbar8 (m : Speicher) (a : Adresse) : Bool :=
  m.schreibbar (addrOff a 0) && m.schreibbar (addrOff a 1) &&
  m.schreibbar (addrOff a 2) && m.schreibbar (addrOff a 3) &&
  m.schreibbar (addrOff a 4) && m.schreibbar (addrOff a 5) &&
  m.schreibbar (addrOff a 6) && m.schreibbar (addrOff a 7)

/-- Assemble a word from eight little-endian bytes. -/
def bytesWort (f : Fin 8 → Byte) : Wort :=
  BitVec.ofNat 64 ((f 0).toNat + (f 1).toNat * 256 +
    (f 2).toNat * 65536 + (f 3).toNat * 16777216 +
    (f 4).toNat * 4294967296 + (f 5).toNat * 1099511627776 +
    (f 6).toNat * 281474976710656 + (f 7).toNat * 72057594037927936)

/-- The eight bytes stored at `a`, as a function of the byte index. -/
def readBytes (m : Speicher) (a : Adresse) : Fin 8 → Byte :=
  fun i => m.bytes (addrOff a i.val)

/-- Little-endian 64-bit load with a per-byte read-permission check. -/
def read64 (m : Speicher) (a : Adresse) : Option Wort :=
  if lesbar8 m a then some (bytesWort (readBytes m a)) else none

/-! ## 5. Byte search and stores -/

/-- Byte offsets below eight name distinct machine addresses, with no
    wrap hypothesis: addition is a group, so distinct small offsets stay
    distinct whatever `a` is. -/
theorem addrOff_inj8 {a : Adresse} {i j : Nat} (hi : i < 8) (hj : j < 8)
    (h : addrOff a i = addrOff a j) : i = j := by
  unfold addrOff at h
  have h2 := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_add,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h2
  have ha := a.isLt
  omega

/-- Distinct offsets below eight name distinct addresses. -/
theorem addrOff_ne8 {a : Adresse} {i j : Nat} (hi : i < 8) (hj : j < 8)
    (hij : i ≠ j) : addrOff a i ≠ addrOff a j :=
  fun he => hij (addrOff_inj8 hi hj he)

/-- Offset zero is the address itself. -/
theorem addrOff_null (a : Adresse) : addrOff a 0 = a := by
  unfold addrOff
  simp

/-- Position search: the index below `n` whose footprint address is `x`,
    if any. The store below is defined through it, so hit/miss facts are
    proved once for every width. -/
def findIdx (a x : Adresse) : Nat → Option Nat
  | 0 => none
  | n+1 => if x = addrOff a n then some n else findIdx a x n

/-- The search finds every footprint index. Needs `n ≤ 8` so the
    competitors it skips are covered by `addrOff_inj8`. -/
theorem findIdx_hit (a : Adresse) (k n : Nat) (hk : k < n) (hn : n ≤ 8) :
    findIdx a (addrOff a k) n = some k := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [findIdx]
    by_cases h : k = n
    · subst h
      simp
    · rw [if_neg (fun he => h (addrOff_inj8 (by omega : k < 8) (by omega : n < 8) he))]
      exact ih (by omega) (by omega)

/-- The search misses exactly the addresses outside the footprint. -/
theorem findIdx_miss (a x : Adresse) (n : Nat)
    (h : ∀ k, k < n → x ≠ addrOff a k) :
    findIdx a x n = none := by
  induction n with
  | zero => simp only [findIdx]
  | succ n ih =>
    simp only [findIdx]
    rw [if_neg (h n (Nat.lt_succ_self n))]
    exact ih (fun k hk => h k (Nat.lt_succ_of_lt hk))

/-- The byte store of an `n`-byte write: footprint addresses carry the
    word's little-endian bytes, everything else is unchanged. -/
def writeBytesN (m : Speicher) (a : Adresse) (v : Wort) (n : Nat)
    (x : Adresse) : Byte :=
  match findIdx a x n with
  | some k => wortByte v k
  | none => m.bytes x

/-- A footprint byte holds the word's byte. -/
theorem writeBytesN_hit (m : Speicher) (a : Adresse) (v : Wort) (n k : Nat)
    (hk : k < n) (hn : n ≤ 8) :
    writeBytesN m a v n (addrOff a k) = wortByte v k := by
  unfold writeBytesN
  rw [findIdx_hit a k n hk hn]

/-- An address outside the footprint keeps its byte. -/
theorem writeBytesN_miss (m : Speicher) (a : Adresse) (v : Wort) (n : Nat)
    (x : Adresse) (h : ∀ k, k < n → x ≠ addrOff a k) :
    writeBytesN m a v n x = m.bytes x := by
  unfold writeBytesN
  rw [findIdx_miss a x n h]

/-- The byte store of one 64-bit write: the eight footprint addresses
    carry the word's little-endian bytes, everything else is unchanged. -/
def writeBytes (m : Speicher) (a : Adresse) (v : Wort) (x : Adresse) : Byte :=
  writeBytesN m a v 8 x

/-- Little-endian 64-bit store with a per-byte write-permission check.
    A refused store returns `none`: memory is unchanged by construction. -/
def write64 (m : Speicher) (a : Adresse) (v : Wort) : Option Speicher :=
  if schreibbar8 m a then some { m with bytes := writeBytes m a v } else none

/-- Read permission for the first `n` bytes starting at `a`. -/
def lesbarN (m : Speicher) (a : Adresse) : Nat → Bool
  | 0 => true
  | n+1 => lesbarN m a n && m.lesbar (addrOff a n)

/-- Write permission for the first `n` bytes starting at `a`. -/
def schreibbarN (m : Speicher) (a : Adresse) : Nat → Bool
  | 0 => true
  | n+1 => schreibbarN m a n && m.schreibbar (addrOff a n)

/-- The generic check covers exactly the eight explicit bytes. -/
theorem lesbarN_acht (m : Speicher) (a : Adresse) :
    lesbarN m a 8 = lesbar8 m a := rfl

/-- The generic check covers exactly the eight explicit bytes. -/
theorem schreibbarN_acht (m : Speicher) (a : Adresse) :
    schreibbarN m a 8 = schreibbar8 m a := rfl

/-! ## 3. Address arithmetic: no-wrap, footprints -/

/-- Explicit no-wrap condition: the eight bytes starting at `a` sit in one
    Nat interval, so consumers may reason with `a.toNat + i`. -/
def OhneUmbruch (a : Adresse) : Prop := a.toNat + 8 ≤ 2 ^ 64

/-- Under no-wrap, machine address addition is Nat addition. -/
theorem ohneUmbruch_addrs (a : Adresse) (h : OhneUmbruch a) (i : Nat)
    (hi : i < 8) : (addrOff a i).toNat = a.toNat + i := by
  unfold OhneUmbruch at h
  unfold addrOff
  have ha := a.isLt
  have hi64 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, hi64,
    Nat.mod_eq_of_lt (by omega : a.toNat + i < 2 ^ 64)]

/-- Two footprints are disjoint: every byte address differs. -/
def Disjunkt (a b : Adresse) : Prop :=
  ∀ i j : Nat, i < 8 → j < 8 → addrOff a i ≠ addrOff b j

/-- The eight footprint addresses are pairwise distinct. -/
theorem fuss_entzerrt (a : Adresse) (i j : Fin 8) (hij : i ≠ j) :
    addrOff a i.val ≠ addrOff a j.val :=
  addrOff_ne8 i.isLt j.isLt (fun e => hij (Fin.ext e))

/-- Nat-interval disjointness gives footprint disjointness, under no-wrap
    on both sides. -/
theorem disjunkt_von_intervallen (a b : Adresse)
    (hA : OhneUmbruch a) (hB : OhneUmbruch b)
    (h : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    Disjunkt a b := by
  intro i j hi hj he
  have e1 := ohneUmbruch_addrs a hA i hi
  have e2 := ohneUmbruch_addrs b hB j hj
  have h2 := congrArg BitVec.toNat he
  rw [e1, e2] at h2
  omega

/-! ## 4. Per-byte events for the future TSO bridge -/

/-- The read events of an `n`-byte access: one event per byte address.
    An eight-byte access is eight events; this states nothing about
    atomicity under concurrency. -/
def leseEreignisse (a : Adresse) (n : Nat) : List Adresse :=
  (List.range n).map (addrOff a)

/-- The write events of an `n`-byte access: one event per byte address. -/
def schreibEreignisse (a : Adresse) (n : Nat) : List Adresse :=
  (List.range n).map (addrOff a)

/-- The eight footprint addresses of an eight-byte access. -/
def Fuss (a : Adresse) : List Adresse := (List.range 8).map (addrOff a)

/-- An eight-byte read is eight per-byte events. -/
theorem leseEreignisse_acht (a : Adresse) :
    leseEreignisse a 8 = Fuss a := rfl

/-- An eight-byte write is eight per-byte events. -/
theorem schreibEreignisse_acht (a : Adresse) :
    schreibEreignisse a 8 = Fuss a := rfl

theorem leseEreignisse_laenge (a : Adresse) (n : Nat) :
    (leseEreignisse a n).length = n := by
  simp [leseEreignisse]

theorem schreibEreignisse_laenge (a : Adresse) (n : Nat) :
    (schreibEreignisse a n).length = n := by
  simp [schreibEreignisse]

theorem leseEreignisse_mem (a x : Adresse) (n : Nat) :
    x ∈ leseEreignisse a n ↔ ∃ k, k < n ∧ addrOff a k = x := by
  unfold leseEreignisse
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [List.mem_range] at hk
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.mpr hk, rfl⟩

theorem schreibEreignisse_mem (a x : Adresse) (n : Nat) :
    x ∈ schreibEreignisse a n ↔ ∃ k, k < n ∧ addrOff a k = x := by
  unfold schreibEreignisse
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [List.mem_range] at hk
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.mpr hk, rfl⟩

theorem fuss_laenge (a : Adresse) : (Fuss a).length = 8 := by
  simp [Fuss]

/-! ## 6. Store effects: permissions, refusal, read-back, frames -/

/-- A successful write preserves all permissions: only `bytes` changes. -/
theorem write64_erhaelt_berechtigungen (m : Speicher) (a : Adresse)
    (v : Wort) (m' : Speicher) (hwr : write64 m a v = some m') :
    m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
      m'.ausfuehrbar = m.ausfuehrbar := by
  unfold write64 at hwr
  by_cases hc : schreibbar8 m a = true
  · rw [if_pos hc] at hwr
    cases hwr
    exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hc] at hwr
    cases hwr

/-- A refused write returns `none`: by construction no memory changes. -/
theorem write64_verweigert (m : Speicher) (a : Adresse) (v : Wort)
    (h : schreibbar8 m a = false) : write64 m a v = none := by
  unfold write64
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- A refused write has no successful outcome at all. -/
theorem write64_verweigert_kein_effekt (m m' : Speicher) (a : Adresse)
    (v : Wort) (h : schreibbar8 m a = false) :
    write64 m a v ≠ some m' := by
  simp [write64_verweigert m a v h]

/-- Replacing `bytes` leaves every generic read check unchanged. -/
theorem lesbarN_update (m : Speicher) (f : Adresse → Byte) (b : Adresse)
    (n : Nat) : lesbarN { m with bytes := f } b n = lesbarN m b n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [lesbarN, ih]

/-- Replacing `bytes` leaves every generic write check unchanged. -/
theorem schreibbarN_update (m : Speicher) (f : Adresse → Byte)
    (b : Adresse) (n : Nat) :
    schreibbarN { m with bytes := f } b n = schreibbarN m b n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [schreibbarN, ih]

/-- A successful write leaves the eight read permissions unchanged. -/
theorem lesbar8_nach_schreiben (m m' : Speicher) (a b : Adresse)
    (v : Wort) (hwr : write64 m a v = some m') :
    lesbar8 m' b = lesbar8 m b := by
  have hperm := write64_erhaelt_berechtigungen m a v m' hwr
  unfold lesbar8
  rw [hperm.1]

/-- A successful write leaves the eight write permissions unchanged. -/
theorem schreibbar8_nach_schreiben (m m' : Speicher) (a b : Adresse)
    (v : Wort) (hwr : write64 m a v = some m') :
    schreibbar8 m' b = schreibbar8 m b := by
  have hperm := write64_erhaelt_berechtigungen m a v m' hwr
  unfold schreibbar8
  rw [hperm.2.1]

/-- Little-endian reassembly inverts byte splitting. -/
theorem bytesWort_wortByte (v : Wort) :
    bytesWort (fun i => wortByte v i.val) = v := by
  apply BitVec.eq_of_toNat_eq
  unfold bytesWort wortByte
  simp only [BitVec.toNat_ofNat,
    show ((0 : Fin 8).val) = 0 from rfl,
    show ((1 : Fin 8).val) = 1 from rfl,
    show ((2 : Fin 8).val) = 2 from rfl,
    show ((3 : Fin 8).val) = 3 from rfl,
    show ((4 : Fin 8).val) = 4 from rfl,
    show ((5 : Fin 8).val) = 5 from rfl,
    show ((6 : Fin 8).val) = 6 from rfl,
    show ((7 : Fin 8).val) = 7 from rfl]
  omega

/-- READ-AFTER-WRITE: a successful store reads back through a readable
    footprint. Needs readability besides writability, since read and write
    permissions are independent fields. -/
theorem read64_nach_write64 (m m' : Speicher) (a : Adresse) (v : Wort)
    (hwr : write64 m a v = some m') (hrd : lesbar8 m a = true) :
    read64 m' a = some v := by
  unfold write64 at hwr
  by_cases hc : schreibbar8 m a = true
  · rw [if_pos hc] at hwr
    cases hwr
    have hle : lesbar8 { m with bytes := writeBytes m a v } a = true := hrd
    have hbytes : readBytes { m with bytes := writeBytes m a v } a =
        fun i => wortByte v i.val := by
      funext i
      show writeBytes m a v (addrOff a i.val) = wortByte v i.val
      unfold writeBytes
      exact writeBytesN_hit m a v 8 i.val i.isLt (Nat.le_refl 8)
    unfold read64
    rw [hle, hbytes, bytesWort_wortByte, if_pos rfl]
  · rw [if_neg hc] at hwr
    cases hwr

/-- A store changes nothing outside its footprint. -/
theorem write64_rahmen (m m' : Speicher) (a x : Adresse) (v : Wort)
    (hwr : write64 m a v = some m')
    (haussen : ∀ k : Nat, k < 8 → x ≠ addrOff a k) :
    m'.bytes x = m.bytes x := by
  unfold write64 at hwr
  by_cases hc : schreibbar8 m a = true
  · rw [if_pos hc] at hwr
    cases hwr
    show writeBytes m a v x = m.bytes x
    unfold writeBytes
    exact writeBytesN_miss m a v 8 x haussen
  · rw [if_neg hc] at hwr
    cases hwr

/-- A read at a disjoint footprint survives a store elsewhere. -/
theorem read64_rahmen (m m' : Speicher) (a b : Adresse) (v : Wort)
    (hwr : write64 m a v = some m')
    (hdis : Disjunkt a b) :
    read64 m' b = read64 m b := by
  have hle := lesbar8_nach_schreiben m m' a b v hwr
  have hbytes : readBytes m' b = readBytes m b := by
    funext i
    show m'.bytes (addrOff b i.val) = m.bytes (addrOff b i.val)
    exact write64_rahmen m m' a _ v hwr
      (fun k hk => Ne.symm (hdis k i.val hk i.isLt))
  unfold read64
  rw [hle, hbytes]

/-! ## 7. Width-indexed helpers, coherent with `read64`/`write64` -/

/-- One-byte load: the byte zero-extended to a word. -/
def read8 (m : Speicher) (a : Adresse) : Option Wort :=
  if lesbarN m a 1 then some (BitVec.ofNat 64 (m.bytes a).toNat) else none

/-- Two-byte little-endian load. -/
def read16 (m : Speicher) (a : Adresse) : Option Wort :=
  if lesbarN m a 2 then
    some (BitVec.ofNat 64 ((m.bytes a).toNat +
      (m.bytes (addrOff a 1)).toNat * 256))
  else none

/-- Four-byte little-endian load. -/
def read32 (m : Speicher) (a : Adresse) : Option Wort :=
  if lesbarN m a 4 then
    some (BitVec.ofNat 64 ((m.bytes a).toNat +
      (m.bytes (addrOff a 1)).toNat * 256 +
      (m.bytes (addrOff a 2)).toNat * 65536 +
      (m.bytes (addrOff a 3)).toNat * 16777216))
  else none

/-- One-byte store: the word's low byte. -/
def write8 (m : Speicher) (a : Adresse) (v : Wort) : Option Speicher :=
  if schreibbarN m a 1 then
    some { m with bytes := writeBytesN m a v 1 }
  else none

/-- Two-byte little-endian store. -/
def write16 (m : Speicher) (a : Adresse) (v : Wort) : Option Speicher :=
  if schreibbarN m a 2 then
    some { m with bytes := writeBytesN m a v 2 }
  else none

/-- Four-byte little-endian store. -/
def write32 (m : Speicher) (a : Adresse) (v : Wort) : Option Speicher :=
  if schreibbarN m a 4 then
    some { m with bytes := writeBytesN m a v 4 }
  else none

/-- Width-indexed load; `.b64` is exactly `read64`. -/
def readBreite (m : Speicher) (b : Breite) (a : Adresse) : Option Wort :=
  match b with
  | .b8 => read8 m a
  | .b16 => read16 m a
  | .b32 => read32 m a
  | .b64 => read64 m a

/-- Width-indexed store; `.b64` is exactly `write64`. -/
def writeBreite (m : Speicher) (b : Breite) (a : Adresse)
    (v : Wort) : Option Speicher :=
  match b with
  | .b8 => write8 m a v
  | .b16 => write16 m a v
  | .b32 => write32 m a v
  | .b64 => write64 m a v

theorem readBreite_b64 (m : Speicher) (a : Adresse) :
    readBreite m .b64 a = read64 m a := rfl

theorem writeBreite_b64 (m : Speicher) (a : Adresse) (v : Wort) :
    writeBreite m .b64 a v = write64 m a v := rfl

/-- A successful one-byte write preserves all permissions. -/
theorem write8_erhaelt_berechtigungen (m : Speicher) (a : Adresse)
    (v : Wort) (m' : Speicher) (hwr : write8 m a v = some m') :
    m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
      m'.ausfuehrbar = m.ausfuehrbar := by
  unfold write8 at hwr
  by_cases hc : schreibbarN m a 1 = true
  · rw [if_pos hc] at hwr
    cases hwr
    exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hc] at hwr
    cases hwr

/-- A successful two-byte write preserves all permissions. -/
theorem write16_erhaelt_berechtigungen (m : Speicher) (a : Adresse)
    (v : Wort) (m' : Speicher) (hwr : write16 m a v = some m') :
    m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
      m'.ausfuehrbar = m.ausfuehrbar := by
  unfold write16 at hwr
  by_cases hc : schreibbarN m a 2 = true
  · rw [if_pos hc] at hwr
    cases hwr
    exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hc] at hwr
    cases hwr

/-- A successful four-byte write preserves all permissions. -/
theorem write32_erhaelt_berechtigungen (m : Speicher) (a : Adresse)
    (v : Wort) (m' : Speicher) (hwr : write32 m a v = some m') :
    m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
      m'.ausfuehrbar = m.ausfuehrbar := by
  unfold write32 at hwr
  by_cases hc : schreibbarN m a 4 = true
  · rw [if_pos hc] at hwr
    cases hwr
    exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hc] at hwr
    cases hwr

/-- READ-AFTER-WRITE for one byte: the low byte reads back. -/
theorem read8_nach_write8 (m m' : Speicher) (a : Adresse) (v : Wort)
    (hwr : write8 m a v = some m') (hrd : lesbarN m a 1 = true) :
    read8 m' a = some (BitVec.ofNat 64 (v.toNat % 256)) := by
  unfold write8 at hwr
  by_cases hc : schreibbarN m a 1 = true
  · rw [if_pos hc] at hwr
    cases hwr
    have hle : lesbarN { m with bytes := writeBytesN m a v 1 } a 1 = true := by
      rw [lesbarN_update]
      exact hrd
    have b0 : writeBytesN m a v 1 a = wortByte v 0 := by
      have hhit := writeBytesN_hit m a v 1 0 (by decide) (by decide)
      rwa [addrOff_null a] at hhit
    unfold read8
    rw [if_pos hle]
    congr 1
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 64 (writeBytesN m a v 1 a).toNat).toNat =
      (BitVec.ofNat 64 (v.toNat % 256)).toNat
    rw [b0]
    unfold wortByte
    simp only [BitVec.toNat_ofNat]
    omega
  · rw [if_neg hc] at hwr
    cases hwr

/-- READ-AFTER-WRITE for two bytes: the low 16 bits read back. -/
theorem read16_nach_write16 (m m' : Speicher) (a : Adresse) (v : Wort)
    (hwr : write16 m a v = some m') (hrd : lesbarN m a 2 = true) :
    read16 m' a = some (BitVec.ofNat 64 (v.toNat % 65536)) := by
  unfold write16 at hwr
  by_cases hc : schreibbarN m a 2 = true
  · rw [if_pos hc] at hwr
    cases hwr
    have hle : lesbarN { m with bytes := writeBytesN m a v 2 } a 2 = true := by
      rw [lesbarN_update]
      exact hrd
    have b0 : writeBytesN m a v 2 a = wortByte v 0 := by
      have hhit := writeBytesN_hit m a v 2 0 (by decide) (by decide)
      rwa [addrOff_null a] at hhit
    have b1 : writeBytesN m a v 2 (addrOff a 1) = wortByte v 1 :=
      writeBytesN_hit m a v 2 1 (by decide) (by decide)
    unfold read16
    rw [if_pos hle]
    congr 1
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 64 ((writeBytesN m a v 2 a).toNat +
      (writeBytesN m a v 2 (addrOff a 1)).toNat * 256)).toNat =
      (BitVec.ofNat 64 (v.toNat % 65536)).toNat
    rw [b0, b1]
    unfold wortByte
    simp only [BitVec.toNat_ofNat]
    omega
  · rw [if_neg hc] at hwr
    cases hwr

/-- READ-AFTER-WRITE for four bytes: the low 32 bits read back. -/
theorem read32_nach_write32 (m m' : Speicher) (a : Adresse) (v : Wort)
    (hwr : write32 m a v = some m') (hrd : lesbarN m a 4 = true) :
    read32 m' a = some (BitVec.ofNat 64 (v.toNat % 4294967296)) := by
  unfold write32 at hwr
  by_cases hc : schreibbarN m a 4 = true
  · rw [if_pos hc] at hwr
    cases hwr
    have hle : lesbarN { m with bytes := writeBytesN m a v 4 } a 4 = true := by
      rw [lesbarN_update]
      exact hrd
    have b0 : writeBytesN m a v 4 a = wortByte v 0 := by
      have hhit := writeBytesN_hit m a v 4 0 (by decide) (by decide)
      rwa [addrOff_null a] at hhit
    have b1 : writeBytesN m a v 4 (addrOff a 1) = wortByte v 1 :=
      writeBytesN_hit m a v 4 1 (by decide) (by decide)
    have b2 : writeBytesN m a v 4 (addrOff a 2) = wortByte v 2 :=
      writeBytesN_hit m a v 4 2 (by decide) (by decide)
    have b3 : writeBytesN m a v 4 (addrOff a 3) = wortByte v 3 :=
      writeBytesN_hit m a v 4 3 (by decide) (by decide)
    unfold read32
    rw [if_pos hle]
    congr 1
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 64 ((writeBytesN m a v 4 a).toNat +
      (writeBytesN m a v 4 (addrOff a 1)).toNat * 256 +
      (writeBytesN m a v 4 (addrOff a 2)).toNat * 65536 +
      (writeBytesN m a v 4 (addrOff a 3)).toNat * 16777216)).toNat =
      (BitVec.ofNat 64 (v.toNat % 4294967296)).toNat
    rw [b0, b1, b2, b3]
    unfold wortByte
    simp only [BitVec.toNat_ofNat]
    omega
  · rw [if_neg hc] at hwr
    cases hwr

/-- One-byte store frame. -/
theorem write8_rahmen (m m' : Speicher) (a x : Adresse) (v : Wort)
    (hwr : write8 m a v = some m')
    (haussen : ∀ k : Nat, k < 1 → x ≠ addrOff a k) :
    m'.bytes x = m.bytes x := by
  unfold write8 at hwr
  by_cases hc : schreibbarN m a 1 = true
  · rw [if_pos hc] at hwr
    cases hwr
    show writeBytesN m a v 1 x = m.bytes x
    exact writeBytesN_miss m a v 1 x haussen
  · rw [if_neg hc] at hwr
    cases hwr

/-- Two-byte store frame. -/
theorem write16_rahmen (m m' : Speicher) (a x : Adresse) (v : Wort)
    (hwr : write16 m a v = some m')
    (haussen : ∀ k : Nat, k < 2 → x ≠ addrOff a k) :
    m'.bytes x = m.bytes x := by
  unfold write16 at hwr
  by_cases hc : schreibbarN m a 2 = true
  · rw [if_pos hc] at hwr
    cases hwr
    show writeBytesN m a v 2 x = m.bytes x
    exact writeBytesN_miss m a v 2 x haussen
  · rw [if_neg hc] at hwr
    cases hwr

/-- Four-byte store frame. -/
theorem write32_rahmen (m m' : Speicher) (a x : Adresse) (v : Wort)
    (hwr : write32 m a v = some m')
    (haussen : ∀ k : Nat, k < 4 → x ≠ addrOff a k) :
    m'.bytes x = m.bytes x := by
  unfold write32 at hwr
  by_cases hc : schreibbarN m a 4 = true
  · rw [if_pos hc] at hwr
    cases hwr
    show writeBytesN m a v 4 x = m.bytes x
    exact writeBytesN_miss m a v 4 x haussen
  · rw [if_neg hc] at hwr
    cases hwr

/-- Width-indexed read-after-write, all widths. -/
theorem readBreite_nach_writeBreite_b8 (m m' : Speicher) (a : Adresse)
    (v : Wort) (hwr : writeBreite m .b8 a v = some m')
    (hrd : lesbarN m a 1 = true) :
    readBreite m' .b8 a = some (BitVec.ofNat 64 (v.toNat % 256)) :=
  read8_nach_write8 m m' a v hwr hrd

theorem readBreite_nach_writeBreite_b16 (m m' : Speicher) (a : Adresse)
    (v : Wort) (hwr : writeBreite m .b16 a v = some m')
    (hrd : lesbarN m a 2 = true) :
    readBreite m' .b16 a = some (BitVec.ofNat 64 (v.toNat % 65536)) :=
  read16_nach_write16 m m' a v hwr hrd

theorem readBreite_nach_writeBreite_b32 (m m' : Speicher) (a : Adresse)
    (v : Wort) (hwr : writeBreite m .b32 a v = some m')
    (hrd : lesbarN m a 4 = true) :
    readBreite m' .b32 a =
      some (BitVec.ofNat 64 (v.toNat % 4294967296)) :=
  read32_nach_write32 m m' a v hwr hrd

theorem readBreite_nach_writeBreite_b64 (m m' : Speicher) (a : Adresse)
    (v : Wort) (hwr : writeBreite m .b64 a v = some m')
    (hrd : lesbar8 m a = true) :
    readBreite m' .b64 a = some v :=
  read64_nach_write64 m m' a v hwr hrd

/-- Width-indexed store frames, all widths. -/
theorem writeBreite_rahmen_b8 (m m' : Speicher) (a x : Adresse)
    (v : Wort) (hwr : writeBreite m .b8 a v = some m')
    (haussen : ∀ k : Nat, k < 1 → x ≠ addrOff a k) :
    m'.bytes x = m.bytes x :=
  write8_rahmen m m' a x v hwr haussen

theorem writeBreite_rahmen_b16 (m m' : Speicher) (a x : Adresse)
    (v : Wort) (hwr : writeBreite m .b16 a v = some m')
    (haussen : ∀ k : Nat, k < 2 → x ≠ addrOff a k) :
    m'.bytes x = m.bytes x :=
  write16_rahmen m m' a x v hwr haussen

theorem writeBreite_rahmen_b32 (m m' : Speicher) (a x : Adresse)
    (v : Wort) (hwr : writeBreite m .b32 a v = some m')
    (haussen : ∀ k : Nat, k < 4 → x ≠ addrOff a k) :
    m'.bytes x = m.bytes x :=
  write32_rahmen m m' a x v hwr haussen

theorem writeBreite_rahmen_b64 (m m' : Speicher) (a x : Adresse)
    (v : Wort) (hwr : writeBreite m .b64 a v = some m')
    (haussen : ∀ k : Nat, k < 8 → x ≠ addrOff a k) :
    m'.bytes x = m.bytes x :=
  write64_rahmen m m' a x v hwr haussen

/-! ## 8. Joint witness: a nonzero eight-byte write and read-back -/

/-- Fully permissive memory with zeroed bytes. -/
def zeugenSpeicher : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun _ => false }

/-- A nonzero word: `0x0102030405060708`. -/
def zeugenWort : Wort := BitVec.ofNat 64 0x0102030405060708

/-- The witness memory after the eight-byte write at address zero. -/
def zeugenSpeicherNach : Speicher :=
  { zeugenSpeicher with bytes := writeBytes zeugenSpeicher 0 zeugenWort }

/-- A nonzero eight-byte write goes through, reads back, and observably
    changes memory (byte `0x00` becomes `0x08` at the base address). -/
theorem write_read_zeuge :
    ∃ (m m' : Speicher) (a : Adresse) (v : Wort),
      v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
        m.bytes a ≠ m'.bytes a := by
  refine ⟨zeugenSpeicher, zeugenSpeicherNach, 0, zeugenWort,
    by decide, ?_, ?_, ?_⟩
  · unfold write64
    have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
    rw [if_pos hc]
    rfl
  · exact read64_nach_write64 zeugenSpeicher _ 0 zeugenWort
      (by unfold write64
          have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
          rw [if_pos hc]
          rfl) rfl
  · have hhit :=
      writeBytesN_hit zeugenSpeicher 0 zeugenWort 8 0 (by decide) (by decide)
    rw [addrOff_null (0 : Adresse)] at hhit
    show BitVec.ofNat 8 0 ≠ writeBytes zeugenSpeicher 0 zeugenWort 0
    unfold writeBytes
    rw [hhit]
    decide

/-- The same joint witness through the width-indexed interface. -/
theorem writeBreite_read_zeuge :
    ∃ (m m' : Speicher) (a : Adresse) (v : Wort),
      v ≠ 0 ∧ writeBreite m .b64 a v = some m' ∧
        readBreite m' .b64 a = some v ∧ m.bytes a ≠ m'.bytes a := by
  obtain ⟨m, m', a, v, hne, hwr, hrd, hchg⟩ := write_read_zeuge
  exact ⟨m, m', a, v, hne, hwr, hrd, hchg⟩

/- CUTS:
   - No atomicity claim for eight-byte (or any multi-byte) accesses under
     concurrency: every lemma here is sequential over one `Speicher`.
     Per-access TSO granularity, alignment/tearing correspondence and the
     GX refinement stay with the TSO-bridge lane (274). The per-byte event
     lists (`leseEreignisse`/`schreibEreignisse`) are the hooks for that work.
   - No decoder, encoder, instruction semantics, ABI/loader, cost transfer
     or source correspondence: this file is byte memory only, over the
     canonical `Typen.lean` vocabulary which it does not extend.
   - No refusal analogues of `write64_verweigert` for the 1/2/4-byte stores
     are stated separately; each refuses exactly when its `schreibbarN`
     check fails, by the same `none` construction.
   - `OhneUmbruch`/`Disjunkt`/`disjunkt_von_intervallen` cover the
     no-wrap/distinct-address conditions of the frame lemmas; footprint
     injectivity itself (`addrOff_inj8`) needs no wrap hypothesis.
-/

#print axioms addrOff_inj8
#print axioms addrOff_ne8
#print axioms addrOff_null
#print axioms ohneUmbruch_addrs
#print axioms fuss_entzerrt
#print axioms disjunkt_von_intervallen
#print axioms findIdx_hit
#print axioms findIdx_miss
#print axioms writeBytesN_hit
#print axioms writeBytesN_miss
#print axioms write64_erhaelt_berechtigungen
#print axioms write64_verweigert
#print axioms write64_verweigert_kein_effekt
#print axioms lesbarN_update
#print axioms schreibbarN_update
#print axioms lesbar8_nach_schreiben
#print axioms schreibbar8_nach_schreiben
#print axioms bytesWort_wortByte
#print axioms read64_nach_write64
#print axioms write64_rahmen
#print axioms read64_rahmen
#print axioms readBreite_b64
#print axioms writeBreite_b64
#print axioms read8_nach_write8
#print axioms read16_nach_write16
#print axioms read32_nach_write32
#print axioms write8_rahmen
#print axioms write16_rahmen
#print axioms write32_rahmen
#print axioms write_read_zeuge
#print axioms writeBreite_read_zeuge

end Gabbro.Grammatik.X86
