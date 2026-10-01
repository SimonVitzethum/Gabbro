/-
  Checked target regions and allocation ceiling (lane 312).

  Target-side region handles with declared extents/rights over the
  canonical `Typen`/`Speicher` vocabulary: checked no-wrap/disjointness,
  a deterministic checked bump allocator/reserver over a finite supplied
  range with ceiling/refuse-on-full, canonical `Speicher`
  initialisation/permission changes, and an opt-in ceiling-free model
  that still allows failure and explicitly loses the static bound.
  Fresh regions are capabilities from checked allocation, never
  number-to-pointer casts. The runtime/OS allocation contract is user
  logic, never an assumption; source dynamic-region and
  allocator-template correspondence is OPEN (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Target region handle: declared extent plus declared rights. -/
structure Region where
  basis : Nat
  len : Nat
  lesbar : Bool
  schreibbar : Bool
  ausfuehrbar : Bool
  deriving DecidableEq, Repr

/-- Finite supplied memory range: ceiling is `lo + umfang`. -/
structure Vorrat where
  lo : Nat
  umfang : Nat
  deriving DecidableEq, Repr

/-- End of a region extent. -/
def regionEnde (r : Region) : Nat := r.basis + r.len

/-- End (ceiling) of the supplied range. -/
def vorratEnde (v : Vorrat) : Nat := v.lo + v.umfang

/-- Checked containment: inside the supplied range with no 64-bit wrap. -/
def innerhalb (v : Vorrat) (r : Region) : Bool :=
  decide (v.lo ≤ r.basis ∧ r.basis + r.len ≤ v.lo + v.umfang ∧
    r.basis + r.len ≤ 2 ^ 64)

/-- Declared alignment holds at the region base. -/
def ausgerichtet (r : Region) (ausr : Nat) : Bool :=
  decide (0 < ausr ∧ r.basis % ausr = 0)

/-- Two regions are disjoint (empty regions touch nothing). -/
def regionDisjunkt (a b : Region) : Bool :=
  decide (a.basis + a.len ≤ b.basis ∨ b.basis + b.len ≤ a.basis)

/-- Round `x` up to a multiple of `ausr` (zero alignment refuses via `none`). -/
def ausricht (x ausr : Nat) : Option Nat :=
  if ausr = 0 then none
  else some (((x + ausr - 1) / ausr) * ausr)

/-- Rounding never moves backwards. -/
theorem ausricht_monoton (x ausr y : Nat)
    (h : ausricht x ausr = some y) : x ≤ y := by
  unfold ausricht at h
  by_cases hz : ausr = 0
  · simp [hz] at h
  · simp [hz] at h
    subst h
    have hpos : 0 < ausr := Nat.pos_of_ne_zero hz
    have hdiv := Nat.div_add_mod (x + ausr - 1) ausr
    rw [Nat.mul_comm] at hdiv
    have hmod : (x + ausr - 1) % ausr < ausr := Nat.mod_lt _ hpos
    omega

/-- Rounding to 1 is the identity. -/
theorem ausricht_eins (x : Nat) : ausricht x 1 = some x := by
  simp [ausricht]

/-- Zero alignment always refuses. -/
theorem ausricht_null_verweigert (x : Nat) :
    ausricht x 0 = none := by
  simp [ausricht]

/-- Deterministic bump-allocator state over a finite supplied range. -/
structure Reservierer where
  vorrat : Vorrat
  naechst : Nat
  belegt : List Region
  deriving DecidableEq, Repr

/-- Checked allocation: align the cursor, refuse empty/unaligned/
    over-ceiling/wrapping requests, else hand a fresh capability and
    advance deterministically. -/
def reserviere (s : Reservierer) (len ausr : Nat)
    (l w x : Bool) : Option (Region × Reservierer) :=
  if len = 0 then none
  else match ausricht s.naechst ausr with
  | none => none
  | some start =>
    if start + len ≤ s.vorrat.lo + s.vorrat.umfang ∧
        start + len ≤ 2 ^ 64 ∧ s.vorrat.lo ≤ start then
      let r : Region :=
        { basis := start, len := len, lesbar := l,
          schreibbar := w, ausfuehrbar := x }
      some (r, { s with naechst := start + len, belegt := r :: s.belegt })
    else none

/-- Empty requests are always refused. -/
theorem reserviere_leer_verweigert (s : Reservierer) (ausr : Nat)
    (l w x : Bool) : reserviere s 0 ausr l w x = none := by
  simp [reserviere]

/-- Zero alignment always refuses allocation. -/
theorem reserviere_ausr_null_verweigert (s : Reservierer) (len : Nat)
    (l w x : Bool) (hlen : len ≠ 0) :
    reserviere s len 0 l w x = none := by
  unfold reserviere ausricht
  simp [hlen]

/-- A handed region carries the requested extent and rights. -/
theorem reserviere_ausmass (s : Reservierer) (len ausr : Nat)
    (l w x : Bool) (r : Region) (s' : Reservierer)
    (h : reserviere s len ausr l w x = some (r, s')) :
    r.len = len ∧ r.lesbar = l ∧ r.schreibbar = w ∧
      r.ausfuehrbar = x := by
  unfold reserviere at h
  by_cases hlen : len = 0
  · simp [hlen] at h
  · simp [hlen] at h
    cases hau : ausricht s.naechst ausr with
    | none => simp [hau] at h
    | some start =>
      simp [hau] at h
      by_cases hc : start + len ≤ s.vorrat.lo + s.vorrat.umfang ∧
          start + len ≤ 2 ^ 64 ∧ s.vorrat.lo ≤ start
      · simp [hc] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl, rfl, rfl⟩
      · simp [hc] at h

/-- A handed region lies inside the supplied range with no wrap. -/
theorem reserviere_innerhalb (s : Reservierer) (len ausr : Nat)
    (l w x : Bool) (r : Region) (s' : Reservierer)
    (h : reserviere s len ausr l w x = some (r, s')) :
    innerhalb s.vorrat r = true := by
  unfold reserviere at h
  by_cases hlen : len = 0
  · simp [hlen] at h
  · simp [hlen] at h
    cases hau : ausricht s.naechst ausr with
    | none => simp [hau] at h
    | some start =>
      simp [hau] at h
      by_cases hc : start + len ≤ s.vorrat.lo + s.vorrat.umfang ∧
          start + len ≤ 2 ^ 64 ∧ s.vorrat.lo ≤ start
      · simp [hc] at h
        obtain ⟨rfl, rfl⟩ := h
        unfold innerhalb
        simp only [decide_eq_true_eq]
        obtain ⟨hc1, hc2, hc3⟩ := hc
        exact ⟨hc3, hc1, hc2⟩
      · simp [hc] at h

/-- The cursor never moves backwards and never passes the ceiling. -/
theorem reserviere_decke (s : Reservierer) (len ausr : Nat)
    (l w x : Bool) (r : Region) (s' : Reservierer)
    (h : reserviere s len ausr l w x = some (r, s')) :
    s.naechst ≤ s'.naechst ∧
      s'.naechst ≤ s.vorrat.lo + s.vorrat.umfang ∧
      s'.naechst ≤ 2 ^ 64 ∧ s'.vorrat = s.vorrat := by
  unfold reserviere at h
  by_cases hlen : len = 0
  · simp [hlen] at h
  · simp [hlen] at h
    cases hau : ausricht s.naechst ausr with
    | none => simp [hau] at h
    | some start =>
      simp [hau] at h
      by_cases hc : start + len ≤ s.vorrat.lo + s.vorrat.umfang ∧
          start + len ≤ 2 ^ 64 ∧ s.vorrat.lo ≤ start
      · simp [hc] at h
        obtain ⟨rfl, rfl⟩ := h
        have hmono := ausricht_monoton s.naechst ausr start hau
        obtain ⟨hc1, hc2, -⟩ := hc
        refine ⟨by simp_all; omega, ?_, ?_, rfl⟩ <;> simp_all <;> omega
      · simp [hc] at h

/-- The handed region starts at or after the old cursor: it is fresh. -/
theorem reserviere_frisch (s : Reservierer) (len ausr : Nat)
    (l w x : Bool) (r : Region) (s' : Reservierer)
    (h : reserviere s len ausr l w x = some (r, s')) :
    s.naechst ≤ r.basis ∧ s'.naechst = r.basis + r.len ∧
      r ∈ s'.belegt := by
  unfold reserviere at h
  by_cases hlen : len = 0
  · simp [hlen] at h
  · simp [hlen] at h
    cases hau : ausricht s.naechst ausr with
    | none => simp [hau] at h
    | some start =>
      simp [hau] at h
      by_cases hc : start + len ≤ s.vorrat.lo + s.vorrat.umfang ∧
          start + len ≤ 2 ^ 64 ∧ s.vorrat.lo ≤ start
      · simp [hc] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨ausricht_monoton s.naechst ausr start hau, rfl,
          List.mem_cons_self⟩
      · simp [hc] at h

/-- Over-ceiling requests are refused outright. -/
theorem reserviere_voll_verweigert (s : Reservierer) (len ausr : Nat)
    (l w x : Bool) (start : Nat) (hau : ausricht s.naechst ausr = some start)
    (hvoll : s.vorrat.lo + s.vorrat.umfang < start + len) :
    reserviere s len ausr l w x = none := by
  unfold reserviere
  by_cases hlen : len = 0
  · simp [hlen]
  · simp only [hlen, ↓reduceIte, hau]
    rw [if_neg]
    intro hc
    obtain ⟨hc1, -, -⟩ := hc
    omega

/-- A `Nat` offset as a machine address. -/
def natAdresse (n : Nat) : Adresse := BitVec.ofNat 64 n

/-- A `Nat` offset lies in the region extent. -/
def inRegion (r : Region) (a : Nat) : Bool :=
  decide (r.basis ≤ a ∧ a < r.basis + r.len)

/-- Canonical initialisation: zero the bytes of the extent and install
    the declared rights there; everything else is untouched. -/
def initialisiere (m : Speicher) (r : Region) : Speicher :=
  { bytes := fun adr => if inRegion r adr.toNat then BitVec.ofNat 8 0
      else m.bytes adr
    lesbar := fun adr => if inRegion r adr.toNat then r.lesbar
      else m.lesbar adr
    schreibbar := fun adr => if inRegion r adr.toNat then r.schreibbar
      else m.schreibbar adr
    ausfuehrbar := fun adr => if inRegion r adr.toNat then r.ausfuehrbar
      else m.ausfuehrbar adr }

/-- FRAME: outside the extent nothing changes. -/
theorem initialisiere_rahmen_bytes (m : Speicher) (r : Region)
    (x : Adresse) (hx : inRegion r x.toNat = false) :
    (initialisiere m r).bytes x = m.bytes x := by
  simp [initialisiere, hx]

/-- FRAME: outside the extent permissions are unchanged. -/
theorem initialisiere_rahmen_rechte (m : Speicher) (r : Region)
    (x : Adresse) (hx : inRegion r x.toNat = false) :
    (initialisiere m r).lesbar x = m.lesbar x ∧
    (initialisiere m r).schreibbar x = m.schreibbar x ∧
    (initialisiere m r).ausfuehrbar x = m.ausfuehrbar x := by
  simp [initialisiere, hx]

/-- EXTENT: inside the extent the declared rights hold. -/
theorem initialisiere_ausmass_rechte (m : Speicher) (r : Region)
    (x : Adresse) (hx : inRegion r x.toNat = true) :
    (initialisiere m r).lesbar x = r.lesbar ∧
    (initialisiere m r).schreibbar x = r.schreibbar ∧
    (initialisiere m r).ausfuehrbar x = r.ausfuehrbar := by
  simp [initialisiere, hx]

/-- EXTENT: inside the extent bytes are defined zero. -/
theorem initialisiere_ausmass_null (m : Speicher) (r : Region)
    (x : Adresse) (hx : inRegion r x.toNat = true) :
    (initialisiere m r).bytes x = BitVec.ofNat 8 0 := by
  simp [initialisiere, hx]

/-- Every tracked region ends at or before the cursor. -/
def alleUnten (s : Reservierer) : Prop :=
  ∀ r ∈ s.belegt, r.basis + r.len ≤ s.naechst

/-- The empty allocator trivially satisfies the cursor invariant. -/
theorem alleUnten_leer (v : Vorrat) (n : Nat) :
    alleUnten { vorrat := v, naechst := n, belegt := [] } := by
  intro r hr
  simp at hr

/-- A handed region is disjoint from every region below the old cursor,
    so the cursor invariant is preserved by construction. -/
theorem reserviere_disjunkt_unten (s : Reservierer) (len ausr : Nat)
    (l w x : Bool) (r : Region) (s' : Reservierer)
    (h : reserviere s len ausr l w x = some (r, s'))
    (q : Region) (_hq : q ∈ s.belegt)
    (hunter : q.basis + q.len ≤ s.naechst) :
    regionDisjunkt r q = true := by
  have hfr := reserviere_frisch s len ausr l w x r s' h
  obtain ⟨hge, -, -⟩ := hfr
  unfold regionDisjunkt
  simp only [decide_eq_true_eq]
  have hlen : 0 < r.len := by
    have hex := reserviere_ausmass s len ausr l w x r s' h
    obtain ⟨hlen_eq, -, -, -⟩ := hex
    rw [hlen_eq]
    unfold reserviere at h
    by_cases hzero : len = 0
    · simp [hzero] at h
    · omega
  omega

/-- Success preserves the cursor invariant for the old entries. -/
theorem reserviere_haelt_unten (s : Reservierer) (len ausr : Nat)
    (l w x : Bool) (r : Region) (s' : Reservierer)
    (h : reserviere s len ausr l w x = some (r, s'))
    (hinv : alleUnten s) :
    ∀ q ∈ s.belegt, q.basis + q.len ≤ s'.naechst := by
  intro q hq
  have hdeck := reserviere_decke s len ausr l w x r s' h
  obtain ⟨hmono, -, -, -⟩ := hdeck
  have hq := hinv q hq
  omega

/-- Under no-wrap, machine address addition is `Nat` addition. -/
theorem natAdresse_addrs (b i : Nat) (h : b + i < 2 ^ 64) :
    addrOff (natAdresse b) i = natAdresse (b + i) := by
  unfold addrOff natAdresse
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hb : b % 2 ^ 64 = b := Nat.mod_eq_of_lt (by omega)
  have hi : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  rw [hb, hi, Nat.mod_eq_of_lt (by omega)]

/-- The `Nat` address of an offset inside the extent is in the region. -/
theorem inRegion_natAdresse (r : Region) (k : Nat)
    (hk : k < r.len) : inRegion r (r.basis + k) = true := by
  unfold inRegion
  simp only [decide_eq_true_eq]
  omega

/-- An eight-byte writable region answers a full write permission
    through the canonical `schreibbar8` check. -/
theorem initialisiere_schreibbar8 (m : Speicher) (r : Region)
    (hw : r.schreibbar = true) (hlen : 8 ≤ r.len)
    (hwrap : r.basis + 8 ≤ 2 ^ 64) :
    schreibbar8 (initialisiere m r) (natAdresse r.basis) = true := by
  have h7 : ∀ i : Nat, i < 8 →
      (initialisiere m r).schreibbar (addrOff (natAdresse r.basis) i) =
        true := by
    intro i hi
    have hi64 : r.basis + i < 2 ^ 64 := by omega
    have had := natAdresse_addrs r.basis i (by omega)
    have hin : inRegion r ((addrOff (natAdresse r.basis) i).toNat) = true := by
      rw [had]
      show inRegion r ((natAdresse (r.basis + i)).toNat) = true
      unfold natAdresse
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact inRegion_natAdresse r i (by omega)
    have hx := initialisiere_ausmass_rechte m r
      (addrOff (natAdresse r.basis) i) hin
    rw [hx.2.1, hw]
  unfold schreibbar8
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨h7 0 (by decide), h7 1 (by decide)⟩,
    h7 2 (by decide)⟩, h7 3 (by decide)⟩, h7 4 (by decide)⟩,
    h7 5 (by decide)⟩, h7 6 (by decide)⟩, h7 7 (by decide)⟩

/-- An eight-byte readable region answers a full read permission
    through the canonical `lesbar8` check. -/
theorem initialisiere_lesbar8 (m : Speicher) (r : Region)
    (hr : r.lesbar = true) (hlen : 8 ≤ r.len)
    (hwrap : r.basis + 8 ≤ 2 ^ 64) :
    lesbar8 (initialisiere m r) (natAdresse r.basis) = true := by
  have h7 : ∀ i : Nat, i < 8 →
      (initialisiere m r).lesbar (addrOff (natAdresse r.basis) i) =
        true := by
    intro i hi
    have had := natAdresse_addrs r.basis i (by omega)
    have hin : inRegion r ((addrOff (natAdresse r.basis) i).toNat) = true := by
      rw [had]
      show inRegion r ((natAdresse (r.basis + i)).toNat) = true
      unfold natAdresse
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact inRegion_natAdresse r i (by omega)
    have hx := initialisiere_ausmass_rechte m r
      (addrOff (natAdresse r.basis) i) hin
    rw [hx.1, hr]
  unfold lesbar8
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨h7 0 (by decide), h7 1 (by decide)⟩,
    h7 2 (by decide)⟩, h7 3 (by decide)⟩, h7 4 (by decide)⟩,
    h7 5 (by decide)⟩, h7 6 (by decide)⟩, h7 7 (by decide)⟩

/-- Opt-in ceiling-free cursor: no `Vorrat`, only the physical
    64-bit no-wrap check. Failure stays explicit through the
    external `scheitert` flag (the runtime/OS answer, user logic). -/
structure FreiStand where
  naechst : Nat
  deriving DecidableEq, Repr

/-- Ceiling-free allocation: still refuses empty requests, wrapping
    extents and externally failed answers; otherwise hands a region.
    There is deliberately no `Vorrat` ceiling here. -/
def freiReserviere (s : FreiStand) (len : Nat) (scheitert : Bool)
    (l w x : Bool) : Option (Region × FreiStand) :=
  if scheitert then none
  else if len = 0 then none
  else if s.naechst + len ≤ 2 ^ 64 then
    let r : Region :=
      { basis := s.naechst, len := len, lesbar := l,
        schreibbar := w, ausfuehrbar := x }
    some (r, { naechst := s.naechst + len })
  else none

/-- The ceiling-free model still allows failure: every request can refuse. -/
theorem freiReserviere_kann_scheitern (s : FreiStand) (len : Nat)
    (l w x : Bool) : freiReserviere s len true l w x = none := by
  simp [freiReserviere]

/-- The ceiling-free model still refuses empty requests. -/
theorem freiReserviere_leer_verweigert (s : FreiStand)
    (l w x : Bool) : freiReserviere s 0 false l w x = none := by
  simp [freiReserviere]

/-- A ceiling-free success carries the requested length. -/
theorem freiReserviere_ausmass (s : FreiStand) (len : Nat)
    (scheitert : Bool) (l w x : Bool) (r : Region) (s' : FreiStand)
    (h : freiReserviere s len scheitert l w x = some (r, s')) :
    r.len = len ∧ r.basis = s.naechst := by
  unfold freiReserviere at h
  by_cases hs : scheitert = true
  · simp [hs] at h
  · simp [hs] at h
    by_cases hlen : len = 0
    · simp [hlen] at h
    · simp [hlen] at h
      by_cases hw : s.naechst + len ≤ 2 ^ 64
      · simp [hw] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
      · simp [hw] at h

/-- NO STATIC BOUND BELOW THE PHYSICAL WIDTH: every bound `B < 2 ^ 64`
    is exceeded by some successful ceiling-free allocation. This is
    about the missing ceiling only: every single extent still satisfies
    `basis + len ≤ 2 ^ 64`, so no physical unbounded-x86-address claim
    is made here. -/
theorem freiReserviere_ohne_statik_gebunden (B : Nat)
    (hB : B < 2 ^ 64) :
    ∃ (s : FreiStand) (len : Nat) (r : Region) (s' : FreiStand),
      freiReserviere s len false true true false = some (r, s') ∧
        B < r.len := by
  refine ⟨⟨0⟩, B + 1, ⟨0, B + 1, true, true, false⟩,
    ⟨0 + (B + 1)⟩, ?_, by show B < B + 1; omega⟩
  unfold freiReserviere
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h0 : B + 1 ≠ 0 := by omega
  simp only [h0, ↓reduceIte]
  rw [if_pos (by omega : 0 + (B + 1) ≤ 2 ^ 64)]

/-- Witness supplied range: 4 KiB at `0x10000`. -/
def zeugenVorrat : Vorrat := { lo := 65536, umfang := 4096 }

/-- Witness allocator start: empty, cursor at the range base. -/
def zeugenStart : Reservierer :=
  { vorrat := zeugenVorrat, naechst := 65536, belegt := [] }

/-- Witness region: eight readable/writable bytes at the range base. -/
def zeugenRegion : Region :=
  { basis := 65536, len := 8, lesbar := true,
    schreibbar := true, ausfuehrbar := false }

/-- Witness memory: zeroed bytes, no permissions anywhere. -/
def zeugenSpeicherR : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => false
    schreibbar := fun _ => false
    ausfuehrbar := fun _ => false }

/-- SUCCESS PROBE: an eight-byte request is handed at the range base
    and the cursor advances past it (real allocator probe). -/
theorem zeugenReserviere_erfolg :
    reserviere zeugenStart 8 8 true true false =
      some (zeugenRegion,
        { vorrat := zeugenVorrat, naechst := 65544,
          belegt := [zeugenRegion] }) := by
  decide

/-- REFUSAL PROBE: a request past the ceiling is refused (real
    refuse-on-full probe: 8 KiB against a 4 KiB range). -/
theorem zeugenReserviere_voll :
    reserviere zeugenStart 8192 8 true true false = none := by
  decide

/-- A read-only region answers no write permission through the
    canonical check (real permission probe). -/
theorem zeugenSchreibschutz_verweigert :
    schreibbar8
      (initialisiere zeugenSpeicherR
        { basis := 65536, len := 8, lesbar := true,
          schreibbar := false, ausfuehrbar := false })
      (natAdresse 65536) = false := by
  decide

/-- JOINT WITNESS: a nonzero write into the initialised witness region
    goes through, reads back, and observably changes the byte. -/
theorem region_schreibLese_zeuge :
    ∃ (m m' : Speicher) (a : Adresse) (v : Wort),
      v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
        m.bytes a ≠ m'.bytes a := by
  have hwr_perm : schreibbar8 (initialisiere zeugenSpeicherR zeugenRegion)
      (natAdresse 65536) = true :=
    initialisiere_schreibbar8 zeugenSpeicherR zeugenRegion rfl
      (by decide) (by decide)
  have hrd_perm : lesbar8 (initialisiere zeugenSpeicherR zeugenRegion)
      (natAdresse 65536) = true :=
    initialisiere_lesbar8 zeugenSpeicherR zeugenRegion rfl
      (by decide) (by decide)
  have hwr : write64 (initialisiere zeugenSpeicherR zeugenRegion)
      (natAdresse 65536) 42 =
      some { initialisiere zeugenSpeicherR zeugenRegion with
        bytes := writeBytes (initialisiere zeugenSpeicherR zeugenRegion)
          (natAdresse 65536) 42 } := by
    unfold write64
    rw [if_pos hwr_perm]
  refine ⟨initialisiere zeugenSpeicherR zeugenRegion, _,
    natAdresse 65536, 42, by decide, hwr,
    read64_nach_write64 _ _ _ _ hwr hrd_perm, ?_⟩
  have hhit := writeBytesN_hit (initialisiere zeugenSpeicherR zeugenRegion)
    (natAdresse 65536) 42 8 0 (by decide) (by decide)
  rw [addrOff_null] at hhit
  have hnull : (initialisiere zeugenSpeicherR zeugenRegion).bytes
      (natAdresse 65536) = BitVec.ofNat 8 0 := by
    apply initialisiere_ausmass_null
    decide
  show (initialisiere zeugenSpeicherR zeugenRegion).bytes
      (natAdresse 65536) ≠
    writeBytesN (initialisiere zeugenSpeicherR zeugenRegion)
      (natAdresse 65536) 42 8 (natAdresse 65536)
  rw [hnull, hhit]
  decide

/- CUTS:
    - No source correspondence: nothing here claims the regions are the
      lowering of any Gabbro `Arena`/allocator construct, duty, cost or
      template. Dynamic-region/allocator-template correspondence is OPEN.
    - No goal coverage: no `Zielsatz/Spec` statement is touched or claimed.
    - Runtime/OS allocation behaviour (reserve/commit/page-return, clone,
      kernel answers) is user logic with checked contracts, never an
      assumption; the external `scheitert` flag of `freiReserviere` models
      that answer point, not its correctness.
    - No independent word/memory model: everything is over the canonical
      `Typen`/`Speicher` vocabulary (`Adresse`/`Wort`/`Byte`, `read64`/
      `write64`, `addrOff`), which this file does not extend.
    - No concurrency claim: disjointness is sequential footprint
      disjointness; per-access TSO refinement stays with the TSO bridge.
    - No loader/image integration: `Bild.lean` mapping, entries,
      relocations and the loader contract are untouched.
    - No decoder, encoder, instruction semantics, ABI, cost transfer or
      final-image acceptance is proved here.
    - The ceiling-free model loses the static `Nat` bound below `2 ^ 64`
      only; every extent still satisfies `basis + len ≤ 2 ^ 64`, so no
      physical unbounded-x86-address claim is made.
    - `ausr = 0` and `len = 0` are always refused; alignment beyond the
      bump-cursor rounding (e.g. section `ausr` demands) is target data.
-/

#print axioms regionEnde
#print axioms vorratEnde
#print axioms ausricht_monoton
#print axioms ausricht_eins
#print axioms ausricht_null_verweigert
#print axioms reserviere_leer_verweigert
#print axioms reserviere_ausr_null_verweigert
#print axioms reserviere_ausmass
#print axioms reserviere_innerhalb
#print axioms reserviere_decke
#print axioms reserviere_frisch
#print axioms reserviere_voll_verweigert
#print axioms initialisiere_rahmen_bytes
#print axioms initialisiere_rahmen_rechte
#print axioms initialisiere_ausmass_rechte
#print axioms initialisiere_ausmass_null
#print axioms alleUnten_leer
#print axioms reserviere_disjunkt_unten
#print axioms reserviere_haelt_unten
#print axioms natAdresse_addrs
#print axioms inRegion_natAdresse
#print axioms initialisiere_schreibbar8
#print axioms initialisiere_lesbar8
#print axioms freiReserviere_kann_scheitern
#print axioms freiReserviere_leer_verweigert
#print axioms freiReserviere_ausmass
#print axioms freiReserviere_ohne_statik_gebunden
#print axioms zeugenReserviere_erfolg
#print axioms zeugenReserviere_voll
#print axioms zeugenSchreibschutz_verweigert
#print axioms region_schreibLese_zeuge

end Gabbro.Grammatik.X86
