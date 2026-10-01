/-
  Checked stack frames and ABI memory obligations (lane 309).

  Frame extents, 16-byte call-boundary alignment, spill/callee-save/stack-arg
  layout and argument/result carriage over the canonical `Speicher` of
  `Grammatik.X86.Typen`/`Speicher`, using the shared `write64`/`read64`.
  No second register, instruction or memory model is created here; `schritt`
  semantics is never duplicated. Callee-save/entry contracts and external
  ABI byte correspondence stay OPEN (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- A checked stack frame: byte base plus depth, over canonical addresses. -/
structure Rahmen where
  basis : Nat
  tiefe : Nat
  deriving DecidableEq, Repr

/-- Top (post-frame) address as a natural number. -/
def Rahmen.spitzeNat (r : Rahmen) : Nat := r.basis + r.tiefe

/-- Word-slot count of a frame. -/
def Rahmen.schlitzZahl (r : Rahmen) : Nat := r.tiefe / 8

/-- Byte address of word slot `idx`, as a natural number. -/
def Rahmen.schlitzNat (r : Rahmen) (idx : Nat) : Nat := r.basis + idx * 8

/-- Byte address of word slot `idx` as a machine address. -/
def Rahmen.schlitzAddr (r : Rahmen) (idx : Nat) : Adresse :=
  BitVec.ofNat 64 (r.schlitzNat idx)

/-- Frame top as a machine word (the call-boundary stack pointer). -/
def Rahmen.spitzeWort (r : Rahmen) : Wort :=
  BitVec.ofNat 64 r.spitzeNat

/-- 16-byte call-boundary alignment of a machine address. -/
def ausgerichtet16 (a : Adresse) : Bool := decide (a.toNat % 16 = 0)

/-! ## 1. Checked extents and call-boundary alignment. -/

/-- Checked frame extent: nonzero depth, a multiple of 16 (alignment is
    preserved), the whole frame inside 64 bits, and a 16-aligned base. -/
def rahmenOk (r : Rahmen) : Bool :=
  decide (0 < r.tiefe ∧ r.tiefe % 16 = 0 ∧ r.spitzeNat ≤ 2 ^ 64 ∧
    r.basis % 16 = 0)

/-- An in-bounds slot ends at or before the frame top. -/
theorem schlitzNat_schranke (r : Rahmen) (idx : Nat)
    (hi : idx < r.schlitzZahl) :
    r.schlitzNat idx + 8 ≤ r.spitzeNat := by
  unfold Rahmen.schlitzZahl at hi
  unfold Rahmen.schlitzNat Rahmen.spitzeNat
  omega

/-- An in-bounds slot address reads back as its natural number. -/
theorem schlitz_toNat (r : Rahmen) (idx : Nat)
    (hle : r.spitzeNat ≤ 2 ^ 64) (hi : idx < r.schlitzZahl) :
    (r.schlitzAddr idx).toNat = r.schlitzNat idx := by
  have hsch := schlitzNat_schranke r idx hi
  unfold Rahmen.schlitzAddr Rahmen.schlitzNat Rahmen.spitzeNat at *
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

/-- ALIGNMENT: a 16-aligned base with a multiple-of-16 depth gives a
    16-aligned call-boundary top. Uses the depth and the base. -/
theorem spitze_ausgerichtet (r : Rahmen)
    (h16 : r.tiefe % 16 = 0) (hb : r.basis % 16 = 0) :
    ausgerichtet16 r.spitzeWort = true := by
  unfold ausgerichtet16 Rahmen.spitzeWort Rahmen.spitzeNat
  simp only [decide_eq_true_eq, BitVec.toNat_ofNat]
  have hN : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  rw [hN]
  omega

/-! ## 2. Checked frame save/restore over the shared byte memory. -/

/-- Checked word save into frame slot `idx`: refused outside the frame. -/
def sichereWort (m : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort) : Option Speicher :=
  if idx < r.schlitzZahl then write64 m (r.schlitzAddr idx) v else none

/-- Checked word load from frame slot `idx`: refused outside the frame. -/
def ladeWort (m : Speicher) (r : Rahmen) (idx : Nat) : Option Wort :=
  if idx < r.schlitzZahl then read64 m (r.schlitzAddr idx) else none

/-- ROUND-TRIP: a saved word loads back through a readable slot. Needs
    readability besides writability, since the permissions are independent. -/
theorem sichere_lade_rundreise (m m' : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort) (hb : idx < r.schlitzZahl)
    (hwr : sichereWort m r idx v = some m')
    (hrd : lesbar8 m (r.schlitzAddr idx) = true) :
    ladeWort m' r idx = some v := by
  unfold sichereWort at hwr
  rw [if_pos hb] at hwr
  unfold ladeWort
  rw [if_pos hb]
  exact read64_nach_write64 m m' (r.schlitzAddr idx) v hwr hrd

/-- BOUNDS REFUSAL: a slot past the frame saves nothing. -/
theorem sichereWort_ausserhalb (m : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort) (h : r.schlitzZahl ≤ idx) :
    sichereWort m r idx v = none := by
  unfold sichereWort
  rw [if_neg (Nat.not_lt.mpr h)]

/-- PERMISSION REFUSAL: a write-protected slot saves nothing. -/
theorem sichereWort_verweigert (m : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort) (hb : idx < r.schlitzZahl)
    (h : schreibbar8 m (r.schlitzAddr idx) = false) :
    sichereWort m r idx v = none := by
  unfold sichereWort
  rw [if_pos hb]
  exact write64_verweigert m (r.schlitzAddr idx) v h

/-- A save preserves every permission: only bytes change. -/
theorem sichereWort_erhaelt_berechtigungen (m m' : Speicher) (r : Rahmen)
    (idx : Nat) (v : Wort) (hb : idx < r.schlitzZahl)
    (hwr : sichereWort m r idx v = some m') :
    m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
      m'.ausfuehrbar = m.ausfuehrbar := by
  unfold sichereWort at hwr
  rw [if_pos hb] at hwr
  exact write64_erhaelt_berechtigungen m (r.schlitzAddr idx) v m' hwr

/-- A save changes nothing outside its eight slot bytes. -/
theorem sichereWort_rahmen (m m' : Speicher) (r : Rahmen) (idx : Nat)
    (x : Adresse) (v : Wort) (hb : idx < r.schlitzZahl)
    (hwr : sichereWort m r idx v = some m')
    (haussen : ∀ k : Nat, k < 8 → x ≠ addrOff (r.schlitzAddr idx) k) :
    m'.bytes x = m.bytes x := by
  unfold sichereWort at hwr
  rw [if_pos hb] at hwr
  exact write64_rahmen m m' (r.schlitzAddr idx) x v hwr haussen

/-- A load from a disjoint slot survives a save elsewhere. -/
theorem ladeWort_rahmen (m m' : Speicher) (r : Rahmen) (idx j : Nat)
    (v : Wort) (hb : idx < r.schlitzZahl) (hbj : j < r.schlitzZahl)
    (hwr : sichereWort m r idx v = some m')
    (hdis : Disjunkt (r.schlitzAddr idx) (r.schlitzAddr j)) :
    ladeWort m' r j = ladeWort m r j := by
  unfold sichereWort at hwr
  rw [if_pos hb] at hwr
  unfold ladeWort
  rw [if_pos hbj, if_pos hbj]
  exact read64_rahmen m m' (r.schlitzAddr idx) (r.schlitzAddr j) v
    hwr hdis

/-! ## 3. Fresh and disjoint slots: no slot shares a byte with another. -/

/-- Two slots of one frame are footprint-disjoint. Needs both bounds, the
    inequality and the frame bound. -/
theorem schlitz_disjunkt (r : Rahmen) (i j : Nat)
    (hi : i < r.schlitzZahl) (hj : j < r.schlitzZahl)
    (hne : i ≠ j) (hle : r.spitzeNat ≤ 2 ^ 64) :
    Disjunkt (r.schlitzAddr i) (r.schlitzAddr j) := by
  have hsi := schlitzNat_schranke r i hi
  have hsj := schlitzNat_schranke r j hj
  have hti := schlitz_toNat r i hle hi
  have htj := schlitz_toNat r j hle hj
  have hOi : OhneUmbruch (r.schlitzAddr i) := by
    unfold OhneUmbruch
    omega
  have hOj : OhneUmbruch (r.schlitzAddr j) := by
    unfold OhneUmbruch
    omega
  have hord : (r.schlitzAddr i).toNat + 8 ≤ (r.schlitzAddr j).toNat ∨
      (r.schlitzAddr j).toNat + 8 ≤ (r.schlitzAddr i).toNat := by
    rw [hti, htj]
    unfold Rahmen.schlitzNat
    by_cases hlt : i < j
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  exact disjunkt_von_intervallen _ _ hOi hOj hord

/-- Two frames are separate: every slot pair is footprint-disjoint. -/
def RahmenGetrennt (r₁ r₂ : Rahmen) : Prop :=
  ∀ i j : Nat, i < r₁.schlitzZahl → j < r₂.schlitzZahl →
    Disjunkt (r₁.schlitzAddr i) (r₂.schlitzAddr j)

/-- Nat-interval separation gives frame separation: caller and callee
    frames share no byte. Uses both bounds and the interval order. -/
theorem rahmen_getrennt_von_intervallen (r₁ r₂ : Rahmen)
    (hle₁ : r₁.spitzeNat ≤ 2 ^ 64) (hle₂ : r₂.spitzeNat ≤ 2 ^ 64)
    (h : r₁.spitzeNat ≤ r₂.basis ∨ r₂.spitzeNat ≤ r₁.basis) :
    RahmenGetrennt r₁ r₂ := by
  intro i j hi hj
  have hti := schlitz_toNat r₁ i hle₁ hi
  have htj := schlitz_toNat r₂ j hle₂ hj
  have hsi := schlitzNat_schranke r₁ i hi
  have hsj := schlitzNat_schranke r₂ j hj
  have hOi : OhneUmbruch (r₁.schlitzAddr i) := by
    unfold OhneUmbruch
    omega
  have hOj : OhneUmbruch (r₂.schlitzAddr j) := by
    unfold OhneUmbruch
    omega
  have hord : (r₁.schlitzAddr i).toNat + 8 ≤ (r₂.schlitzAddr j).toNat ∨
      (r₂.schlitzAddr j).toNat + 8 ≤ (r₁.schlitzAddr i).toNat := by
    rw [hti, htj]
    unfold Rahmen.schlitzNat at hsi hsj ⊢
    unfold Rahmen.spitzeNat at hsi hsj h
    omega
  exact disjunkt_von_intervallen _ _ hOi hOj hord

/-! ## 4. Frame layout: spills, callee-save words, stack arguments. -/

/-- Frame layout: spill slots, callee-save slots, stack-passed argument words,
    laid out back to back from the frame base. -/
structure Belegung where
  spill : Nat
  gerettet : Nat
  stapelArgs : Nat
  deriving DecidableEq, Repr

/-- Words the layout needs. -/
def Belegung.braucht (b : Belegung) : Nat :=
  b.spill + b.gerettet + b.stapelArgs

/-- The layout fits the frame. -/
def Belegung.passt (b : Belegung) (r : Rahmen) : Bool :=
  decide (b.braucht * 8 ≤ r.tiefe)

/-- Slot index of the `i`-th callee-save word. Spill words live at the
    bare indices `i` below `b.spill`, so they need no offset function. -/
def Belegung.gerettetIdx (b : Belegung) (i : Nat) : Nat := b.spill + i

/-- Slot index of the `i`-th stack-passed argument word. -/
def Belegung.stapelArgIdx (b : Belegung) (i : Nat) : Nat :=
  b.spill + b.gerettet + i

/-- Two index ranges that do not overlap name disjoint slots. The generic
    shape behind spill/callee-save/argument separation. -/
theorem bereich_getrennt (r : Rahmen) (a₁ e₁ a₂ e₂ i j : Nat)
    (h₁ : a₁ ≤ i) (h₁' : i < e₁) (h₂ : a₂ ≤ j) (h₂' : j < e₂)
    (hsep : e₁ ≤ a₂ ∨ e₂ ≤ a₁)
    (hb₁ : e₁ ≤ r.schlitzZahl) (hb₂ : e₂ ≤ r.schlitzZahl)
    (hle : r.spitzeNat ≤ 2 ^ 64) :
    Disjunkt (r.schlitzAddr i) (r.schlitzAddr j) := by
  have hbi : i < r.schlitzZahl := by omega
  have hbj : j < r.schlitzZahl := by omega
  have hne : i ≠ j := by omega
  exact schlitz_disjunkt r i j hbi hbj hne hle

/-- A spill slot shares no byte with a callee-save slot. -/
theorem spill_gerettet_getrennt (b : Belegung) (r : Rahmen) (i j : Nat)
    (hi : i < b.spill) (hj : j < b.gerettet)
    (hpasst : b.braucht * 8 ≤ r.tiefe)
    (hle : r.spitzeNat ≤ 2 ^ 64) :
    Disjunkt (r.schlitzAddr i) (r.schlitzAddr (b.gerettetIdx j)) := by
  unfold Belegung.gerettetIdx Belegung.braucht at *
  have hb : b.spill + b.gerettet ≤ r.schlitzZahl := by
    unfold Rahmen.schlitzZahl
    omega
  exact bereich_getrennt r 0 b.spill b.spill (b.spill + b.gerettet) i
    (b.spill + j) (by omega) hi (by omega) (by omega) (Or.inl (by omega))
    (by omega) hb hle

/-- A callee-save slot shares no byte with a stack-argument slot. -/
theorem gerettet_stapel_getrennt (b : Belegung) (r : Rahmen) (i j : Nat)
    (hi : i < b.gerettet) (hj : j < b.stapelArgs)
    (hpasst : b.braucht * 8 ≤ r.tiefe)
    (hle : r.spitzeNat ≤ 2 ^ 64) :
    Disjunkt (r.schlitzAddr (b.gerettetIdx i))
      (r.schlitzAddr (b.stapelArgIdx j)) := by
  unfold Belegung.gerettetIdx Belegung.stapelArgIdx Belegung.braucht at *
  have hb : b.spill + b.gerettet + b.stapelArgs ≤ r.schlitzZahl := by
    unfold Rahmen.schlitzZahl
    omega
  exact bereich_getrennt r b.spill (b.spill + b.gerettet)
    (b.spill + b.gerettet) (b.spill + b.gerettet + b.stapelArgs)
    (b.spill + i) (b.spill + b.gerettet + j)
    (by omega) (by omega) (by omega) (by omega)
    (Or.inl (by omega)) (by omega) hb hle

/-! ## 5. Argument and result carriage. -/

/-- Register of the `i`-th integer argument (System V order); further
    arguments travel on the stack. -/
def argReg (i : Nat) : Option Register :=
  if i = 0 then some .rdi
  else if i = 1 then some .rsi
  else if i = 2 then some .rdx
  else if i = 3 then some .rcx
  else if i = 4 then some .r8
  else if i = 5 then some .r9
  else none

/-- Operand probe: the first argument travels in `rdi`. -/
theorem argReg_sonde_rdi : argReg 0 = some .rdi := by decide

/-- Operand probe: the sixth argument travels in `r9`. -/
theorem argReg_sonde_r9 : argReg 5 = some .r9 := by decide

/-- The six argument registers are pairwise distinct. -/
theorem argReg_verschieden :
    argReg 0 ≠ argReg 1 ∧ argReg 0 ≠ argReg 2 ∧
    argReg 0 ≠ argReg 3 ∧ argReg 0 ≠ argReg 4 ∧
    argReg 0 ≠ argReg 5 ∧ argReg 1 ≠ argReg 2 ∧
    argReg 1 ≠ argReg 3 ∧ argReg 1 ≠ argReg 4 ∧
    argReg 1 ≠ argReg 5 ∧ argReg 2 ≠ argReg 3 ∧
    argReg 2 ≠ argReg 4 ∧ argReg 2 ≠ argReg 5 ∧
    argReg 3 ≠ argReg 4 ∧ argReg 3 ≠ argReg 5 ∧
    argReg 4 ≠ argReg 5 := by
  decide

/-- The seventh and further arguments travel on the stack, never in a
    register. Uses the lower bound. -/
theorem argReg_ab_sechs (i : Nat) (h : 6 ≤ i) : argReg i = none := by
  unfold argReg
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Slot index of the `i`-th call argument (`i ≥ 6`): stack-carried words
    start behind the register-carried ones. -/
def argStapelIdx (b : Belegung) (i : Nat) : Nat :=
  b.spill + b.gerettet + (i - 6)

/-- A stack-carried argument of an `n`-argument call lies in the frame.
    Uses the argument position, the register count, the declared arity
    and the frame fit. -/
theorem argStapel_schranke (b : Belegung) (r : Rahmen) (i n : Nat)
    (hb : i < n) (h6 : 6 ≤ i) (hfit : b.stapelArgs = n - 6)
    (hpasst : b.braucht * 8 ≤ r.tiefe) :
    argStapelIdx b i < r.schlitzZahl := by
  unfold argStapelIdx Belegung.braucht Rahmen.schlitzZahl at *
  omega

/-- Checked result-word save at a caller address. -/
def sichereErgebnis (m : Speicher) (e : Adresse) (v : Wort)
    : Option Speicher :=
  write64 m e v

/-- Checked result-word load from a caller address. -/
def ladeErgebnis (m : Speicher) (e : Adresse) : Option Wort :=
  read64 m e

/-- RESULT ROUND-TRIP: a saved result word loads back through a readable
    address. -/
theorem sichere_lade_ergebnis_rundreise (m m' : Speicher) (e : Adresse)
    (v : Wort) (hwr : sichereErgebnis m e v = some m')
    (hrd : lesbar8 m e = true) :
    ladeErgebnis m' e = some v := by
  unfold sichereErgebnis at hwr
  unfold ladeErgebnis
  exact read64_nach_write64 m m' e v hwr hrd

/-- A result word at a frame-disjoint address survives a frame save. Uses
    the slot bound, the save and the disjointness. -/
theorem ergebnis_bleibt_vor_rahmen (m m' : Speicher) (r : Rahmen)
    (idx : Nat) (e : Adresse) (v : Wort) (hb : idx < r.schlitzZahl)
    (hwr : sichereWort m r idx v = some m')
    (hdis : Disjunkt (r.schlitzAddr idx) e) :
    ladeErgebnis m' e = ladeErgebnis m e := by
  unfold sichereWort at hwr
  rw [if_pos hb] at hwr
  unfold ladeErgebnis
  exact read64_rahmen m m' (r.schlitzAddr idx) e v hwr hdis

/-! ## 6. Whole-region save/restore. -/

/-- Save a word list into consecutive slots from `ab`. -/
def sichereListe (m : Speicher) (r : Rahmen) (ab : Nat) :
    List Wort → Option Speicher
  | [] => some m
  | v :: vs =>
    match sichereWort m r ab v with
    | none => none
    | some m' => sichereListe m' r (ab + 1) vs

/-- Load `n` words from consecutive slots from `ab`. -/
def ladeListe (m : Speicher) (r : Rahmen) (ab : Nat) :
    Nat → Option (List Wort)
  | 0 => some []
  | n + 1 =>
    match ladeWort m r ab with
    | none => none
    | some v =>
      match ladeListe m r (ab + 1) n with
      | none => none
      | some vs => some (v :: vs)

/-- Saving nothing changes nothing. -/
theorem sichereListe_leer (m : Speicher) (r : Rahmen) (ab : Nat) :
    sichereListe m r ab [] = some m := rfl

/-- Loading nothing loads nothing. -/
theorem ladeListe_null (m : Speicher) (r : Rahmen) (ab : Nat) :
    ladeListe m r ab 0 = some [] := rfl

/-- A region write preserves the read at a slot it never touches. Uses
    the frame bound, the slot bound, the fit, the separation and the write. -/
theorem sichereListe_rahmen_fremd (m m' : Speicher) (r : Rahmen) (ab : Nat)
    (vs : List Wort) (k : Nat)
    (hle : r.spitzeNat ≤ 2 ^ 64)
    (hk : k < r.schlitzZahl)
    (hfit : ∀ j, j < vs.length → ab + j < r.schlitzZahl)
    (hsep : ∀ j, j < vs.length → k ≠ ab + j)
    (hwr : sichereListe m r ab vs = some m') :
    read64 m' (r.schlitzAddr k) = read64 m (r.schlitzAddr k) := by
  induction vs generalizing ab m m' with
  | nil =>
    cases hwr
    rfl
  | cons w ws ih =>
    unfold sichereListe at hwr
    cases hmw : sichereWort m r ab w with
    | none =>
      simp only [hmw] at hwr
      cases hwr
    | some m₁ =>
      simp only [hmw] at hwr
      have h0 : 0 < (w :: ws).length := by simp
      have hb : ab + 0 < r.schlitzZahl := hfit 0 h0
      simp only [Nat.add_zero] at hb
      have hne : ab ≠ k := fun he => hsep 0 h0 he.symm
      have hdis : Disjunkt (r.schlitzAddr ab) (r.schlitzAddr k) :=
        schlitz_disjunkt r ab k hb hk hne hle
      have hmw64 : write64 m (r.schlitzAddr ab) w = some m₁ := by
        unfold sichereWort at hmw
        rw [if_pos hb] at hmw
        exact hmw
      have hstep : read64 m₁ (r.schlitzAddr k) =
          read64 m (r.schlitzAddr k) :=
        read64_rahmen m m₁ (r.schlitzAddr ab) (r.schlitzAddr k) w hmw64
          hdis
      have hfit' : ∀ j, j < ws.length → (ab + 1) + j < r.schlitzZahl := by
        intro j hj
        have hj' : j + 1 < (w :: ws).length := by
          simp only [List.length_cons] at hj ⊢
          omega
        have h := hfit (j + 1) hj'
        omega
      have hsep' : ∀ j, j < ws.length → k ≠ (ab + 1) + j := by
        intro j hj
        have hj' : j + 1 < (w :: ws).length := by
          simp only [List.length_cons] at hj ⊢
          omega
        have h := hsep (j + 1) hj'
        omega
      have ihrest := ih m₁ m' (ab + 1) hfit' hsep' hwr
      rw [hstep] at ihrest
      exact ihrest

/-- WHOLE-REGION ROUND-TRIP: a saved word list loads back. Uses the frame
    bound, the fit, the write and the readability of every slot. -/
theorem sichereListe_ladeListe_rundreise (m m' : Speicher) (r : Rahmen)
    (ab : Nat) (vs : List Wort)
    (hle : r.spitzeNat ≤ 2 ^ 64)
    (hfit : ∀ j, j < vs.length → ab + j < r.schlitzZahl)
    (hwr : sichereListe m r ab vs = some m')
    (hrd : ∀ j, j < vs.length → lesbar8 m (r.schlitzAddr (ab + j)) = true) :
    ladeListe m' r ab vs.length = some vs := by
  induction vs generalizing ab m m' with
  | nil =>
    cases hwr
    rfl
  | cons v ws ih =>
    unfold sichereListe at hwr
    cases hmw : sichereWort m r ab v with
    | none =>
      simp only [hmw] at hwr
      cases hwr
    | some m₁ =>
      simp only [hmw] at hwr
      have h0 : 0 < (v :: ws).length := by simp
      have hb : ab < r.schlitzZahl := by
        have h := hfit 0 h0
        simpa using h
      have hrd0 : lesbar8 m (r.schlitzAddr ab) = true := by
        have h := hrd 0 h0
        simpa using h
      have hmw64 : write64 m (r.schlitzAddr ab) v = some m₁ := by
        unfold sichereWort at hmw
        rw [if_pos hb] at hmw
        exact hmw
      have hread1 : read64 m₁ (r.schlitzAddr ab) = some v :=
        read64_nach_write64 m m₁ (r.schlitzAddr ab) v hmw64 hrd0
      have hsep : ∀ j, j < ws.length → ab ≠ (ab + 1) + j :=
        fun j _ => by omega
      have hfit_tail : ∀ j, j < ws.length → (ab + 1) + j < r.schlitzZahl := by
        intro j hj
        have hj' : j + 1 < (v :: ws).length := by
          simp only [List.length_cons] at hj ⊢
          omega
        have h := hfit (j + 1) hj'
        omega
      have hkeep : read64 m' (r.schlitzAddr ab) =
          read64 m₁ (r.schlitzAddr ab) :=
        sichereListe_rahmen_fremd m₁ m' r (ab + 1) ws ab hle hb
          hfit_tail hsep hwr
      have hread : read64 m' (r.schlitzAddr ab) = some v := by
        rw [hkeep]
        exact hread1
      have hhead : ladeWort m' r ab = some v := by
        unfold ladeWort
        rw [if_pos hb]
        exact hread
      have hrd' : ∀ j, j < ws.length →
          lesbar8 m₁ (r.schlitzAddr ((ab + 1) + j)) = true := by
        intro j hj
        have hj' : j + 1 < (v :: ws).length := by
          simp only [List.length_cons] at hj ⊢
          omega
        have h2 := hrd (j + 1) hj'
        have hperm := lesbar8_nach_schreiben m m₁ (r.schlitzAddr ab)
          (r.schlitzAddr ((ab + 1) + j)) v hmw64
        rw [hperm]
        have heq : ab + (j + 1) = (ab + 1) + j := by omega
        rw [heq] at h2
        exact h2
      have ihtail := ih m₁ m' (ab + 1) hfit_tail hwr hrd'
      have hlen : (v :: ws).length = ws.length + 1 := rfl
      simp only [hlen, ladeListe, hhead, ihtail]

/- CUTS:
    - No instruction semantics, decoder, image mapping, TSO bridge, source
      correspondence, cost transfer or final-image acceptance is proved here.
    - Callee-save/entry contracts and external ABI byte correspondence are
      OPEN: this file states checked memory obligations only.
    - No Linux-specific mechanism: no stack sizes, guard pages, clone flags
      or syscall numbers appear here.
-/

end Gabbro.Grammatik.X86
