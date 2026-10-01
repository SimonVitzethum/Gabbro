/-
  File:      Grammatik/X86/SourceMemory.lean
  Subject:   Source world/table values to target byte representation (lane 570).

  The ONE small generic representation interface between real source
  `Deklaration`/`World` table carriers and accepted `TableLayout`/`Speicher`
  bytes, for the bounded integer fragment (one `.int lo hi` slot stored as
  one little-endian 8-byte word). Source writes reuse the actual
  `execStmt` table-write operation (`World.schreibSlot`, unfolded by
  `execStmt_assignSlot`); target writes reuse `write64`/`read64`; checked
  premises reuse `repOk` (range/width/region) and `layoutOk`/`regionDisjunkt`.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.Parser.Uebersetze
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Regionen
import Grammatik.X86.TableLayout

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze

/-- A source integer value as a target word: the (nonnegative) number as
    64 bits. Faithful exactly when `0 <= v.n` and `v.n < 2 ^ 64`
    (`zahlWort_wortZahl`); outside that the mapping is lossy by
    construction (`Int.toNat` clips negatives, `BitVec.ofNat` wraps). -/
def zahlWort {lo hi : Int} (v : Zahl lo hi) : Wort :=
  BitVec.ofNat 64 v.n.toNat

/-- A target word back as a source integer: `some` exactly when the
    unsigned value lies in `lo .. hi`. The `none` case is the checked
    out-of-range refusal of the interface. -/
def wortZahl (lo hi : Int) (w : Wort) : Option (Zahl lo hi) :=
  if h : lo ≤ Int.ofNat w.toNat ∧ Int.ofNat w.toNat ≤ hi then
    some ⟨Int.ofNat w.toNat, h.1, h.2⟩
  else none

/-- ROUNDTRIP: a source value in a nonnegative range below `2 ^ 64`
    survives the word mapping. Uses both bounds: `hLo` for the `toNat`
    inversion, `hHi` for the `ofNat` modulo identity. -/
theorem zahlWort_wortZahl {lo hi : Int} (v : Zahl lo hi)
    (hLo : 0 ≤ lo) (hHi : hi < 2 ^ 64) :
    wortZahl lo hi (zahlWort v) = some v := by
  obtain ⟨n, hlo, hhi⟩ := v
  have hnn : 0 ≤ n := by omega
  have hnn2 : 0 ≤ hi := by omega
  have hcast : ((2 ^ 64 : Nat) : Int) = (2 ^ 64 : Int) := by decide
  have hlt : hi.toNat < 2 ^ 64 := by
    have h2 : hi < ((2 ^ 64 : Nat) : Int) := by
      rw [hcast]; exact hHi
    exact (Int.toNat_lt hnn2).mpr h2
  have hmod : n.toNat % 2 ^ 64 = n.toNat :=
    Nat.mod_eq_of_lt (by
      have hle : n.toNat ≤ hi.toNat := Int.toNat_le_toNat hhi
      omega)
  simp only [wortZahl, zahlWort, BitVec.toNat_ofNat, hmod]
  have hnn' : Int.ofNat n.toNat = n := Int.toNat_of_nonneg hnn
  simp only [hnn']
  rw [dif_pos ⟨hlo, hhi⟩]

/-- The ONE checked admission Bool of the interface: range (`0 <= lo`,
    `hi < 2 ^ 64`), width (an `.int` field, never `bool`/sums/FP/pointers)
    and region (the 8-byte slot fits the layout entry extent with no
    64-bit wrap). A Rust layout hint is re-decided against this, never a
    premise. -/
def repOk (ty : Ty) (base len off : Nat) : Bool :=
  match ty with
  | .int lo hi =>
    decide (0 ≤ lo ∧ hi < 2 ^ 64 ∧ off + 8 ≤ len ∧ base + off + 8 ≤ 2 ^ 64)
  | _ => false

/-- An accepted check yields exactly the range/width/region facts the
    preservation theorems consume. -/
theorem repOk_klingt {lo hi : Int} {base len off : Nat}
    (h : repOk (.int lo hi) base len off = true) :
    0 ≤ lo ∧ hi < 2 ^ 64 ∧ off + 8 ≤ len ∧ base + off + 8 ≤ 2 ^ 64 := by
  unfold repOk at h
  simp only [decide_eq_true_eq] at h
  exact h

/-- Byte offset of field `fi` inside one row: the accepted `typWeite`
    (bool 1 byte, else one word) of every earlier field. -/
def feldOff (tab : UTab) (fi : Nat) : Nat :=
  (tab.felder.take fi).foldl
    (fun acc p => acc + if tab.bools.contains p.1 then 1 else 8) 0

/-- Byte offset of slot `(row, fi)` inside the table extent. -/
def slotOff (tab : UTab) (row fi : Nat) : Nat :=
  row * zeilenWeite tab + feldOff tab fi

/-- Target address of the slot: layout base plus slot offset. -/
def slotAddr (base off : Nat) : Adresse := natAdresse (base + off)

/-- THE REPRESENTATION: the target 8-byte word at `a` is exactly the
    source integer held in slot `(t, k, f)`. The stable producer/consumer
    interface: the compiler (producer) establishes it per slot write, the
    validator/TSO bridge (consumer) assumes only this equation plus the
    checked `repOk`/`layoutOk` Bools. Sums, floats, bools, globals and
    function pointers have no representation (explicit cuts). -/
def RepSlot {D : Deklaration} (t : D.Tab) (k : Int) (f : D.Feld t)
    (lo hi : Int) (hT : D.typ t f = .int lo hi)
    (a : Adresse) (m : Speicher) (σ : World D) : Prop :=
  read64 m a = some (zahlWort
    (cast (congrArg (Wert D) hT) (σ.slots t k f) : Wert D (.int lo hi)))

/-- A source slot write lands at its own carrier: the exact operation
    `execStmt` performs for `.assignSlot` (see `execStmt_assignSlot`).
    The `merke` bridge is `rfl` (trace entries touch only `spur`;
    `Koernung.schreibSlot_slots_same` is the same fact). -/
theorem schreibSlot_hit {D : Deklaration} (σ : World D) (t : D.Tab)
    (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) :
    (σ.schreibSlot t Λ k f v).slots t k f = v := by
  have hss : (σ.schreibSlot t Λ k f v).slots t k f =
      (σ.storeSlot t k f v).slots t k f := rfl
  rw [hss]
  simp [World.storeSlot]

/-- A source slot write leaves a different table untouched. -/
theorem schreibSlot_fremd_tab {D : Deklaration} (σ : World D) (t : D.Tab)
    (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f))
    (t2 : D.Tab) (k2 : Int) (f2 : D.Feld t2)
    (ht : t2 ≠ t) :
    (σ.schreibSlot t Λ k f v).slots t2 k2 f2 = σ.slots t2 k2 f2 := by
  have hss : (σ.schreibSlot t Λ k f v).slots t2 k2 f2 =
      (σ.storeSlot t k f v).slots t2 k2 f2 := rfl
  rw [hss]
  simp [World.storeSlot, ht]

/-- A source slot write leaves a different row of the same table
    untouched. -/
theorem schreibSlot_fremd_schluessel {D : Deklaration} (σ : World D)
    (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f))
    (k2 : Int) (f2 : D.Feld t)
    (hk : k2 ≠ k) :
    (σ.schreibSlot t Λ k f v).slots t k2 f2 = σ.slots t k2 f2 := by
  have hss : (σ.schreibSlot t Λ k f v).slots t k2 f2 =
      (σ.storeSlot t k f v).slots t k2 f2 := rfl
  rw [hss]
  simp [World.storeSlot, hk]

/-- A source slot write leaves a different field of the same slot
    untouched. -/
theorem schreibSlot_fremd_feld {D : Deklaration} (σ : World D) (t : D.Tab)
    (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f))
    (k2 : Int) (f2 : D.Feld t)
    (hk : k2 = k) (hf : f2 ≠ f) :
    (σ.schreibSlot t Λ k f v).slots t k2 f2 = σ.slots t k2 f2 := by
  subst hk
  have hss : (σ.schreibSlot t Λ k2 f v).slots t k2 f2 =
      (σ.storeSlot t k2 f v).slots t k2 f2 := rfl
  rw [hss]
  simp [World.storeSlot, hf]

/-- DISJOINT PRESERVATION (other table): a source write to one carrier
    and a target word write into a disjoint footprint preserve the
    representation of every carrier of another table. Every premise is
    used: `hSrc` + `ht` move the source side, `hRep2` is the carried
    fact, `hTgt` + `hDis` move the target side. -/
theorem rep_fremd_tab {D : Deklaration}
    (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f))
    (t2 : D.Tab) (k2 : Int) (f2 : D.Feld t2)
    (lo2 hi2 : Int) (hT2 : D.typ t2 f2 = .int lo2 hi2)
    (ht : t2 ≠ t)
    (σL : World D) (hSrc : σL = σ.schreibSlot t Λ k f v)
    (a1 a2 : Adresse) (m m' : Speicher) (w : Wort)
    (hRep2 : RepSlot t2 k2 f2 lo2 hi2 hT2 a2 m σ)
    (hTgt : write64 m a1 w = some m')
    (hDis : Disjunkt a1 a2) :
    RepSlot t2 k2 f2 lo2 hi2 hT2 a2 m' σL := by
  unfold RepSlot at hRep2 ⊢
  rw [hSrc, schreibSlot_fremd_tab σ t Λ k f v t2 k2 f2 ht,
    read64_rahmen m m' a1 a2 w hTgt hDis]
  exact hRep2

/-- DISJOINT PRESERVATION (other row): the same, for another row of the
    written table. -/
theorem rep_fremd_schluessel {D : Deklaration}
    (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f))
    (k2 : Int) (f2 : D.Feld t)
    (lo2 hi2 : Int) (hT2 : D.typ t f2 = .int lo2 hi2)
    (hk : k2 ≠ k)
    (σL : World D) (hSrc : σL = σ.schreibSlot t Λ k f v)
    (a1 a2 : Adresse) (m m' : Speicher) (w : Wort)
    (hRep2 : RepSlot t k2 f2 lo2 hi2 hT2 a2 m σ)
    (hTgt : write64 m a1 w = some m')
    (hDis : Disjunkt a1 a2) :
    RepSlot t k2 f2 lo2 hi2 hT2 a2 m' σL := by
  unfold RepSlot at hRep2 ⊢
  rw [hSrc, schreibSlot_fremd_schluessel σ t Λ k f v k2 f2 hk,
    read64_rahmen m m' a1 a2 w hTgt hDis]
  exact hRep2

/-- DISJOINT PRESERVATION (other field): the same, for another field of
    the written slot. -/
theorem rep_fremd_feld {D : Deklaration}
    (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f))
    (k2 : Int) (f2 : D.Feld t)
    (lo2 hi2 : Int) (hT2 : D.typ t f2 = .int lo2 hi2)
    (hk : k2 = k) (hf : f2 ≠ f)
    (σL : World D) (hSrc : σL = σ.schreibSlot t Λ k f v)
    (a1 a2 : Adresse) (m m' : Speicher) (w : Wort)
    (hRep2 : RepSlot t k2 f2 lo2 hi2 hT2 a2 m σ)
    (hTgt : write64 m a1 w = some m')
    (hDis : Disjunkt a1 a2) :
    RepSlot t k2 f2 lo2 hi2 hT2 a2 m' σL := by
  unfold RepSlot at hRep2 ⊢
  rw [hSrc, schreibSlot_fremd_feld σ t Λ k f v k2 f2 hk hf,
    read64_rahmen m m' a1 a2 w hTgt hDis]
  exact hRep2

/-- LAYOUT DISJOINTNESS: two accepted disjoint layout entries give
    disjoint 8-byte slot footprints. This feeds `rep_fremd_bleibt` from
    the decided `layoutOk`/`repOk` checks instead of an assumed
    disjointness: `hReg` orders the extents, `hLen1`/`hLen2` keep each
    footprint inside its extent, `hWrap1`/`hWrap2` keep machine addition
    Nat addition. -/
theorem disjunkt_von_layout (e1 e2 : TabLayout)
    (off1 off2 : Nat)
    (hReg : regionDisjunkt (alsRegion e1) (alsRegion e2) = true)
    (hLen1 : off1 + 8 ≤ e1.len) (hLen2 : off2 + 8 ≤ e2.len)
    (hWrap1 : e1.basis + off1 + 8 ≤ 2 ^ 64)
    (hWrap2 : e2.basis + off2 + 8 ≤ 2 ^ 64) :
    Disjunkt (slotAddr e1.basis off1) (slotAddr e2.basis off2) := by
  have g1 : ∀ i : Nat, i < 8 →
      (addrOff (slotAddr e1.basis off1) i).toNat = e1.basis + off1 + i := by
    intro i hi
    have hlt : e1.basis + off1 + i < 2 ^ 64 := by omega
    unfold slotAddr natAdresse addrOff
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : e1.basis + off1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
      Nat.mod_eq_of_lt hlt]
  have g2 : ∀ j : Nat, j < 8 →
      (addrOff (slotAddr e2.basis off2) j).toNat = e2.basis + off2 + j := by
    intro j hj
    have hlt : e2.basis + off2 + j < 2 ^ 64 := by omega
    unfold slotAddr natAdresse addrOff
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : e2.basis + off2 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
      Nat.mod_eq_of_lt hlt]
  have e1n : (slotAddr e1.basis off1).toNat = e1.basis + off1 := by
    unfold slotAddr natAdresse
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : e1.basis + off1 < 2 ^ 64)]
  have e2n : (slotAddr e2.basis off2).toNat = e2.basis + off2 := by
    unfold slotAddr natAdresse
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : e2.basis + off2 < 2 ^ 64)]
  have hU1 : OhneUmbruch (slotAddr e1.basis off1) := by
    unfold OhneUmbruch
    rw [e1n]; omega
  have hU2 : OhneUmbruch (slotAddr e2.basis off2) := by
    unfold OhneUmbruch
    rw [e2n]; omega
  have hReg' : e1.basis + e1.len ≤ e2.basis ∨
      e2.basis + e2.len ≤ e1.basis := by
    unfold regionDisjunkt alsRegion at hReg
    exact of_decide_eq_true hReg
  have hInt : (slotAddr e1.basis off1).toNat + 8 ≤
        (slotAddr e2.basis off2).toNat ∨
      (slotAddr e2.basis off2).toNat + 8 ≤
        (slotAddr e1.basis off1).toNat := by
    rw [e1n, e2n]
    omega
  intro i j hi hj he
  exact (disjunkt_von_intervallen _ _ hU1 hU2 hInt i j hi hj he).elim

/-- MAIN STEP PRESERVATION: one actual source table-write step
    (`Stmt.assignSlot` through `execStmt`) together with the matching
    target word write preserves the representation at the written slot,
    and the written bytes parse back to the source value. Every premise
    is used: `hT` links the field type, `hOk` supplies the checked
    range/width/region bounds, `i`/`e`/`hw`/`hL` are the executed
    statement, `hLese`/`hk`/`hv` name the evaluated index and value,
    `hExec` is the source step, `hTgt` + `hRd` give the target
    read-back. The disjoint carriers are covered by `rep_fremd_tab`,
    `rep_fremd_schluessel` and `rep_fremd_feld`. -/
theorem rep_schritt_bleibt {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (t : D.Tab) (f : D.Feld t)
    (lo hi : Int) (hT : D.typ t f = .int lo hi)
    (base len off : Nat)
    (hOk : repOk (D.typ t f) base len off = true)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ)
    (σL : World D) (hLese : σL = σ.lese Λ (i.orte ++ e.orte))
    (k : Int) (v : Zahl lo hi)
    (hk : (eval σL i σL ρ).n = k)
    (hv : (cast (congrArg (Wert D) hT) (eval σL e σL ρ) :
      Wert D (.int lo hi)) = v)
    (a : Adresse) (m m' : Speicher)
    (σ' : World D) (ρ' : Env D Γ)
    (hExec : execStmt O passes R (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      .ok σ' ρ')
    (hTgt : write64 m a (zahlWort v) = some m')
    (hRd : lesbar8 m a = true) :
    RepSlot t k f lo hi hT a m' σ' ∧
      ∃ w, read64 m' a = some w ∧ wortZahl lo hi w = some v := by
  rw [hT] at hOk
  obtain ⟨hLo, hHi, -, -⟩ := repOk_klingt hOk
  have hU : execStmt O passes R (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      Ausgang.ok
        ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
          (eval (σ.lese Λ (i.orte ++ e.orte)) i
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ)) ρ := by
    simp only [execStmt]
  rw [hU] at hExec
  cases hExec
  rw [← hLese]
  have hHit := schreibSlot_hit σL t Λ (eval σL i σL ρ).n f
    (eval σL e σL ρ)
  rw [hk] at hHit
  unfold RepSlot
  rw [hk, hHit, hv]
  exact ⟨read64_nach_write64 m m' a (zahlWort v) hTgt hRd,
    ⟨_, read64_nach_write64 m m' a (zahlWort v) hTgt hRd,
      zahlWort_wortZahl v hLo hHi⟩⟩

/-- OUT-OF-RANGE REFUSAL: a range reaching `2 ^ 64` is refused by the
    checked admission (the word mapping would wrap). -/
theorem repOk_zu_gross_verweigert :
    repOk (.int 0 (2 ^ 64)) 4096 16 0 = false := by
  decide

/-- WIDTH-MISMATCH REFUSAL: a `bool` field has no word representation. -/
theorem repOk_bool_verweigert :
    repOk .bool 4096 16 0 = false := by
  decide

/-- REGION REFUSAL: a slot past the entry extent is refused. -/
theorem repOk_ausserhalb_verweigert :
    repOk (.int 0 100) 4096 16 16 = false := by
  decide

/-- OVERLAP REFUSAL at region level: overlapping entries share bytes, so
    the `hReg` premise of `disjunkt_von_layout` is refused for them. -/
theorem region_ueberlapp_verweigert :
    regionDisjunkt
      (alsRegion { tab := 0, basis := 4096, len := 16, ausr := 8 })
      (alsRegion { tab := 1, basis := 4104, len := 16, ausr := 8 }) =
      false := by
  decide

/- CUTS:
    - The execStmt-facing main theorem, the refusals and the joint
      witness are still to come.
-/

#print axioms zahlWort
#print axioms wortZahl
#print axioms zahlWort_wortZahl
#print axioms repOk
#print axioms repOk_klingt

end Gabbro.Grammatik.X86
