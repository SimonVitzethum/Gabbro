/-
  File:      Grammatik/Verschachtelt.lean
  Subject:   Nested arrays `[[T; N]; M]` in the model: the DECISION (a
             stated flattening, `M[i][j]` is cell `i*N + j` of a table with
             `count M*N`), its lemmas, the correspondence to C's row-major
             `T a[M][N]`, and a witness.

  THE SURFACE (lane 170, merged 2026-09-14, MUSE-REPORT-170.md): the checker
  proves every index per dimension (`M103`), the shape (`N285`) and the
  rectangularity (`N286`) of a nested literal, and refuses a whole-row
  store (`N287`); the emitter lowers a nested static to `T a[M][N]` and
  `M[i][j]` to `a[i][j]`.

  THE DECISION: flattening, not a product index. The model's arrays are
  tables with `count N` and the index type `.index (count t)`
  (Syntax.lean `Expr.slot`); a product index `Fin M × Fin N` would need a
  new index type in `Ty` and new `Expr` constructors (a Syntax change that
  every semantics file matches on), while the flattening reuses `.index
  (M*N)` and every existing slot lemma unchanged. What the product index
  would carry as types is carried here as theorems:
    * `flach_bereich`  -- the two per-dimension bounds (M103 twice) give a
      valid flat index (`0 ≤ i*N+j < M*N`);
    * `flach_injektiv` -- distinct `(i, j)` are distinct cells (no two
      nested elements alias; rectangularity, N286, is what makes every row
      exactly `N` long);
    * `flach_zerlegung` -- every flat cell is exactly one `(i, j)`.
  `nestIdx` builds the flat index as an ordinary Gabbro expression
  (`i * N + j`, widened to `.index (M*N)`), so `M[i][j]` is `Expr.slot t f
  (nestIdx i j)` and `M[i][j] = v` is `Stmt.assignSlot t f (nestIdx i j) v`.
  A whole-row store has no term (a row is not a value of the model) --
  N287 as a theorem shape.

  THE C SIDE: `a[i][j]` on `T a[M][N]` is `*(*(a + i) + j)` (C11
  6.5.2.1p3-4): the model writes it `ld (idx (idx a i M (N*es)) j N es)`;
  `ev_idx_nested` proves it addresses the same byte as the flat access
  `idx a (i*N + j) (M*N) es` -- row-major, exactly the flattening.
-/
import Grammatik.CFormen

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The flattening, as integer facts -/

/-- The flat index of `M[i][j]` in a nested array with rows of `N`. -/
def flachIndex (N i j : Int) : Int := i * N + j

/-- Per-dimension bounds give a valid flat index. -/
theorem flach_bereich (M N i j : Int) (hi0 : 0 ≤ i) (hiM : i < M) (hj0 : 0 ≤ j) (hjN : j < N) :
    0 ≤ flachIndex N i j ∧ flachIndex N i j < M * N := by
  unfold flachIndex
  have hN : 0 ≤ N := by omega
  have h1 : 0 ≤ i * N := Int.mul_nonneg hi0 hN
  have h2 : i * N ≤ (M - 1) * N := Int.mul_le_mul_of_nonneg_right (by omega) hN
  have e : (M - 1) * N = M * N - N := by rw [Int.sub_mul, Int.one_mul]
  omega

/-- The row of a flat index is its quotient by `N`, the column its
    remainder. -/
theorem flach_div_mod (N i j : Int) (hj0 : 0 ≤ j) (hjN : j < N) :
    flachIndex N i j / N = i ∧ flachIndex N i j % N = j := by
  unfold flachIndex
  have hN : N ≠ 0 := by omega
  constructor
  · rw [Int.add_comm, Int.add_mul_ediv_right _ _ hN, Int.ediv_eq_zero_of_lt hj0 hjN, Int.zero_add]
  · rw [Int.add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hj0 hjN]

/-- Distinct elements are distinct cells: the flattening does not alias. -/
theorem flach_injektiv (N i j i' j' : Int) (hj0 : 0 ≤ j) (hjN : j < N) (hj0' : 0 ≤ j')
    (hjN' : j' < N) (h : flachIndex N i j = flachIndex N i' j') : i = i' ∧ j = j' := by
  obtain ⟨a1, a2⟩ := flach_div_mod N i j hj0 hjN
  obtain ⟨b1, b2⟩ := flach_div_mod N i' j' hj0' hjN'
  rw [h] at a1 a2
  exact ⟨a1.symm.trans b1, a2.symm.trans b2⟩

/-- Every cell of the flat table is exactly one element `(k / N, k % N)`. -/
theorem flach_zerlegung (M N k : Int) (hN : 0 < N) (hk0 : 0 ≤ k) (hkM : k < M * N) :
    k = flachIndex N (k / N) (k % N) ∧ 0 ≤ k / N ∧ k / N < M ∧ 0 ≤ k % N ∧ k % N < N := by
  have hN' : N ≠ 0 := by omega
  refine ⟨?_, Int.ediv_nonneg hk0 (by omega), ?_, Int.emod_nonneg _ hN', Int.emod_lt_of_pos _ hN⟩
  · unfold flachIndex
    have h := Int.emod_add_ediv_mul k N
    rw [Int.add_comm]
    exact h.symm
  · exact Int.ediv_lt_of_lt_mul hN hkM

/-! ## 2. The flat index as a Gabbro expression -/

theorem nestIdx_lo (M N : Nat) (hM : 0 < M) :
    (0 : Int) ≤ imin (imin (0 * (N : Int)) (0 * N)) (imin (((M : Int) - 1) * N) (((M : Int) - 1) * N))
      + 0 := by
  have ha : 0 ≤ ((M : Int) - 1) * N := Int.mul_nonneg (by omega) (by omega)
  simp only [Int.zero_mul, imin]
  split <;> split <;> omega

theorem nestIdx_hi (M N : Nat) (hM : 0 < M) (hN : 0 < N) :
    imax (imax (0 * (N : Int)) (0 * N)) (imax (((M : Int) - 1) * N) (((M : Int) - 1) * N))
      + ((N : Int) - 1) ≤ ((M * N : Nat) : Int) - 1 := by
  have ha : 0 ≤ ((M : Int) - 1) * N := Int.mul_nonneg (by omega) (by omega)
  have e : ((M : Int) - 1) * N = (M : Int) * N - N := by rw [Int.sub_mul, Int.one_mul]
  have e2 : ((M * N : Nat) : Int) = (M : Int) * N := by push_cast; rfl
  simp only [Int.zero_mul, imax]
  split <;> split <;> omega

/-- `M[i][j]`'s cell: `i * N + j`, widened to the flat table's index type. -/
def nestIdx {Γ : Ctx} {Λ : List (Res D)} (M N : Nat) (hM : 0 < M) (hN : 0 < N)
    (i : Expr D Γ Λ (.index (M : Int))) (j : Expr D Γ Λ (.index (N : Int))) :
    Expr D Γ Λ (.index ((M * N : Nat) : Int)) :=
  Expr.weiter (nestIdx_lo M N hM) (nestIdx_hi M N hM hN) (Expr.add (Expr.mul i (Expr.lit N)) j)

/-- The model reads `nestIdx i j` as the flat index. -/
theorem eval_nestIdx {Γ : Ctx} {Λ : List (Res D)} (M N : Nat) (hM : 0 < M) (hN : 0 < N)
    (i : Expr D Γ Λ (.index (M : Int))) (j : Expr D Γ Λ (.index (N : Int))) (σ₀ σ : World D)
    (ρ : Env D Γ) :
    (eval σ₀ (nestIdx M N hM hN i j) σ ρ).n =
      flachIndex N (eval σ₀ i σ ρ).n (eval σ₀ j σ ρ).n := rfl

/-! ## 3. C: row-major `a[i][j]` is the flat access -/

/-- **`a[i][j]` on `T a[M][N]` addresses the flat cell `i*N + j`**: the
    nested element address (row `i` of `M`, `N*es` bytes a row, then
    element `j` of `N`) is the address of element `i*N + j` of `M*N`, from
    any object start `0 ≤ q.off` and indices within their dimensions. -/
theorem ev_idx_nested (L : CLayout) (orc : DevOrc) (fr : Nat) {p ci cj ck : CX} {st : CSt}
    {ρ : CLok} {q : CPtr} {i j : Int} (M N es : Nat) (hq : 0 ≤ q.off)
    (hp : ev L orc fr p st ρ = some (.ptr q, st)) (hi : ev L orc fr ci st ρ = some (.int i, st))
    (hj : ev L orc fr cj st ρ = some (.int j, st))
    (hk : ev L orc fr ck st ρ = some (.int (flachIndex N i j), st))
    (hi0 : 0 ≤ i) (hiM : i < M) (hj0 : 0 ≤ j) (hjN : j < N) :
    ev L orc fr (.idx (.idx p ci M (N * es)) cj N es) st ρ =
      ev L orc fr (.idx p ck (M * N) es) st ρ := by
  obtain ⟨hb0, hbM⟩ := flach_bereich M N i j hi0 hiM hj0 hjN
  have hflat : (0 ≤ flachIndex N i j ∧ flachIndex N i j < ((M * N : Nat) : Int)) := by
    refine ⟨hb0, ?_⟩; push_cast; exact hbM
  simp only [ev, hp, hi, hk]
  rw [if_pos ⟨hi0, hiM⟩, if_pos hflat]
  have hoff : 0 ≤ i * ((N * es : Nat) : Int) := Int.mul_nonneg hi0 (by omega)
  have hsum : i * ((N * es : Nat) : Int) + j * (es : Int) = flachIndex N i j * (es : Int) := by
    unfold flachIndex; push_cast
    rw [Int.add_mul, Int.mul_assoc]
  cases h1 : ptrAdd L q (i * ((N * es : Nat) : Int)) 1 with
  | some q1 =>
      simp only []
      rw [hj]
      simp only []
      rw [if_pos ⟨hj0, hjN⟩, ptrAdd_add h1, hsum]
  | none =>
      simp only []
      -- the row is outside the object, so is the element (it lies further in)
      have : ptrAdd L q (flachIndex N i j * (es : Int)) 1 = none := by
        unfold ptrAdd at h1 ⊢
        cases hL : L q.blk with
        | none => rfl
        | some B =>
            rw [hL] at h1
            dsimp only at h1 ⊢
            have hn : ¬ (0 ≤ q.off + i * ((N * es : Nat) : Int) * ((1 : Nat) : Int) ∧
                q.off + i * ((N * es : Nat) : Int) * ((1 : Nat) : Int) ≤ (B.lay.size : Int)) := by
              intro hc; rw [if_pos hc] at h1; exact absurd h1 (by simp)
            have hj' : 0 ≤ j * (es : Int) := Int.mul_nonneg hj0 (by omega)
            rw [if_neg]
            intro hc
            apply hn
            simp only [Int.natCast_one, Int.mul_one] at hc ⊢
            rw [← hsum] at hc
            omega
      rw [this]

/-! ## 4. Witness: `[[u32; 4]; 3]`, `M[1][2] = 7`, read back -/

/-- The one function's signature: writes the table. -/
def nvSig : Signatur Unit Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun g => nomatch g
  konsumiert := []
  produziert := []

/-- One table `M`: 12 cells (`[[u32; 4]; 3]` flattened), one field `u32`. -/
def nvD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 12
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 4294967295
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun _ => false
  ggeteilt := fun g => nomatch g
  Lock := Empty
  decLock := inferInstance
  rang := fun L => L.elim
  maskiert := fun L => L.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun _ => []
  gbraucht := fun g => nomatch g
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => nvSig
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

abbrev nvV : Vertrag nvD := vertragVon nvD ()

theorem nvDarf : darf nvD () [] := fun _ h => nomatch h

/-- `1` as a row index of `[[u32; 4]; 3]`, `2` as a column index. -/
def nvI : Expr nvD [] [] (.index ((3 : Nat) : Int)) := .weiter (by decide) (by decide) (.lit 1)
def nvJ : Expr nvD [] [] (.index ((4 : Nat) : Int)) := .weiter (by decide) (by decide) (.lit 2)

/-- `M[1][2] = 7;` -/
def nvBlock : Block nvD nvV false [] [] [] :=
  .cons (.assignSlot () () (nestIdx 3 4 (by decide) (by decide) nvI nvJ)
    (.weiter (by decide) (by decide) (.lit 7)) rfl nvDarf) .nil

def nvO : Orakel nvD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

def nvR : ∀ f : nvD.Fn, World nvD → Env nvD (nvD.params f) → RufAusgang f := fun _ σ _ => .ok σ ()

def nvWelt : World nvD where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun g => nomatch g
  spur := []

/-- The cells after an `ok` outcome, as numbers (`none` otherwise). -/
def nvZelle (k : Int) : Ausgang nvV false [] → Option Int
  | .ok σ _ => some (σ.slots () k ()).n
  | _ => none

/-- **`M[1][2] = 7` writes cell `1*4 + 2 = 6` and no other**: cell 6 reads
    7, cells 9 (`M[2][1]`), 2 (`M[0][2]`) and 7 (`M[1][3]`) stay 0. -/
theorem nv_lauf :
    nvZelle 6 (execBlock nvO 0 nvR nvBlock nvWelt .nil) = some 7 ∧
    nvZelle 9 (execBlock nvO 0 nvR nvBlock nvWelt .nil) = some 0 ∧
    nvZelle 2 (execBlock nvO 0 nvR nvBlock nvWelt .nil) = some 0 ∧
    nvZelle 7 (execBlock nvO 0 nvR nvBlock nvWelt .nil) = some 0 := by
  decide

/-- The flattening of `[[u32; 4]; 3]` is a bijection onto `0 .. 11`, checked
    on all 12 elements. -/
theorem nv_bijektiv :
    (∀ i : Fin 3, ∀ j : Fin 4, ∀ i' : Fin 3, ∀ j' : Fin 4,
      flachIndex 4 i j = flachIndex 4 i' j' → i = i' ∧ j = j') ∧
    (∀ k : Fin 12, ∃ i : Fin 3, ∃ j : Fin 4, (k : Int) = flachIndex 4 i j) := by
  decide

/-- The C address of `a[1][2]` on `uint32_t a[3][4]` (4-byte elements) is
    byte 24 = element 6: `ev_idx_nested` at the witness's numbers. -/
theorem nv_c_adresse (L : CLayout) (orc : DevOrc) (fr : Nat) (st : CSt) (ρ : CLok) (q : CPtr)
    (hq : 0 ≤ q.off) (p : CX) (hp : ev L orc fr p st ρ = some (.ptr q, st)) :
    ev L orc fr (.idx (.idx p (.lit 1) 3 (4 * 4)) (.lit 2) 4 4) st ρ =
      ev L orc fr (.idx p (.lit 6) (3 * 4) 4) st ρ :=
  ev_idx_nested L orc fr 3 4 4 hq hp rfl rfl rfl (by decide) (by decide) (by decide) (by decide)

#print axioms flach_injektiv
#print axioms flach_zerlegung
#print axioms eval_nestIdx
#print axioms ev_idx_nested
#print axioms nv_lauf
#print axioms nv_c_adresse

end Gabbro.Grammatik

/- CUTS: what is not proved here.
   - The memory correspondence of a static array (the `corrW` relation for a
     `T a[M][N]` object) is not stated: static arrays are the pre-existing
     uncovered form `expr:array-read` (one-dimensional ones included). This
     file proves the ADDRESS equality (`ev_idx_nested`): once a flat array
     read has its lemma, the nested one inherits it.
   - `N286` (rectangularity) enters as the modelling decision (every row
     has `N` cells by construction of `count M*N`), not as a lemma about
     the checker's literal walk; `N285`/`N287` likewise have no Lean
     counterpart beyond "a row is not a value".
   - Deeper nesting `[[[T; K]; N]; M]` is the same flattening twice
     (`flachIndex K (flachIndex N i j) k`); not stated separately.
-/
