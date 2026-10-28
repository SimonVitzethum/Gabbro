/-
  File:      Grammatik/Gen/Erzeuger/Kompakt/AusdruckTab.lean
  Subject:   THE TABLE of the expressions one per key (`genEK`): size after size, the clause stream on the buckets
             below, of which each bucket keeps the first expression of every key not seen before and of exactly its
             size; the quantifier bodies come from the table of the extended context of the body's own size. Every
             expression of size at most the bound has a representative in it (`genEK_rep`): same type, the same
             carriers read, not larger, in the bucket of its own size; and the tables of two bounds agree on the
             buckets both have (`tab_genEK_le`).
-/
import Grammatik.Gen.Erzeuger.Kompakt.Ausdruck

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {Γ : Ctx} {Λ : List (Res D)}

/-! ## Buckets -/

section Eimer

variable {β : Type} (leer : β)

theorem getD_buckets_le (step : List β → Nat → β) (d : β) {j n : Nat} (hj : j ≤ n) : ∀ m, n ≤ m →
    (buckets leer step m).getD j d = (buckets leer step n).getD j d := by
  intro m hm
  induction m with
  | zero => have : n = 0 := by omega
            subst this; rfl
  | succ m ih =>
    by_cases h : n ≤ m
    · rw [getD_buckets_alt _ _ _ (by omega), ih h]
    · have : n = m + 1 := by omega
      subst this; rfl

theorem getD_buckets_step (step : List β → Nat → β) (d : β) {k n : Nat} (hk : k + 1 ≤ n) :
    (buckets leer step n).getD (k + 1) d = step (buckets leer step k) (k + 1) := by
  rw [getD_buckets_le leer step d (Nat.le_refl _) n hk, getD_buckets_neu]

/-- Two step functions that agree on the sizes up to `n` build the same buckets up to `n`. -/
theorem buckets_gleich (step step' : List β → Nat → β) :
    ∀ n, (∀ prev k, k ≤ n → step prev k = step' prev k) → buckets leer step n = buckets leer step' n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [buckets]
    rw [buckets_gleich step step' n fun prev k hk => h prev k (by omega), h _ _ (Nat.le_refl _)]

/-- Step functions that agree on the sizes both bounds reach give tables that agree on the buckets both have. -/
theorem getD_buckets_zwei (step step' : List β → Nat → β) (d : β) {j n n' : Nat} (hj : j ≤ n) (hj' : j ≤ n')
    (h : ∀ prev k, k ≤ n → k ≤ n' → step prev k = step' prev k) :
    (buckets leer step n).getD j d = (buckets leer step' n').getD j d := by
  rw [getD_buckets_le leer step d (n := j) (Nat.le_refl _) n hj,
    getD_buckets_le leer step' d (n := j) (Nat.le_refl _) n' hj',
    buckets_gleich leer step step' j fun prev k hk => h prev k (by omega) (by omega)]

theorem mem_buckets_flatten {α : Type} {step : List (List α) → Nat → List α} {leer : List α} {k : Nat}
    {y : α} (h : y ∈ ((buckets leer step k).flatMap id)) : ∃ j ≤ k, y ∈ (buckets leer step k).getD j [] := by
  obtain ⟨l, hl, hy⟩ := List.mem_flatMap.1 h
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  have := length_buckets leer step k
  refine ⟨j, by omega, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact hy

end Eimer

/-! ## The table -/

/-- One bucket of size `k`: the first expression of every key not seen in the buckets below, of size `k`. -/
def dedupE (k : Nat) (prev : List (List (SE D Γ Λ))) (b : List (SE D Γ Λ)) : List (SE D Γ Λ) :=
  (entdoppeltEimer eSchl (fun x => groesseExpr x.2 != k) ([], (prev.flatMap id).map eSchl) b).1

/-- **The expressions of one context, one per key**, by size up to `n`; a quantifier body of bound `j` comes from
    the table of bound `j` of the extended context (asked only below the bucket at hand). -/
def genEK (n : Nat) (Γ : Ctx) (Λ : List (Res D)) : List (List (SE D Γ Λ)) :=
  buckets [] (fun prev k => dedupE k prev (exprS (fun Γ' j => if h : j < k ∧ j < n then tab (genEK j Γ' Λ) else
    fun _ => []) (tab prev) k)) n
termination_by n
decreasing_by exact h.2

/-- The step of the table of bound `n`. -/
def schrittEK (n : Nat) (Γ : Ctx) (Λ : List (Res D)) (prev : List (List (SE D Γ Λ))) (k : Nat) : List (SE D Γ Λ) :=
  dedupE k prev (exprS (fun Γ' j => if j < k ∧ j < n then tab (genEK j Γ' Λ) else fun _ => []) (tab prev) k)

theorem genEK_eq (n : Nat) (Γ : Ctx) : genEK (D := D) n Γ Λ = buckets [] (schrittEK n Γ Λ) n := by
  rw [genEK]
  simp only [dite_eq_ite]
  rfl

/-- The tables of two bounds agree on the buckets both have. -/
theorem tab_genEK_le (Γ : Ctx) {j n m : Nat} (hj : j ≤ n) (hm : j ≤ m) :
    tab (genEK (D := D) n Γ Λ) j = tab (genEK m Γ Λ) j := by
  rw [genEK_eq, genEK_eq]
  unfold tab
  refine getD_buckets_zwei [] _ _ [] hj hm fun prev k hk hk' => ?_
  simp only [schrittEK]
  congr 2
  funext Γ' i
  by_cases h : i < k
  · rw [if_pos ⟨h, by omega⟩, if_pos ⟨h, by omega⟩]
  · rw [if_neg (fun h' => h h'.1), if_neg (fun h' => h h'.1)]

/-- Every expression of a bucket has the bucket's size. -/
theorem groesse_genEK (n : Nat) (Γ : Ctx) (j : Nat) :
    ∀ x ∈ tab (genEK (D := D) n Γ Λ) j, groesseExpr x.2 = j := by
  intro x hx
  rw [genEK_eq] at hx
  unfold tab at hx
  rcases j with _ | k
  · rcases n with _ | n
    · simp only [buckets, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, Nat.zero_add,
  Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero, Option.getD_some, List.not_mem_nil] at hx
    · rw [getD_buckets_le _ _ _ (Nat.zero_le _) (n + 1) (Nat.zero_le _)] at hx
      simp only [buckets, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, Nat.zero_add,
  Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero, Option.getD_some, List.not_mem_nil] at hx
  · by_cases hk : k + 1 ≤ n
    · rw [getD_buckets_step _ _ _ hk] at hx
      rcases eimer_teil _ _ _ _ x hx with h | ⟨_, h⟩
      · cases h
      · simpa using h
    · have hl := length_buckets ([] : List (SE D Γ Λ)) (schrittEK n Γ Λ) n
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hx
      cases hx

set_option maxHeartbeats 2000000 in
/-- **Every expression has a representative in the table**: same type, same carriers read, not larger, in the
    bucket of its own size. -/
theorem genEK_rep : ∀ (n : Nat) (Γ : Ctx) (τ : Ty) (e : Expr D Γ Λ τ),
    groesseExpr e ≤ n → groesseExpr e < unendlich →
    ∃ e' : Expr D Γ Λ τ, (⟨τ, e'⟩ : SE D Γ Λ) ∈ tab (genEK n Γ Λ) (groesseExpr e') ∧ GlE e' e := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
  intro Γ
  let Q : Nat → (Γ' : Ctx) → Nat → Sz (SE D Γ' Λ) := fun k Γ' j => if j < k ∧ j < n then tab (genEK j Γ' Λ) else
    fun _ => []
  suffices H : ∀ s, ∀ (τ : Ty) (e : Expr D Γ Λ τ), groesseExpr e = s → s ≤ n → s < unendlich →
      ∃ e' : Expr D Γ Λ τ, (⟨τ, e'⟩ : SE D Γ Λ) ∈ tab (genEK n Γ Λ) (groesseExpr e') ∧ GlE e' e from
    fun τ e h1 h2 => H _ τ e rfl h1 h2
  intro s
  induction s using Nat.strongRecOn with
  | ind s ihs =>
  intro τ e hs hn hu
  -- the parts and the quantifier body have representatives
  obtain ⟨e', hg, hP, hPQ⟩ := ersetzeE
    (fun y => y ∈ tab (genEK n Γ Λ) (groesseExpr y.2))
    (fun y => y.2 ∈ tab (genEK (groesseExpr y.2.2) y.1 Λ) (groesseExpr y.2.2)) e
    (fun x hx => by
      have hlt := teile_kleiner e x hx
      exact ihs _ (by omega) x.1 x.2 rfl (by omega) (by omega))
    (fun x hx => by
      have hlt := qteil_kleiner e x hx
      obtain ⟨y, hy, gy⟩ := ihn (groesseExpr x.2.2) (by omega) x.1 x.2.1 x.2.2 (Nat.le_refl _) (by omega)
      refine ⟨y, ?_, gy⟩
      show _ ∈ tab (genEK (groesseExpr y) x.1 Λ) (groesseExpr y)
      rw [tab_genEK_le x.1 (Nat.le_refl _) gy.groesse]
      exact hy)
  -- the representative is in the clause stream of its size, on the buckets below it
  have hpos := groesseExpr_pos e'
  obtain ⟨k, hk⟩ : ∃ k, groesseExpr e' = k + 1 := ⟨groesseExpr e' - 1, by omega⟩
  have hkn : k + 1 ≤ n := by have := hg.groesse; omega
  have hT : genEK n Γ Λ = buckets [] (schrittEK n Γ Λ) n := genEK_eq n Γ
  have hTe : ∀ x ∈ e'.teile, x ∈ tab (buckets [] (schrittEK n Γ Λ) k) (groesseExpr x.2) := by
    intro x hx
    have hlt := teile_kleiner e' x hx
    have := hP x hx
    rw [hT] at this
    unfold tab at this ⊢
    rwa [getD_buckets_le _ _ _ (n := k) (by omega) n (by omega)] at this
  have hQe : QTeileIn (Q (k + 1)) e' := by
    intro x hx
    have hlt := qteil_kleiner e' x hx
    have h1 : groesseExpr x.2.2 < k + 1 ∧ groesseExpr x.2.2 < n := ⟨by omega, by omega⟩
    show x.2 ∈ (if groesseExpr x.2.2 < k + 1 ∧ groesseExpr x.2.2 < n then tab (genEK (groesseExpr x.2.2) x.1 Λ)
      else fun _ => []) (groesseExpr x.2.2)
    rw [if_pos h1]
    exact hPQ x hx
  have hc := exprS_vollst (Q (k + 1)) (tab (buckets [] (schrittEK n Γ Λ) k)) e' (by have := hg.groesse; omega)
    hTe hQe
  rw [hk] at hc
  -- the bucket keeps it or an expression of the same key
  have hbucket : tab (genEK n Γ Λ) (k + 1) = schrittEK n Γ Λ (buckets [] (schrittEK n Γ Λ) k) (k + 1) := by
    rw [hT]; unfold tab; rw [getD_buckets_step _ _ _ hkn]
  obtain ⟨-, -, h3, h4⟩ := eimer_spec eSchl (fun x => groesseExpr x.2 != k + 1)
    (exprS (Q (k + 1)) (tab (buckets [] (schrittEK n Γ Λ) k)) (k + 1))
    ([], ((buckets [] (schrittEK n Γ Λ) k).flatMap id).map eSchl)
  have hkey := h4 _ hc (by simp only [hk, bne_self_eq_false])
  have rep : ∀ y ∈ tab (genEK n Γ Λ) (groesseExpr y.2), eSchl y = eSchl ⟨τ, e'⟩ →
      groesseExpr y.2 ≤ k + 1 → ∃ e'' : Expr D Γ Λ τ, (⟨τ, e''⟩ : SE D Γ Λ) ∈ tab (genEK n Γ Λ)
        (groesseExpr e'') ∧ GlE e'' e := by
    intro y hy hky hle
    obtain ⟨τ', y⟩ := y
    simp only at hle hy
    have hτ : τ' = τ := (Prod.mk.inj hky).1
    subst hτ
    exact ⟨y, hy, GlE.trans ⟨orte_of_eSchl hky, by omega⟩ hg⟩
  rcases h3 _ hkey with hprev | ⟨b, hb, hkb⟩
  · obtain ⟨y, hy, hky⟩ := List.mem_map.1 hprev
    obtain ⟨j, hj, hyj⟩ := mem_buckets_flatten hy
    have hyT : y ∈ tab (genEK n Γ Λ) j := by
      rw [hT]; unfold tab; rw [getD_buckets_le _ _ _ hj n (by omega)]; exact hyj
    have hsz := groesse_genEK n Γ j y hyT
    exact rep y (by rw [hsz]; exact hyT) hky (by omega)
  · have hbT : b ∈ tab (genEK n Γ Λ) (k + 1) := by
      rw [hbucket]; simp only [schrittEK, dedupE]; exact hb
    have hsz := groesse_genEK n Γ (k + 1) b hbT
    exact rep b (by rw [hsz]; exact hbT) hkb (by omega)

end Gabbro.Grammatik.Gen
