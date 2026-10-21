/-
  File:      Grammatik/Gen/Erzeuger/Kompakt/MerkenAusdruck.lean
  Subject:   THE EXPRESSION TABLES, BUILT ONCE PER CONTEXT: as `Merken.lean` for the statements. `fuelleE` builds the
             expression table of a context and, first, those of the quantifier bodies' contexts; the bodies are then
             read from the cache (`tafelE`). Every cached table is the table of `genEK` (`fuelleE_ok`), so a bucket read
             from the cache is the canonical one (`bucketE_eq`).
-/
import Grammatik.Gen.Erzeuger.Kompakt.Tabelle

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen]

/-- A cached expression table: its context, its bound, the table. -/
structure EintragE (D : Deklaration) where
  Γ : Ctx
  Λ : List (Res D)
  n : Nat
  t : List (List (SE D Γ Λ))

/-- Every expression table of the cache is the table of `genEK` of its context and bound. -/
def CacheEOk (c : List (EintragE D)) : Prop := ∀ x ∈ c, x.t = genEK x.n x.Γ x.Λ

/-- An expression table of an equal context. -/
def castE {Γ Γ' : Ctx} {Λ Λ' : List (Res D)} (h : Γ = Γ' ∧ Λ = Λ') (t : List (List (SE D Γ Λ))) :
    List (List (SE D Γ' Λ')) := by
  obtain ⟨rfl, rfl⟩ := h
  exact t

/-- Bucket `i` of the expressions of a context: from a cached table whose bound reaches `i`, else built. -/
def bucketE (c : List (EintragE D)) (Γ : Ctx) (Λ : List (Res D)) (i : Nat) : List (SE D Γ Λ) :=
  match c.findSome? (fun x => if h : x.Γ = Γ ∧ x.Λ = Λ then
      (if i ≤ x.n then some (tab (castE h x.t) i) else none) else none) with
  | some e => e
  | none => tab (genEK i Γ Λ) i

theorem bucketE_eq {c : List (EintragE D)} (hc : CacheEOk c) (Γ : Ctx) (Λ : List (Res D)) (i : Nat) :
    bucketE c Γ Λ i = eK Γ Λ i := by
  unfold bucketE eK
  split
  · rename_i e he
    obtain ⟨l₁, x, l₂, _, hx, _⟩ := List.findSome?_eq_some_iff.1 he
    have hxc : x ∈ c := by rw [‹c = l₁ ++ x :: l₂›]; simp
    by_cases h : x.Γ = Γ ∧ x.Λ = Λ
    · rw [dif_pos h] at hx
      by_cases hi : i ≤ x.n
      · rw [if_pos hi] at hx
        have := Option.some.inj hx
        rw [← this]
        obtain ⟨x1, x2, x3, xt⟩ := x
        obtain ⟨h1, h2⟩ := h
        simp only at h1 h2 hi hc hxc ⊢
        subst h1 h2
        have := hc _ hxc
        simp only at this
        simp only [castE]
        rw [this]
        exact tab_genEK_le _ hi (Nat.le_refl _)
      · rw [if_neg hi] at hx; cases hx
    · rw [dif_neg h] at hx; cases hx
  · rfl

/-- The quantifier bodies of bound `j`, read from the cache up to `j`. -/
def qM (c : List (EintragE D)) (Λ : List (Res D)) (Γ' : Ctx) (j : Nat) : Sz (SE D Γ' Λ) :=
  fun i => if i ≤ j then bucketE c Γ' Λ i else tab (genEK j Γ' Λ) i

theorem qM_eq {c : List (EintragE D)} (hc : CacheEOk c) (Λ : List (Res D)) (Γ' : Ctx) (j : Nat) :
    qM c Λ Γ' j = tab (genEK j Γ' Λ) := by
  funext i
  unfold qM
  split
  · rw [bucketE_eq hc]; exact tab_genEK_le Γ' (Nat.le_refl _) (by omega)
  · rfl

/-- The expression table of a context of bound `n` over the cache. -/
def tafelE (c : List (EintragE D)) (n : Nat) (Γ : Ctx) (Λ : List (Res D)) : List (List (SE D Γ Λ)) :=
  buckets [] (fun prev k => dedupE k prev (exprS (fun Γ' j => if j < k ∧ j < n then qM c Λ Γ' j else fun _ => [])
    (tab prev) k)) n

theorem tafelE_eq {c : List (EintragE D)} (hc : CacheEOk c) (n : Nat) (Γ : Ctx) (Λ : List (Res D)) :
    tafelE c n Γ Λ = genEK n Γ Λ := by
  rw [genEK_eq]
  unfold tafelE
  refine buckets_gleich _ _ _ n fun prev k _ => ?_
  simp only [schrittEK]
  congr 2
  funext Γ' j
  split
  · rw [qM_eq hc]
  · rfl

/-- An expression table of the context with a bound reaching `n` is cached. -/
def hatE (c : List (EintragE D)) (n : Nat) (Γ : Ctx) (Λ : List (Res D)) : Bool :=
  c.any fun x => decide (x.Γ = Γ ∧ x.Λ = Λ ∧ n ≤ x.n)

/-- **Fill the cache** with the expression table of a context of bound `n`: the quantifier bodies' contexts first. -/
def fuelleE (n : Nat) (Γ : Ctx) (Λ : List (Res D)) (c : List (EintragE D)) : List (EintragE D) :=
  if hatE c n Γ Λ then c else
  match n with
  | 0 => ⟨Γ, Λ, 0, tafelE c 0 Γ Λ⟩ :: c
  | m + 1 =>
    let c' := (Aufz.tab (D := D)).foldl (fun c t => fuelleE m (.index (D.count t) :: Γ) Λ c) c
    ⟨Γ, Λ, m + 1, tafelE c' (m + 1) Γ Λ⟩ :: c'

theorem fuelleE_ok : ∀ (n : Nat) (Γ : Ctx) (Λ : List (Res D)) (c : List (EintragE D)), CacheEOk c →
    CacheEOk (fuelleE n Γ Λ c) := by
  intro n
  induction n with
  | zero =>
    intro Γ Λ c hc
    unfold fuelleE
    split
    · exact hc
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact tafelE_eq hc 0 Γ Λ
      · exact hc x hx
  | succ m ih =>
    intro Γ Λ c hc
    unfold fuelleE
    split
    · exact hc
    · have hfold : ∀ (ts : List D.Tab) (c : List (EintragE D)), CacheEOk c →
          CacheEOk (ts.foldl (fun c t => fuelleE m (.index (D.count t) :: Γ) Λ c) c) := by
        intro ts
        induction ts with
        | nil => intro c hc; exact hc
        | cons t ts iht => intro c hc; exact iht _ (ih _ _ _ hc)
      have hc' := hfold Aufz.tab c hc
      intro x hx
      simp only at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact tafelE_eq hc' (m + 1) Γ Λ
      · exact hc' x hx

end Gabbro.Grammatik.Gen
