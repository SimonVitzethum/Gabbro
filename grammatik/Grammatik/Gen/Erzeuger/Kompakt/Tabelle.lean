/-
  File:      Grammatik/Gen/Erzeuger/Kompakt/Tabelle.lean
  Subject:   THE TABLE of the statements, blocks and end blocks of one context by size over the expressions one per key
             (`genTK`): bucket `k` is the clause step on the buckets below, the expressions of every context the
             canonical ones (`eK`: bucket `i` of the expression table of bound `i`), and the blocks of the other
             contexts the buckets of THEIR tables (bucket `i` of the table of bound `i`). Its completeness up to the
             summary (`genTK_rep`): every statement, block and end block of size at most the bound has a
             representative in the bucket of its own size. The tables of two bounds agree on the buckets both have
             (`genTK_getD_le`).
-/
import Grammatik.Gen.Erzeuger.Kompakt.Block
import Grammatik.Gen.Erzeuger.Knoten

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {V : Vertrag D}

/-- **The expressions of a context**: bucket `i` of the table of bound `i`. -/
def eK (Γ : Ctx) (Λ : List (Res D)) : Sz (SE D Γ Λ) := fun i => tab (genEK i Γ Λ) i

theorem eK_rep {Γ : Ctx} {Λ : List (Res D)} (τ : Ty) (e : Expr D Γ Λ τ) (hu : groesseExpr e < unendlich) :
    ∃ e' : Expr D Γ Λ τ, (⟨τ, e'⟩ : SE D Γ Λ) ∈ eK Γ Λ (groesseExpr e') ∧ GlE e' e := by
  obtain ⟨e', h, g⟩ := genEK_rep (groesseExpr e) Γ τ e (Nat.le_refl _) hu
  refine ⟨e', ?_, g⟩
  show _ ∈ tab (genEK (groesseExpr e') Γ Λ) (groesseExpr e')
  rw [tab_genEK_le Γ (Nat.le_refl _) g.groesse]
  exact h

/-- **The table of a context by size up to `n`.** -/
def genTK (V : Vertrag D) (n : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : List (Eimer V l Γ Λ) :=
  let Et := genEK n Γ Λ
  buckets ([], [], []) (fun prev k => schritt
    ⟨fun Γ' Λ' _ => eK Γ' Λ',
     fun l' Γ' Λ' _ i => if h : i < k ∧ i < n then tabB (genTK V i l' Γ' Λ') i else [],
     fun l' Γ' Λ' _ i => if h : i < k ∧ i < n then tabN (genTK V i l' Γ' Λ') i else []⟩
    (fun i => if i ≤ n then tab Et i else eK Γ Λ i) prev k) n
termination_by n
decreasing_by all_goals exact h.2

/-- The oracle of bucket `k` of the table of bound `n`. -/
def orakelK (V : Vertrag D) (n k : Nat) : Orakel V where
  ex := fun Γ' Λ' _ => eK Γ' Λ'
  bl := fun l' Γ' Λ' _ i => if i < k ∧ i < n then tabB (genTK V i l' Γ' Λ') i else []
  en := fun l' Γ' Λ' _ i => if i < k ∧ i < n then tabN (genTK V i l' Γ' Λ') i else []

theorem eK_bis (n : Nat) (Γ : Ctx) (Λ : List (Res D)) :
    (fun i => if i ≤ n then tab (genEK n Γ Λ) i else eK Γ Λ i) = eK Γ Λ := by
  funext i
  split
  · exact tab_genEK_le Γ (by omega) (Nat.le_refl _)
  · rfl

theorem genTK_eq (n : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) :
    genTK V n l Γ Λ = buckets ([], [], []) (fun prev k => schritt (orakelK V n k) (eK Γ Λ) prev k) n := by
  rw [genTK]
  simp only [dite_eq_ite]
  rw [eK_bis]
  rfl

theorem orakelK_gleich {n m k : Nat} (hn : k ≤ n) (hm : k ≤ m) : orakelK V n k = orakelK V m k := by
  simp only [orakelK, Orakel.mk.injEq]
  refine ⟨trivial, ?_, ?_⟩ <;>
  · funext l' Γ' Λ' _ i
    by_cases h : i < k
    · rw [if_pos ⟨h, by omega⟩, if_pos ⟨h, by omega⟩]
    · rw [if_neg (fun h' => h h'.1), if_neg (fun h' => h h'.1)]

/-- The tables of two bounds agree on the buckets both have. -/
theorem genTK_getD_le (l : Bool) (Γ : Ctx) (Λ : List (Res D)) {j n m : Nat} (hj : j ≤ n) (hm : j ≤ m) :
    (genTK V n l Γ Λ).getD j ([], [], []) = (genTK V m l Γ Λ).getD j ([], [], []) := by
  rw [genTK_eq, genTK_eq]
  exact getD_buckets_zwei _ _ _ _ hj hm fun prev k hk hk' => by rw [orakelK_gleich hk hk']

/-- Every statement, block and end block of size at most `n` has a representative in the bucket of its own size. -/
def TRep (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (n : Nat) (t : List (Eimer V l Γ Λ)) : Prop :=
  (∀ (Λ' : List (Res D)) (s : Stmt D V l Γ Λ Λ'), groesseStmt s ≤ n → groesseStmt s < unendlich →
    ∃ s' : Stmt D V l Γ Λ Λ', (⟨Λ', s'⟩ : SS D V l Γ Λ) ∈ tabS t (groesseStmt s') ∧ GlS s' s) ∧
  (∀ (Λ' : List (Res D)) (b : Block D V l Γ Λ Λ'), groesseBlock b ≤ n → groesseBlock b < unendlich →
    ∃ b' : Block D V l Γ Λ Λ', (⟨Λ', b'⟩ : SB D V l Γ Λ) ∈ tabB t (groesseBlock b') ∧ GlB b' b) ∧
  (∀ (e : Endblock D V l Γ Λ), groesseEnd e ≤ n → groesseEnd e < unendlich →
    ∃ e' : Endblock D V l Γ Λ, e' ∈ tabN t (groesseEnd e') ∧ GlN e' e)

/-- The oracle of bucket `j` holds representatives below `j` when the tables of the smaller bounds are complete. -/
theorem oru_orakelK {n j : Nat} (hj : j ≤ n) (hn : n < unendlich)
    (ih : ∀ i < n, ∀ l Γ Λ, TRep V l Γ Λ i (genTK V i l Γ Λ)) : ORU (orakelK V n j) j := by
  refine ⟨fun Γ' Λ' τ e hlt => ?_, fun l' Γ' Λ' Λ'' b hlt => ?_, fun l' Γ' Λ' e hlt => ?_⟩
  · obtain ⟨e', h, g⟩ := eK_rep τ e (by omega)
    exact ⟨e', fun _ _ => h, g⟩
  · obtain ⟨b', hb, gb⟩ := (ih (groesseBlock b) (by omega) l' Γ' Λ').2.1 Λ'' b (Nat.le_refl _) (by omega)
    refine ⟨b', fun _ _ => ?_, gb⟩
    have h1 : groesseBlock b' ≤ groesseBlock b := gb.groesse
    show _ ∈ (if groesseBlock b' < j ∧ groesseBlock b' < n then tabB (genTK V (groesseBlock b') l' Γ' Λ')
      (groesseBlock b') else [])
    rw [if_pos ⟨by omega, by omega⟩]
    unfold tabB at hb ⊢
    rw [genTK_getD_le l' Γ' Λ' (Nat.le_refl _) h1]
    exact hb
  · obtain ⟨e', he, ge⟩ := (ih (groesseEnd e) (by omega) l' Γ' Λ').2.2 e (Nat.le_refl _) (by omega)
    refine ⟨e', fun _ _ => ?_, ge⟩
    have h1 : groesseEnd e' ≤ groesseEnd e := ge.groesse
    show _ ∈ (if groesseEnd e' < j ∧ groesseEnd e' < n then tabN (genTK V (groesseEnd e') l' Γ' Λ')
      (groesseEnd e') else [])
    rw [if_pos ⟨by omega, by omega⟩]
    unfold tabN at he ⊢
    rw [genTK_getD_le l' Γ' Λ' (Nat.le_refl _) h1]
    exact he

/-- The oracle that answers the context at hand from the buckets below holds representatives below `j`. -/
theorem oru_selbst {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (O : Orakel V) (prev : List (Eimer V l Γ Λ)) {j : Nat}
    (hO : ORU O j) (hB : BRU (tabB prev) j) (hN : NRU (tabN prev) j) : ORU (selbst O prev) j := by
  refine ⟨fun Γ' Λ' τ e hlt => hO.ex Γ' Λ' τ e hlt, fun l' Γ' Λ' Λ'' b hlt => ?_, fun l' Γ' Λ' e hlt => ?_⟩
  · by_cases h : l' = l ∧ Γ' = Γ ∧ Λ' = Λ
    · obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨b', hb, gb⟩ := hB Λ'' b hlt
      refine ⟨b', fun m _ => ?_, gb⟩
      show _ ∈ (if h : l' = l' ∧ Γ' = Γ' ∧ Λ' = Λ' then tabBAls h prev else O.bl l' Γ' Λ' m) _
      rw [dif_pos ⟨rfl, rfl, rfl⟩]
      exact hb
    · obtain ⟨b', hb, gb⟩ := hO.bl l' Γ' Λ' Λ'' b hlt
      refine ⟨b', fun m hm => ?_, gb⟩
      show _ ∈ (if h : l' = l ∧ Γ' = Γ ∧ Λ' = Λ then tabBAls h prev else O.bl l' Γ' Λ' m) _
      rw [dif_neg h]
      exact hb m hm
  · by_cases h : l' = l ∧ Γ' = Γ ∧ Λ' = Λ
    · obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨e', he, ge⟩ := hN e hlt
      refine ⟨e', fun m _ => ?_, ge⟩
      show _ ∈ (if h : l' = l' ∧ Γ' = Γ' ∧ Λ' = Λ' then tabNAls h prev else O.en l' Γ' Λ' m) _
      rw [dif_pos ⟨rfl, rfl, rfl⟩]
      exact he
    · obtain ⟨e', he, ge⟩ := hO.en l' Γ' Λ' e hlt
      refine ⟨e', fun m hm => ?_, ge⟩
      show _ ∈ (if h : l' = l ∧ Γ' = Γ ∧ Λ' = Λ then tabNAls h prev else O.en l' Γ' Λ' m) _
      rw [dif_neg h]
      exact he m hm

set_option maxHeartbeats 4000000 in
/-- **Completeness of the table up to the summary**: every statement, block and end block of size at most `n` has a
    representative in the bucket of its own size. -/
theorem genTK_rep : ∀ (n : Nat), n < unendlich → ∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)),
    TRep V l Γ Λ n (genTK V n l Γ Λ) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
  intro hn l Γ Λ
  have ih : ∀ i < n, ∀ l Γ Λ, TRep V l Γ Λ i (genTK V i l Γ Λ) := fun i hi => ihn i hi (by omega)
  let step := fun (prev : List (Eimer V l Γ Λ)) k => schritt (orakelK V n k) (eK Γ Λ) prev k
  have hT : genTK V n l Γ Λ = buckets ([], [], []) step n := genTK_eq n l Γ Λ
  -- the claim for every size up to `n`, by strong induction on the size
  suffices C : ∀ j, j ≤ n →
      (∀ (Λ' : List (Res D)) (s : Stmt D V l Γ Λ Λ'), groesseStmt s = j →
        ∃ s' : Stmt D V l Γ Λ Λ', (⟨Λ', s'⟩ : SS D V l Γ Λ) ∈ tabS (genTK V n l Γ Λ) (groesseStmt s') ∧ GlS s' s) ∧
      (∀ (Λ' : List (Res D)) (b : Block D V l Γ Λ Λ'), groesseBlock b = j →
        ∃ b' : Block D V l Γ Λ Λ', (⟨Λ', b'⟩ : SB D V l Γ Λ) ∈ tabB (genTK V n l Γ Λ) (groesseBlock b') ∧ GlB b' b) ∧
      (∀ (e : Endblock D V l Γ Λ), groesseEnd e = j →
        ∃ e' : Endblock D V l Γ Λ, e' ∈ tabN (genTK V n l Γ Λ) (groesseEnd e') ∧ GlN e' e) from
    ⟨fun Λ' s h _ => (C _ h).1 Λ' s rfl, fun Λ' b h _ => (C _ h).2.1 Λ' b rfl, fun e h _ => (C _ h).2.2 e rfl⟩
  intro j
  induction j using Nat.strongRecOn with
  | ind j ihj =>
  intro hjn
  -- the buckets below `j` hold representatives of everything below `j`
  rcases j with _ | k
  · refine ⟨fun Λ' s h => ?_, fun Λ' b h => ?_, fun e h => ?_⟩
    · have := groesseStmt_pos s; omega
    · have := groesseBlock_pos b; omega
    · have := groesseEnd_pos e; omega
  let prev := buckets ([], [], []) step k
  have hpre : ∀ i ≤ k, (genTK V n l Γ Λ).getD i ([], [], []) = prev.getD i ([], [], []) := fun i hi => by
    rw [hT]; exact getD_buckets_le _ _ _ hi n (by omega)
  have hS : SRU (tabS prev) (k + 1) := fun Λ' s hlt => by
    obtain ⟨s', hs, gs⟩ := (ihj (groesseStmt s) hlt (by omega)).1 Λ' s rfl
    refine ⟨s', ?_, gs⟩
    unfold tabS at hs ⊢; rwa [← hpre _ (by have := gs.groesse; omega)]
  have hB : BRU (tabB prev) (k + 1) := fun Λ' b hlt => by
    obtain ⟨b', hb, gb⟩ := (ihj (groesseBlock b) hlt (by omega)).2.1 Λ' b rfl
    refine ⟨b', ?_, gb⟩
    unfold tabB at hb ⊢; rwa [← hpre _ (by have := gb.groesse; omega)]
  have hN : NRU (tabN prev) (k + 1) := fun e hlt => by
    obtain ⟨e', he, ge⟩ := (ihj (groesseEnd e) hlt (by omega)).2.2 e rfl
    refine ⟨e', ?_, ge⟩
    unfold tabN at he ⊢; rwa [← hpre _ (by have := ge.groesse; omega)]
  have hE : ERU (eK Γ Λ) (k + 1) := fun τ e _ => eK_rep τ e (by omega)
  have hO := oru_selbst (orakelK V n (k + 1)) prev (oru_orakelK hjn hn ih) hB hN
  have hbucket : (genTK V n l Γ Λ).getD (k + 1) ([], [], []) = step prev (k + 1) := by
    rw [hT]; exact getD_buckets_step _ _ _ hjn
  refine ⟨fun Λ' s hs => ?_, fun Λ' b hb => ?_, fun e he => ?_⟩
  · obtain ⟨s', hs', gs⟩ := stmtS_rep _ (eK Γ Λ) (tabB prev) s (by omega) (by rw [hs]; exact hE) (by rw [hs]; exact hB)
      (by rw [hs]; exact hO)
    by_cases hj : groesseStmt s' = k + 1
    · refine ⟨s', ?_, gs⟩
      unfold tabS; rw [hj, hbucket]; rw [hj] at hs'; exact hs'
    · obtain ⟨s'', hs'', gs'⟩ := (ihj (groesseStmt s') (by have := gs.groesse; omega) (by have := gs.groesse; omega)).1 Λ' s' rfl
      exact ⟨s'', hs'', gs'.trans gs⟩
  · obtain ⟨b', hb', gb⟩ := blockS_rep _ (eK Γ Λ) (tabS prev) (tabB prev) (tabN prev) b (by omega) (by rw [hb]; exact hE)
      (by rw [hb]; exact hS) (by rw [hb]; exact hB) (by rw [hb]; exact hN) (by rw [hb]; exact hO)
    by_cases hj : groesseBlock b' = k + 1
    · refine ⟨b', ?_, gb⟩
      unfold tabB; rw [hj, hbucket]; rw [hj] at hb'; exact hb'
    · obtain ⟨b'', hb'', gb'⟩ := (ihj (groesseBlock b') (by have := gb.groesse; omega) (by have := gb.groesse; omega)).2.1 Λ' b' rfl
      exact ⟨b'', hb'', gb'.trans gb⟩
  · obtain ⟨e', he', ge⟩ := endS_rep _ (eK Γ Λ) (tabS prev) e (by omega) (by rw [he]; exact hE)
      (by rw [he]; exact hS) (by rw [he]; exact hO)
    by_cases hj : groesseEnd e' = k + 1
    · refine ⟨e', ?_, ge⟩
      unfold tabN; rw [hj, hbucket]; rw [hj] at he'; exact he'
    · obtain ⟨e'', he'', ge'⟩ := (ihj (groesseEnd e') (by have := ge.groesse; omega) (by have := ge.groesse; omega)).2.2 e' rfl
      exact ⟨e'', he'', ge'.trans ge⟩

end Gabbro.Grammatik.Gen
