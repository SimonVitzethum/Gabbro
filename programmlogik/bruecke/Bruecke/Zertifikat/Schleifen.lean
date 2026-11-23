module
public import Bruecke.Zertifikat.Regeln
import all Grammatik.Speichermodell.Atomar.AtomarSem.Teil1
import all Grammatik.Kern.Semantik.Semantik.T1.Teil2
import all Grammatik.Kern.Semantik.Semantik.T2.Teil1
@[expose] public section

/-!
# Exact weakest-precondition rules for bounded loops, one pass at a time

`retry n` runs at most `n + 1` checks and `traverse` runs over the finite list of a table's indices
(`retryLauf`, `traverseLauf`). Both are unrolled here exactly as the model defines them: one rule for
the end of the loop and one for a pass, each an equivalence. No invariant is needed where the bound
is a number: the proof follows the passes. (The generic invariant rules `wpSA_retry`/`wpSA_traverse`
of the model remain for unbounded reasoning.)
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.WP

variable {D : Deklaration} {V : Vertrag D}

section HA

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {l : Bool} {Γ : Ctx}

/-- The weakest precondition of the remaining `n` passes of a `retry`. -/
def wpRetryA {Λ : List (Res D)} (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (ueberlauf : Block D V l Γ Λ Λ) (n : Nat) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) : Prop :=
  Q (retryLauf (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
      (fun σ ρ => let σ := leseA A σ Λ bis.orte; (σ, wahr? (eval σ bis σ ρ)))
      (fun σ ρ => execBlockHA S O U A passes R ueberlauf σ ρ) n σ ρ)

/-- What follows one pass of a `retry`, by the pass's outcome. -/
def retryWeiter {Λ : List (Res D)} (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (ueberlauf : Block D V l Γ Λ Λ) (n : Nat) (Q : Ausgang V l Γ → Prop) : Ausgang V true Γ → Prop
  | .ok σ' ρ' => wpRetryA S O U A passes R bis body ueberlauf n Q σ' ρ'
  | .next _ σ' ρ' => wpRetryA S O U A passes R bis body ueberlauf n Q σ' ρ'
  | .leave _ σ' ρ' => Q (.ok σ' ρ')
  | .zurueck σ' v => Q (.zurueck σ' v)
  | .why σ' r => Q (.why σ' r)
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

theorem wpSA_retry_lauf {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (ueberlauf : Block D V l Γ Λ Λ) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpSA S O U A passes R (.retry n bis body ueberlauf) Q σ ρ ↔
      wpRetryA S O U A passes R bis body ueberlauf n Q σ ρ := by
  unfold wpSA wpRetryA
  simp only [execStmtHA]

theorem wpRetryA_null {Λ : List (Res D)} (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (ueberlauf : Block D V l Γ Λ Λ) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpRetryA S O U A passes R bis body ueberlauf 0 Q σ ρ ↔
      if wahr? (eval (leseA A σ Λ bis.orte) bis (leseA A σ Λ bis.orte) ρ) = true
      then Q (.ok (leseA A σ Λ bis.orte) ρ)
      else wpBA S O U A passes R ueberlauf Q (leseA A σ Λ bis.orte) ρ := by
  unfold wpRetryA wpBA
  simp only [retryLauf]
  split <;> rfl

theorem wpRetryA_succ {Λ : List (Res D)} (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (ueberlauf : Block D V l Γ Λ Λ) (n : Nat) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpRetryA S O U A passes R bis body ueberlauf (n + 1) Q σ ρ ↔
      if wahr? (eval (leseA A σ Λ bis.orte) bis (leseA A σ Λ bis.orte) ρ) = true
      then Q (.ok (leseA A σ Λ bis.orte) ρ)
      else wpBA S O U A passes R body (retryWeiter S O U A passes R bis body ueberlauf n Q)
        (leseA A σ Λ bis.orte) ρ := by
  unfold wpRetryA wpBA
  simp only [retryLauf]
  split
  · rfl
  · cases execBlockHA S O U A passes R body (leseA A σ Λ bis.orte) ρ <;> rfl

/-- The weakest precondition of a `traverse` over the remaining indices `ks`. -/
def wpTravA {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (ks : List (Wert D (.index (D.count t))))
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) : Prop :=
  Q (traverseLauf (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
      (fun σ ρ => let σ := leseA A σ Λ inv.orte; (σ, wahr? (eval σ inv σ ρ))) ks σ ρ)

/-- What follows one pass of a `traverse`, by the pass's outcome. -/
def travWeiter {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (ks : List (Wert D (.index (D.count t))))
    (Q : Ausgang V l Γ → Prop) : Ausgang V true (.index (D.count t) :: Γ) → Prop
  | .ok σ' ρ' => wpTravA S O U A passes R t inv body ks Q σ' ρ'.tail
  | .next _ σ' ρ' => wpTravA S O U A passes R t inv body ks Q σ' ρ'.tail
  | .leave _ σ' ρ' =>
      if wahr? (eval (leseA A σ' Λ inv.orte) inv (leseA A σ' Λ inv.orte) ρ'.tail) = true
      then Q (.ok (leseA A σ' Λ inv.orte) ρ'.tail) else Q (.logik .schleife)
  | .zurueck σ' v => Q (.zurueck σ' v)
  | .why σ' r => Q (.why σ' r)
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

theorem wpSA_traverse_lauf {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (Q : Ausgang V l Γ → Prop) (σ : World D)
    (ρ : Env D Γ) :
    wpSA S O U A passes R (.traverse t inv body) Q σ ρ ↔
      wpTravA S O U A passes R t inv body (alleIndizes (D.count t)) Q σ ρ := by
  unfold wpSA wpTravA
  simp only [execStmtHA]

/-- The index `k` of a table of `n` slots, if it is one (the function `alleIndizes` filters by). -/
def indexVon (n : Int) (k : Nat) : Option (Zahl 0 (n - 1)) :=
  if h : ((k : Nat) : Int) ≤ n - 1 then some ⟨((k : Nat) : Int), by omega, h⟩ else none

/-- **The indices of a table, one at a time.** `List.range` is built from its end, so the kernel cannot take
    the first index of a large table without building them all; `List.range'` gives them from the front. -/
theorem alleIndizes_faul (n : Int) :
    alleIndizes n = (List.range' 0 n.toNat).filterMap (indexVon n) := by
  unfold alleIndizes indexVon
  rw [List.range_eq_range']

/-- The next index of a large table, by an equation (the kernel's head normal form of `List.range'` is
    its internal recursor, which a later step would unfold over the whole table). -/
theorem indizes_ab (n : Int) (s m : Nat) (h : ((s : Nat) : Int) ≤ n - 1) :
    (List.range' s (m + 1)).filterMap (indexVon n) =
      ⟨((s : Nat) : Int), by omega, h⟩ :: (List.range' (s + 1) m).filterMap (indexVon n) := by
  simp only [List.range'_succ, List.filterMap_cons, indexVon, h, dite_true]

theorem indizes_leer (n : Int) (s : Nat) : (List.range' s 0).filterMap (indexVon n) = [] := rfl

theorem wpTravA_nil {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (Q : Ausgang V l Γ → Prop) (σ : World D)
    (ρ : Env D Γ) :
    wpTravA S O U A passes R t inv body [] Q σ ρ ↔
      if wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = true
      then Q (.ok (leseA A σ Λ inv.orte) ρ) else Q (.logik .schleife) := by
  unfold wpTravA
  simp only [traverseLauf]
  split <;> rfl

theorem wpTravA_cons {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (k : Wert D (.index (D.count t)))
    (ks : List (Wert D (.index (D.count t)))) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpTravA S O U A passes R t inv body (k :: ks) Q σ ρ ↔
      if wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = false
      then Q (.logik .schleife)
      else wpBA S O U A passes R body (travWeiter S O U A passes R t inv body ks Q)
        (leseA A σ Λ inv.orte) (.cons k ρ) := by
  unfold wpTravA wpBA
  simp only [traverseLauf]
  split
  · rfl
  · cases execBlockHA S O U A passes R body (leseA A σ Λ inv.orte) (.cons k ρ) <;>
      first | rfl | exact iff_of_eq (apply_ite Q _ _ _)

end HA

end Gabbro.Bruecke
