/-
  File:      Grammatik/Adaequanz/Zeugen.lean
  Subject:   WITNESSES for Theorems 1-3 on a concrete, non-degenerate signature (`Zeugenpflicht`), every fact
             decided by the kernel.

  The signature is the smallest picture of the lock rule: `n` (a statement, arity 0), `s` (sequence, arity 2),
  `l` (`locks L { .. }`, arity 1). The spec is a checker that refuses a lock taken while it is held: state
  0 "no lock", 1 "takes the lock", 2 "takes it twice nested" (refused). Three states, all reachable, separated
  by the hole and by `l (hole)` (`l` over state 0 accepts, over state 1 refuses). Cells: 1 + 9 + 3 = 13.

    * the test set for `m = n = 3` has `2 * (3 + 13) = 32` trees (`testmenge_zahl`); the spec passes it;
      a planted wrong checker (the sequence forgets its first part) fails one of them (`falsch_faellt`);
      Theorem 1 applies (`hinlaenglich_zeuge`).
    * the root mutant of the cell `l` over state 1 passes the test set minus the trees rooted at that cell and
      fails on its witness (`wurzel_noetig_zeuge`); the lower bound `13 ≤ |M|` holds for every set sufficient
      for 4 states (`wurzel_schranke_zeuge`).
    * the counter model passes the 32 trees and is wrong on a tower (`kein_endlicher_test_zeuge`).
    * the cover theorem on the cells of the 32 trees (`deckung_zeuge`).
-/
import Grammatik.Adaequanz.Ueberdeckung

namespace Gabbro.Grammatik.Adaequanz.Zeugen

open Gabbro.Grammatik.Adaequanz

set_option linter.unusedSectionVars false

/-- The labels: a plain statement, a sequence, a lock block. -/
inductive ZK
  | n | s | l
  deriving DecidableEq, Repr

instance : Fintype ZK := ⟨⟨↑[ZK.n, ZK.s, ZK.l], by decide⟩, fun k => by cases k <;> decide⟩

def zar : ZK → Nat
  | .n => 0
  | .s => 2
  | .l => 1

def zsig : Sig := ⟨ZK, zar⟩

instance : DecidableEq zsig.K := inferInstanceAs (DecidableEq ZK)
instance : Fintype zsig.K := inferInstanceAs (Fintype ZK)

/-- The spec: 0 no lock, 1 takes the lock, 2 nested (refused). -/
def zδ : (k : ZK) → (Fin (zar k) → Fin 3) → Fin 3
  | .n, _ => 0
  | .s, p => max (p ⟨0, by decide⟩) (p ⟨1, by decide⟩)
  | .l, p => if p ⟨0, by decide⟩ = 0 then 1 else 2

def spez : Automat zsig (Fin 3) Bool := ⟨zδ, fun q => decide (q ≠ 2)⟩

def tn : Baum zsig := .knoten (k := ZK.n) fun i => absurd i.isLt (Nat.not_lt_zero _)
def ts (a b : Baum zsig) : Baum zsig := .knoten (k := ZK.s) fun i => if i.val = 0 then a else b
def tl (a : Baum zsig) : Baum zsig := .knoten (k := ZK.l) fun _ => a

/-- The access trees. -/
def acc : Fin 3 → Baum zsig := ![tn, tl tn, tl (tl tn)]

def ks : List zsig.K := [ZK.n, ZK.s, ZK.l]
def qs : List (Fin 3) := [0, 1, 2]

/-- The distinguishing contexts: the hole and `l (hole)`. -/
def W : List (Kontext zsig) := [.loch, .knoten (k := ZK.l) ⟨0, by decide⟩ (fun _ => tn) .loch]

theorem spezifiziert : Spezifiziert spez ks qs acc W where
  ks_voll k := by
    cases k
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  qs_voll := by decide
  zugang := by decide
  loch := List.mem_cons_self
  trennt := by decide

/-- The test set for implementations with at most 3 states (`m = n`, depth 1). -/
def M : List (Baum zsig) := testmenge ks (qs.map acc) W (3 - Fintype.card (Fin 3) + 1)

theorem testmenge_zahl : M.length = 32 := by
  rw [M, testmenge_laenge]; decide

theorem spez_besteht : ∀ p ∈ M, spez.sem p = spez.sem p := fun _ _ => rfl

/-- A planted wrong checker: the sequence forgets its first part. -/
def falsch : Automat zsig (Fin 3) Bool :=
  ⟨fun k p => match k, p with
    | .n, _ => 0
    | .s, p => p ⟨1, by decide⟩
    | .l, p => if p ⟨0, by decide⟩ = 0 then 1 else 2, fun q => decide (q ≠ 2)⟩

theorem falsch_faellt : ∃ p ∈ M, falsch.sem p ≠ spez.sem p := by decide

/-- **Theorem 1 on the witness**: every checker with at most 3 states that passes the 32 trees is right on
    every tree. -/
theorem hinlaenglich_zeuge : Hinreichend spez M 3 := fun _ _ I hm hpass =>
  hinlaenglich spezifiziert I hm hpass

/-- The cell `l` over state 1 (a lock block around a body that takes the lock). -/
def zelleL1 : Zelle zsig (Fin 3) := ⟨ZK.l, fun _ => 1⟩

theorem wurzel_noetig_zeuge :
    (∀ p ∈ M.filter (fun p => decide (spez.zelle p ≠ zelleL1)),
        (wurzelMutant spez zelleL1 (fun b => !b)).sem p = spez.sem p) ∧
      (wurzelMutant spez zelleL1 (fun b => !b)).sem (zeuge acc zelleL1) ≠ spez.sem (zeuge acc zelleL1) := by
  refine ⟨wurzelMutant_besteht spez zelleL1 _ _ fun p hp => ?_, ?_⟩
  · simpa using (List.mem_filter.mp hp).2
  · exact wurzelMutant_falsch spez zelleL1 _ spezifiziert.zugang (by decide)

/-- **Theorem 2a on the witness**: a set sufficient for 4 states has at least 13 trees. -/
theorem wurzel_schranke_zeuge {M' : List (Baum zsig)} (hM : Hinreichend spez M' 4) : 13 ≤ M'.length := by
  have := wurzel_schranke spezifiziert.zugang (kipp := fun b => !b) (by decide) (by decide) hM
  have h13 : (∑ k : zsig.K, Fintype.card (Fin 3) ^ zsig.ar k) = 13 := by decide
  omega

/-- **The counter model on the witness**: it passes the 32 trees and fails on a tower. -/
theorem kein_endlicher_test_zeuge :
    (∀ p ∈ M, (zaehlerModell spez (fun b => !b) ((M.map hoehe).sum)).sem p = spez.sem p) ∧
      ∃ t, (zaehlerModell spez (fun b => !b) ((M.map hoehe).sum)).sem t ≠ spez.sem t :=
  let h := kein_endlicher_test spez (kipp := fun b => !b) (by decide) (k0 := ZK.n) (k1 := ZK.l) rfl (by decide) M
  ⟨h.1, _, h.2⟩

/-- **Theorem 3 on the witness**: the cells of the spec, as the cells the trees contain; the 32 trees cover
    all 13 (so they are sufficient for every cell-local table). -/
theorem deckung_zeuge : ∀ z : Zelle zsig (Fin 3), (∃ p, Enthaelt spez z p) → ∃ p ∈ M, Enthaelt spez z p := by
  intro z _
  have hz : spez.zelle (zeuge acc z) = z := zelle_zeuge spezifiziert.zugang z
  refine ⟨zeuge acc z, ?_, ?_⟩
  · have hmem : zeuge acc z ∈ schicht ks (qs.map acc) 1 := by
      refine knoten_mem_schicht ks spezifiziert.ks_voll _ 0 z.1 _ fun i => ?_
      exact List.mem_map.mpr ⟨z.2 i, spezifiziert.qs_voll _, rfl⟩
    exact ein_mem_testmenge ks _ spezifiziert.loch hmem
  · obtain ⟨k, q⟩ := z
    exact Enthaelt.hier (by simpa [Automat.zelle, zeuge] using hz)

end Gabbro.Grammatik.Adaequanz.Zeugen
