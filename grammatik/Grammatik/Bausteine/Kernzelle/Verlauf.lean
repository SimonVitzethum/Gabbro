module

public import Grammatik.Bausteine.Kernzelle.Belegung
public import Grammatik.Kern.Semantik.Maschine.T1.Teil1

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Isabelle.AccumulatesMonoid

/-! ## 1. The ghost history -/

/-- One recorded update: the cell it stored to, the queried core, the saved
    argument and the pre/post cell values at the actual store. A failure
    before any store adds no record; a later failure cannot erase a store
    already performed (the history only grows). -/
structure AccBeitrag where
  zelle : Nat
  kern : Nat
  arg : Int
  vor : Int
  nach : Int
deriving DecidableEq

/-- A contribution is completed when its store performed the merge. -/
def beitragFertig (op : AccOperator) (c : AccBeitrag) : Prop :=
  c.nach = mergeInt op c.vor c.arg

/-- The shared ghost history of one accumulator: initialization, the
    completed stores and the in-flight contributions (queried, not yet
    stored/released). -/
structure AccVerlauf where
  init : Bool
  fertig : List AccBeitrag
  flug : List AccBeitrag

/-- The fold of one cell's contributions, from the neutral element. -/
def zellFalte (op : AccOperator) (neutral : Int) (cs : List AccBeitrag) (i : Nat) : Int :=
  (cs.filter (fun c => decide (c.zelle = i))).foldl (fun acc c => mergeInt op acc c.arg) neutral

/-- Appending an unrelated store leaves the cell's fold unchanged (a later
    record cannot erase an earlier store's contribution). -/
theorem zellFalteFremd (op : AccOperator) (neutral : Int) (cs : List AccBeitrag)
    (c : AccBeitrag) (i : Nat) (h : c.zelle ≠ i) :
    zellFalte op neutral (cs ++ [c]) i = zellFalte op neutral cs i := by
  unfold zellFalte
  rw [List.filter_append]
  have hdec : ¬ decide (c.zelle = i) = true := by simpa using h
  have hc : [c].filter (fun d => decide (d.zelle = i)) = [] := by
    simp only [List.filter_cons, List.filter_nil, if_neg hdec]
  rw [hc, List.append_nil]

/-- Every guarded cell equals its completed fold plus any committed
    in-flight contribution since one-time initialization. -/
def verlaufGleichFalte (op : AccOperator) (neutral : Int) (h : AccVerlauf)
    (zellen : Nat → Int) : Prop :=
  ∀ i, zellen i = zellFalte op neutral (h.fertig ++ h.flug) i

/-! ## 2. Quiescence -/

/-- **Quiescent history**: initialization complete and no update in flight
    or occurring. Derived from a proved joined/frozen writer phase or an
    internal all-cell lock scope (the concurrency slice); never from a
    caller-provided `Bool`. -/
def akkuRuhig (h : AccVerlauf) : Prop :=
  h.init = true ∧ h.flug = []

/-- Folding the per-cell folds is folding everything: the generic
    quiescent reduction, for every merge monoid. -/
theorem falteFlach (M : MergeMonoid α) (bei : List (List α)) :
    faltet M (bei.map (faltet M)) = faltet M bei.flatten := by
  induction bei with
  | nil => simp only [List.map_nil, List.flatten_nil]
  | cons xs xss ih =>
      simp only [List.map_cons, faltet, List.flatten_cons, faltet_anhaengen]
      rw [ih]

/-- **Under quiescence, the sampled fold equals the fold of all
    contributions and the abstract neutral-start RMW chain** (the typed form
    of `am_ruhepunkt_gleich_dem_atomaren_rmw`). Samples are the per-cell
    folds; typing the contributions (range checks at each update) is user
    duty. -/
theorem ruhigFalte (M : MergeMonoid α) (bei : List (List α)) (proben : List α)
    (hz : proben = bei.map (faltet M)) :
    faltet M proben = faltet M bei.flatten ∧
      faltet M proben = rmwKette M M.neutral bei.flatten := by
  subst hz
  refine ⟨falteFlach M bei, ?_⟩
  rw [falteFlach M bei]
  exact (am_ruhepunkt_gleich_dem_atomaren_rmw M bei.flatten).symm

/-- Permutations preserve the contribution sum. -/
theorem permSumme {xs ys : List Int} (h : IsPerm xs ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.sum_cons, ih]
  | swap x y l => simp only [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Conditional permutation equality for checked addition**: two orders
    with every compared prefix in range agree. Nonnegative contributions
    suffice when the total fits (`addNichtnegGenuegt`); mixed signs need the
    stronger prefix duty on both orders. -/
theorem addVertauschungImBereich {lo hi z : Int} {xs ys : List Int}
    (hp : IsPerm xs ys) (hx : addKetteOk lo hi z xs) (hy : addKetteOk lo hi z ys) :
    rmwKette addIntMonoid z xs = rmwKette addIntMonoid z ys := by
  rw [addKetteGleichSumme, addKetteGleichSumme, permSumme hp]

/-! ## 3. The staged goal leg -/

/-- The accumulator's cell type, from descriptor validity. -/
theorem akkuZellTyp {D : Deklaration} {a : AccumulatorDecl D}
    (h : akkuOk D a) (i : Fin a.kernZahl) : D.gtyp (a.zellen i) = Ty.int a.lo a.hi :=
  h.2.2.2.2.1 i

/-- A cell value read from shared memory. -/
def zellWert (D : Deklaration) (sp : Speicher D) (a : AccumulatorDecl D)
    (hok : ∀ i, D.gtyp (a.zellen i) = Ty.int a.lo a.hi) (i : Nat) : Int :=
  if h : i < a.kernZahl then (hok ⟨i, h⟩ ▸ sp.globs (a.zellen ⟨i, h⟩)).n else 0

/-- **The staged goal leg**: every admitted accumulator's cells equal their
    completed fold plus committed in-flight contributions, at quiescence the
    sampled fold. The run-level proof that such a history exists for every
    reachable machine needs the per-cell lock protocol and GX replay (the
    concurrency slice); the pure reduction is `ruhigFalte`. -/
def AccumulatorTreueG (D : Deklaration) (sp : Speicher D)
    (A : List (AccumulatorDecl D)) (H : AccumulatorDecl D → AccVerlauf) : Prop :=
  ∀ a ∈ A, ∀ hok : akkuOk D a,
    verlaufGleichFalte a.op (neutralInt a.op a.lo a.hi a.breite) (H a)
      (zellWert D sp a (akkuZellTyp hok))

#print axioms Gabbro.Grammatik.Kernzelle.zellFalteFremd
#print axioms Gabbro.Grammatik.Kernzelle.falteFlach
#print axioms Gabbro.Grammatik.Kernzelle.ruhigFalte
#print axioms Gabbro.Grammatik.Kernzelle.permSumme
#print axioms Gabbro.Grammatik.Kernzelle.addVertauschungImBereich
#print axioms Gabbro.Grammatik.Kernzelle.akkuZellTyp

end Gabbro.Grammatik.Kernzelle
