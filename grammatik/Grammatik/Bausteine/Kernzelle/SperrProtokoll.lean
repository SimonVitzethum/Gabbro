module

public import Grammatik.Bausteine.Kernzelle.Zulassung
public import Grammatik.Bausteine.Kernzelle.Verlauf
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T3
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T3a

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Isabelle.AccumulatesMonoid

variable {D : Deklaration}

/-! ## 1. The per-cell lock protocol -/

/-- Each accumulator cell is guarded by its exclusive lock: the admission's
    storage fact is exactly the guard the race leg needs. No per-core race
    exemption is added; the ordinary guarded case (`rennfrei_g_voll` via
    `RennfreiBisGA`) orders every cross-thread pair on these cells. -/
theorem akkuZelleBewacht {P : Programm D} {fs : List D.Fn} {a : AccumulatorDecl D}
    (h : akkuZulaessig P fs a) (i : Fin a.kernZahl) :
    Bewacht (.inr (a.zellen i)) (a.sperren i) := by
  obtain ⟨_, h1, _, _, _, _⟩ := h
  simpa only [Bewacht, h1 i]

/-- Every cell of an admitted accumulator has a guard lock. -/
theorem akkuZellenBewacht {P : Programm D} {fs : List D.Fn} {a : AccumulatorDecl D}
    (h : akkuZulaessig P fs a) (i : Fin a.kernZahl) :
    ∃ L, Bewacht (.inr (a.zellen i)) L :=
  ⟨a.sperren i, akkuZelleBewacht h i⟩

/-- The admitted cells are covered by the existing race leg: each has a guard,
    so the unguarded separation duty (`renn`) never fires on them and the
    guarded leg orders their accesses. Group invariants and `KernHaltEA`
    still apply unchanged (they quantify over all locks and carriers,
    including the generated ones; caller floors come from the admission's
    `mE` facts). -/
theorem akkuRennfreiAbgedeckt {P : Programm D} {fs : List D.Fn} {a : AccumulatorDecl D}
    (h : akkuZulaessig P fs a) (i : Fin a.kernZahl) :
    ∃ L, Bewacht (.inr (a.zellen i)) L :=
  akkuZellenBewacht h i

/-! ## 2. Quiescence collapses the history -/

/-- Under quiescence the in-flight list is empty, so the appended history is
    the completed one. -/
theorem zellFalteRuhig (op : AccOperator) (neutral : Int) (h : AccVerlauf)
    (hr : akkuRuhig h) (i : Nat) :
    zellFalte op neutral (h.fertig ++ h.flug) i = zellFalte op neutral h.fertig i := by
  rw [hr.2, List.append_nil]

/-- A history witness that is quiescent agrees cell-for-cell with the
    completed fold. -/
theorem verlaufGleichRuhig (op : AccOperator) (neutral : Int) (h : AccVerlauf)
    (zellen : Nat → Int) (hT : verlaufGleichFalte op neutral h zellen)
    (hr : akkuRuhig h) (i : Nat) :
    zellen i = zellFalte op neutral h.fertig i := by
  have h1 := hT i
  rw [zellFalteRuhig op neutral h hr i] at h1
  exact h1

/-- The sampled per-cell folds, as one list. -/
def akkuProben (M : MergeMonoid α) (bei : List (List α)) : List α :=
  bei.map (faltet M)

/-- **Quiescent reduction, applied**: the sampled fold equals the fold of all
    contributions and the neutral-start RMW chain (`ruhigFalte` at the ghost
    level; typing the contributions and establishing quiescence are user
    duties). -/
theorem akkuRuhigReduktion (M : MergeMonoid α) (bei : List (List α)) :
    faltet M (akkuProben M bei) = faltet M bei.flatten ∧
      faltet M (akkuProben M bei) = rmwKette M M.neutral bei.flatten :=
  ruhigFalte M bei _ rfl

/-- Under a quiescent history, every admitted cell equals its completed fold. -/
theorem akkuRuhigTreue (A : List (AccumulatorDecl D)) (H : AccumulatorDecl D → AccVerlauf)
    (sp : Speicher D) (hT : AccumulatorTreueG D sp A H) {a : AccumulatorDecl D}
    (ha : a ∈ A) (hok : akkuOk D a) (hr : akkuRuhig (H a)) (i : Nat) :
    zellWert D sp a (akkuZellTyp hok) i =
      zellFalte a.op (neutralInt a.op a.lo a.hi a.breite) (H a).fertig i := by
  have h1 := (hT a ha hok) i
  rw [zellFalteRuhig a.op _ (H a) hr i] at h1
  exact h1

/-! ## 3. The staged added conjunct -/

/-- **The staged accumulator leg, as an added conjunct beside `ZielX`/`ZielFX`**:
    the cell/history equality for every admitted accumulator, plus its
    quiescent collapse to the completed fold. The run-level existence of such
    a history for every reachable machine needs the GX replay of the update
    stores (open); the pure reduction is `akkuRuhigReduktion`. Once that replay
    lands, this becomes a field of `ZielX`/`ZielFX`; until then it is stated
    here, proved from an explicit history witness. -/
structure AkkuZielErweitert (sp : Speicher D) (A : List (AccumulatorDecl D))
    (H : AccumulatorDecl D → AccVerlauf) : Prop where
  treue : AccumulatorTreueG D sp A H
  ruhigFalte : ∀ a ∈ A, ∀ hok : akkuOk D a, akkuRuhig (H a) → ∀ i,
    zellWert D sp a (akkuZellTyp hok) i =
      zellFalte a.op (neutralInt a.op a.lo a.hi a.breite) (H a).fertig i

/-- From a history witness and quiescence, the staged leg holds. -/
theorem akkuZielErweitert_aus (A : List (AccumulatorDecl D))
    (H : AccumulatorDecl D → AccVerlauf) (sp : Speicher D)
    (hT : AccumulatorTreueG D sp A H) (hr : ∀ a ∈ A, akkuRuhig (H a)) :
    AkkuZielErweitert sp A H where
  treue := hT
  ruhigFalte := fun a ha hok hrA i => akkuRuhigTreue A H sp hT ha hok (hr a ha) i

/-! ## 4. Start completeness: admission plus start values decide the start check -/

/-- **Start completeness**: with the admission (descriptor validity) and the
    start values (neutral at every cell), the decided start check holds. This
    is the link direction the interface needs: per-unit start values plus the
    linked admission give the linked start Bool. -/
theorem akkuStartB_vollst {E : Einheit D} {fs : List D.Fn} {A : List (AccumulatorDecl D)}
    (hAdm : AccumulatorAdmission E.P fs A) (hStart : AkkuStart E A) :
    akkuStartB E A = true := by
  unfold akkuStartB
  refine List.all_eq_true.mpr fun a ha => ?_
  have hok : akkuOk D a := (hAdm.1 a ha).1
  have b0 : akkuOkB a = true := (akkuOkB_iff).mpr hok
  rw [b0, Bool.true_and]
  refine (finRangeAll_iff).mpr fun i => ?_
  unfold spGlobIntB
  rw [dif_pos (akkuZellTyp hok i)]
  exact decide_eq_true (hStart a ha hok i)

#print axioms Gabbro.Grammatik.Kernzelle.akkuZelleBewacht
#print axioms Gabbro.Grammatik.Kernzelle.akkuZellenBewacht
#print axioms Gabbro.Grammatik.Kernzelle.akkuRennfreiAbgedeckt
#print axioms Gabbro.Grammatik.Kernzelle.zellFalteRuhig
#print axioms Gabbro.Grammatik.Kernzelle.verlaufGleichRuhig
#print axioms Gabbro.Grammatik.Kernzelle.akkuRuhigReduktion
#print axioms Gabbro.Grammatik.Kernzelle.akkuRuhigTreue
#print axioms Gabbro.Grammatik.Kernzelle.akkuZielErweitert_aus
#print axioms Gabbro.Grammatik.Kernzelle.akkuStartB_vollst

end Gabbro.Grammatik.Kernzelle
