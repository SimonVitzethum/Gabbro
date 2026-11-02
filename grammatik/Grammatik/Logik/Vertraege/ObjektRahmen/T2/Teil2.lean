module
public import Grammatik.Logik.Vertraege.ObjektRahmen.T2.Teil2Basis
import all Grammatik.Logik.Vertraege.ObjektRahmen.T2.Teil2Basis

public import Grammatik.Logik.Vertraege.ObjektRahmen.T1
public import Grammatik.Logik.Vertraege.ObjektRahmen.T1a
public import Grammatik.Logik.Vertraege.ObjektRahmen.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
/-! ## 8. THE CALL: `rufAt` keeps the frame over objects, and the frame at a separated call -/

theorem foldl_lese_slots_obj (P : Programm D) :
    ∀ (is : List D.Inv) (σ : World D),
      (is.foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ).slots = σ.slots
  | [], _ => rfl
  | i :: is, σ => foldl_lese_slots_obj P is (σ.lese (invSicht D i) (P.invariante i).orte)

/-- **The model's call keeps the frame over objects, at every depth and every world.** The
    only premise besides the program's discipline is the hardware's frame (H1). -/
theorem rufAt_obj (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O)
    (objs : D.Fn → List (ObjPar D)) (hP : ProgObjOk objs P) :
    ∀ fuel, ObjTreuR objs (rufAt P O passes fuel) := by
  intro fuel
  induction fuel with
  | zero => intro f σ ρ σ' h; simp only [RufAusgang.welt, rufAt, reduceCtorEq] at h
  | succ n ih =>
      intro f σ ρ σ' h
      simp only [rufAt] at h
      split at h
      · simp only [RufAusgang.welt, reduceCtorEq] at h
      · have hb := end_obj (O := O) (passes := passes) (R := rufAt P O passes n) (objs := objs)
          (W := WVon (objs f) ρ) (ps := objs f) ih hO (P.rumpf f) (hP f).1
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ (hP f).2.1
          (objInv_eigen _ ρ)
        split at h
        · rename_i σ2 v hs
          rw [hs] at hb
          split at h
          · simp only [RufAusgang.welt, reduceCtorEq] at h
          · split at h
            · simp only [RufAusgang.welt, reduceCtorEq] at h
            · simp only [RufAusgang.welt, Option.some.injEq] at h
              subst h
              intro t k fld hn
              rw [foldl_lese_slots_obj]
              exact hb t k fld hn
        · rename_i σ2 r hs
          simp only [RufAusgang.welt, Option.some.injEq] at h
          subst h
          rw [hs] at hb
          exact hb
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · simp only [RufAusgang.welt, reduceCtorEq] at h
        · simp only [RufAusgang.welt, reduceCtorEq] at h


end Gabbro.Grammatik
