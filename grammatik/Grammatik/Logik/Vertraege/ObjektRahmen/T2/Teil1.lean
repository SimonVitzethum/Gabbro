module

public import Grammatik.Logik.Vertraege.ObjektRahmen.T1
public import Grammatik.Logik.Vertraege.ObjektRahmen.T1a

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

section Schleifen
variable {W : D.Tab → Int → Prop} {ps : List (ObjPar D)} {V : Vertrag D} {l : Bool}

theorem traverseLauf_obj {τ : Ty} {Γ : Ctx} (hlen : LenOk ps Γ)
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, ObjInv W ps ρ → ObjA W ps σ (schritt σ ρ))
    (hi : ∀ σ ρ, SlotRahmen W σ (inv σ ρ).1) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ), ObjInv W ps ρ →
      ObjA W ps σ (traverseLauf (l := l) schritt inv ks σ ρ) := by
  intro ks
  induction ks with
  | nil =>
      intro σ ρ hρ
      simp only [traverseLauf]
      split
      · exact ⟨hi σ ρ, hρ⟩
      · trivial
  | cons k ks ih =>
      intro σ ρ hρ
      simp only [traverseLauf]
      split
      · trivial
      · have hstep := hs (inv σ ρ).1 (.cons k ρ) (hρ.cons hlen k)
        split
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hi σ ρ).trans hstep.1) (ih σ1 ρ1.tail hstep.2.tail)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hi σ ρ).trans hstep.1) (ih σ1 ρ1.tail hstep.2.tail)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          split
          · exact ⟨((hi σ ρ).trans hstep.1).trans (hi σ1 ρ1.tail), hstep.2.tail⟩
          · trivial
        · rename_i σ1 v hs1
          rw [hs1] at hstep
          exact (hi σ ρ).trans hstep
        · rename_i σ1 r hs1
          rw [hs1] at hstep
          exact (hi σ ρ).trans hstep
        · trivial
        · trivial

theorem retryLauf_obj {Γ : Ctx} (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, ObjInv W ps ρ → ObjA W ps σ (schritt σ ρ))
    (hb : ∀ σ ρ, SlotRahmen W σ (bis σ ρ).1)
    (hu : ∀ σ ρ, ObjInv W ps ρ → ObjA W ps σ (ueberlauf σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), ObjInv W ps ρ →
      ObjA W ps σ (retryLauf schritt bis ueberlauf n σ ρ) := by
  intro n
  induction n with
  | zero =>
      intro σ ρ hρ
      simp only [retryLauf]
      split
      · exact ⟨hb σ ρ, hρ⟩
      · exact ObjA.vor (hb σ ρ) (hu _ ρ hρ)
  | succ n ih =>
      intro σ ρ hρ
      simp only [retryLauf]
      split
      · exact ⟨hb σ ρ, hρ⟩
      · have hstep := hs (bis σ ρ).1 ρ hρ
        split
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hb σ ρ).trans hstep.1) (ih σ1 ρ1 hstep.2)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hb σ ρ).trans hstep.1) (ih σ1 ρ1 hstep.2)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ⟨(hb σ ρ).trans hstep.1, hstep.2⟩
        · rename_i σ1 v hs1
          rw [hs1] at hstep
          exact (hb σ ρ).trans hstep
        · rename_i σ1 r hs1
          rw [hs1] at hstep
          exact (hb σ ρ).trans hstep
        · trivial
        · trivial

theorem foreverLauf_obj {Γ : Ctx} (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, ObjInv W ps ρ → ObjA W ps σ (schritt σ ρ))
    (hi : ∀ σ ρ, SlotRahmen W σ (inv σ ρ).1) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), ObjInv W ps ρ →
      ObjA W ps σ (foreverLauf (l := l) a schritt inv n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ _; simp only [foreverLauf]; trivial
  | succ n ih =>
      intro σ ρ hρ
      simp only [foreverLauf]
      split
      · trivial
      · have hstep := hs (inv σ ρ).1 ρ hρ
        split
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hi σ ρ).trans hstep.1) (ih σ1 ρ1 hstep.2)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ObjA.vor ((hi σ ρ).trans hstep.1) (ih σ1 ρ1 hstep.2)
        · rename_i σ1 ρ1 hs1
          rw [hs1] at hstep
          exact ⟨(hi σ ρ).trans hstep.1, hstep.2⟩
        · rename_i σ1 v hs1
          rw [hs1] at hstep
          exact (hi σ ρ).trans hstep
        · rename_i σ1 r hs1
          rw [hs1] at hstep
          exact (hi σ ρ).trans hstep
        · trivial
        · trivial

end Schleifen
/-- A completed call admitted by `ObjRufOk` stays inside the caller's frame. -/
theorem ruf_rahmen_in {objs : D.Fn → List (ObjPar D)} {W : D.Tab → Int → Prop}
    {ps : List (ObjPar D)} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : ObjTreuR objs R) {Γ : Ctx} {Λ : List (Res D)} {f : D.Fn}
    {args : Args D Γ Λ (D.params f)} {ρ : Env D Γ} (hok : ObjRufOk objs ps f args)
    (hinv : ObjInv W ps ρ) (σ σ1 : World D)
    (hw : (R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).welt =
      some σ1) : SlotRahmen W σ σ1 :=
  (hR f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) σ1 hw).mono
    (objRufOk_rahmen hok hinv _ _)

/-- An axiom that writes no table changes no slot. -/
theorem axiom_rahmen {O : Orakel D} (hO : TreuO O) {W : D.Tab → Int → Prop} {a : D.Ax}
    (hok : KeinTabAx a) (σ : World D) (ρ : Env D (D.aparams a))
    {σ1 : World D} (h : (axiomAntwort O a σ ρ).1 = σ1) : SlotRahmen W σ σ1 := by
  have h1 := axiomAntwort_treu O hO a σ ρ
  rw [h] at h1
  exact fun t k f _ => h1.1.1 t (hok t) k f

/-! ## 7. THE INDUCTION over the whole grammar -/

section Rumpf
variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (objs : D.Fn → List (ObjPar D)) (W : D.Tab → Int → Prop) (ps : List (ObjPar D))
variable (hR : ObjTreuR objs R) (hO : TreuO O)
include hR hO
set_option linter.unusedSectionVars false

end Rumpf
end Gabbro.Grammatik
