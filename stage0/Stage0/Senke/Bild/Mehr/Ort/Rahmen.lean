/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Ort/Rahmen.lean
  Subject:   A memory statement changes no carrier outside its carriers (multi-thread image theorem, package MT2:
             the write-back half of the G frame lemma). `OrtPrem C s` names the carrier `s` writes in `C`, so a run
             of `s` that ends normally leaves every carrier outside `C` as it was (`ort_rahmen`): reads change only
             the trace, a write to a table or a global changes only that carrier. With `ort_stmt` this is the frame
             lemma of the commit: the world after the statement, run on the CURRENT world of machine G, is the
             thread's own result on `C` and the current world everywhere else -- the other threads' commits stay.
-/
module
public import Stage0.Senke.Bild.Mehr.Ort.Blatt
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T2.Teil1
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- A read changes no carrier. -/
theorem traeger_lese (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) (c : D.Tab ⊕ D.Glob) :
    TraegerGleich (σ.lese Λ os).speicher σ.speicher c :=
  traegerGleich_refl σ.speicher c

/-- A write to a table changes no other carrier. -/
theorem traeger_schreibSlot (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) {c : D.Tab ⊕ D.Glob} (hc : c ≠ .inl t) :
    TraegerGleich (σ.schreibSlot t Λ k f v).speicher σ.speicher c := by
  cases c with
  | inl t' =>
    have ht : t' ≠ t := fun e => hc (by rw [e])
    show (σ.storeSlot t k f v).slots t' = σ.slots t'
    funext k' f'
    exact storeSlot_andere σ t k f v t' ht k' f'
  | inr g => rfl

/-- A write to a global changes no other carrier. -/
theorem traeger_schreibGlob (σ : World D) (g : D.Glob) (Λ : List (Res D)) (v : Wert D (D.gtyp g))
    {c : D.Tab ⊕ D.Glob} (hc : c ≠ .inr g) : TraegerGleich (σ.schreibGlob g Λ v).speicher σ.speicher c := by
  cases c with
  | inl t => rfl
  | inr g' =>
    have hg : g' ≠ g := fun e => hc (by rw [e])
    show (σ.storeGlob g v).globs g' = σ.globs g'
    exact storeGlob_andere σ g v g' hg

/-- Bytes written to a table change no other carrier. -/
theorem traeger_schreibBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (Λ : List (Res D))
    {c : D.Tab ⊕ D.Glob} (hc : c ≠ .inl t) :
    ∀ (bs : List Byte) (k : Int) (σ : World D), TraegerGleich (σ.schreibBytes t f hf Λ k bs).speicher σ.speicher c
  | [], _, σ => traegerGleich_refl σ.speicher c
  | _ :: bs, k, σ => by
    simp only [World.schreibBytes]
    exact traegerGleich_trans (traeger_schreibBytes t f hf Λ hc bs (k + 1) _) (traeger_schreibSlot σ t Λ k f _ hc)

/-- The written table lies in `C`, so every carrier outside `C` is another one. -/
theorem ne_von_C {C : D.Tab ⊕ D.Glob → Prop} {c w : D.Tab ⊕ D.Glob} (hw : C w) (hc : ¬ C c) : c ≠ w :=
  fun e => hc (by rw [e]; exact hw)

/-- **The write-back half of the frame lemma**: a memory statement that ends normally changes no carrier outside
    `C`. -/
theorem ort_rahmen (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {C : D.Tab ⊕ D.Glob → Prop} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ'), OrtPrem C s → ∀ {σ σ1 : World D} {ρ ρ1 : Env D Γ},
      execStmt O passes R s σ ρ = .ok σ1 ρ1 → ∀ c, ¬ C c → TraegerGleich σ1.speicher σ.speicher c
  | .assignSlot t _ _ _ _ _, hC => by
      intro σ σ1 ρ ρ1 hex c hc
      cases hex
      exact traegerGleich_trans (traeger_schreibSlot _ t Λ _ _ _ (ne_von_C (show _ ∧ _ from hC).1 hc))
        (traeger_lese σ Λ _ c)
  | .assignThru _ t _ _ _ _ _ _, hC => by
      intro σ σ1 ρ ρ1 hex c hc
      cases hex
      exact traegerGleich_trans (traeger_schreibSlot _ t Λ _ _ _ (ne_von_C (show _ ∧ _ from hC).1 hc))
        (traeger_lese σ Λ _ c)
  | .assignThruOwn _ t _ _ _ _ _ _ _ _ _ _ _, hC => by
      intro σ σ1 ρ ρ1 hex c hc
      cases hex
      exact traegerGleich_trans (traeger_schreibSlot _ t Λ _ _ _ (ne_von_C (show _ ∧ _ from hC).1 hc))
        (traeger_lese σ Λ _ c)
  | .assignSlotRef _ t _ _ _ _ _ _, hC => by
      intro σ σ1 ρ ρ1 hex c hc
      cases hex
      exact traegerGleich_trans (traeger_schreibSlot _ t Λ _ _ _ (ne_von_C (show _ ∧ _ from hC).1 hc))
        (traeger_lese σ Λ _ c)
  | .assignGlob g _ _ _, hC => by
      intro σ σ1 ρ ρ1 hex c hc
      cases hex
      exact traegerGleich_trans (traeger_schreibGlob _ g Λ _ (ne_von_C (show _ ∧ _ from hC).1 hc))
        (traeger_lese σ Λ _ c)
  | .putBytes t f hf _ _ _ _ _ _ _, hC => by
      intro σ σ1 ρ ρ1 hex c hc
      cases hex
      exact traegerGleich_trans (traeger_schreibBytes t f hf Λ (ne_von_C (show _ ∧ _ from hC).1 hc) _ _ _)
        (traeger_lese σ Λ _ c)
  | .assignVar _ _, _ => by
      intro σ σ1 ρ ρ1 hex c _
      cases hex
      exact traeger_lese σ Λ _ c
  | .shift t _ _ i _ _ _ _ _ _, hC => by
      have hCt : C (.inl t) := (show ∀ o ∈ (.inl t :: i.orte : List (D.Tab ⊕ D.Glob)), C o from hC) _ (by simp)
      intro σ σ1 ρ ρ1 hex c hc
      simp only [execStmt] at hex
      split at hex
      · cases hex
        exact traegerGleich_trans (traeger_schreibSlot _ t Λ _ _ _ (ne_von_C hCt hc)) (traeger_lese σ Λ _ c)
      · cases hex
  | .ite .., h => False.elim h
  | .onOption .., h => False.elim h
  | .onTag .., h => False.elim h
  | .onWhy .., h => False.elim h
  | .call .., h => False.elim h
  | .callInd .., h => False.elim h
  | .locks .., h => False.elim h
  | .breaking .., h => False.elim h
  | .traverse .., h => False.elim h
  | .retry .., h => False.elim h
  | .forever .., h => False.elim h
  | .axiomCall .., h => False.elim h
  | .regWrite .., h => False.elim h
  | .transition .., h => False.elim h
  | .publish .., h => False.elim h
  | .advances .., h => False.elim h
  | .retires .., h => False.elim h
  | .ret .., h => False.elim h
  | .retWhy .., h => False.elim h
  | .leave .., h => False.elim h
  | .next .., h => False.elim h
  | .consumeTraverse .., h => False.elim h
  | .retScoped .., h => False.elim h
  | .retWhyScoped .., h => False.elim h
  | .axiomCallElse .., h => False.elim h
  | .callIndElse .., h => False.elim h

end Gabbro.Stage0.Senke.BildMehr
