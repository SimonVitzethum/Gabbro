/- Part 3 of `Maschine/T1` (C11 scoped-return release): the PLAIN release-aware
   leaf fact (`gutRet_blatt`), next to `gut_blatt` (the residual-precise one). -/
module

public import Grammatik.Kern.Semantik.Maschine.T1.Teil1

@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- **Frame and trace of a LEAF, plain release-aware (`GutRet`).**

    The scope-free sibling of `gut_blatt`: a scoped return releases exactly
    its scopes (`gutRet_retScoped`/`gutRet_retWhyScoped`), and memory facts
    -- the frame, the event goodness, the consistency -- never needed the
    spare-and-rank side (`GutRet` carries no residual). Only the
    residual-precise transport (`GutRetV`, the lock equality a caller keeps)
    needs the static scope check, and that lives in `gut_blatt`.

    Machine steps that fire arbitrary leaves (`.welt` firing equations, no
    program at hand) read this lemma: `blatt_brav`/`blatt_rahmen_vertrag`
    (`Maschine/T2`, `Maschine/T7`). No new premise beyond `hleaf`, which
    every `blatt` rule carries. -/
theorem Stmt.gutRet_blatt (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (hO : GutO O) :
    ∀ (s : Stmt D V l Γ Λ Λ'), s.istBlatt = true → ∀ (σ : World D) (ρ : Env D Γ),
      HeldIn Λ σ.haelt → ∀ σ', (execStmt O passes R s σ ρ).welt = some σ' →
        GutRet V.schreibt V.gschreibt σ σ'
  | .assignSlot t f i e hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append i.orte_darf e.orte_darf) hh
      exact (hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hh))).toRet
  | .assignThru p t _ f i e hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _
        (orte_append (orte_append p.orte_darf i.orte_darf) e.orte_darf) hh
      exact (hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hh))).toRet
  | .assignThruOwn p t _ f i e _ _ _ _ _ hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _
        (orte_append (orte_append p.orte_darf i.orte_darf) e.orte_darf) hh
      exact (hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hh))).toRet
  | .assignSlotRef r t _ _ f e hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append r.orte_darf e.orte_darf) hh
      exact (hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hh))).toRet
  | .assignGlob g e hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh
      exact (hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldIn hh))).toRet
  | .putBytes t f hf n i _ _ e hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append i.orte_darf e.orte_darf) hh
      exact (hl.trans (gut_schreibBytes _ t f hf Λ hw hL _ _ (hl.heldIn hh))).toRet
  | .assignVar x e, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (gut_lese σ Λ _ e.orte_darf hh).toRet
  | .shift t f hτ i von nach hn he hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_cons (orte_tab hL) i.orte_darf) hh
        exact (hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hh))).toRet
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .axiomCall a args _ hw hg hd hgd, _, σ, ρ, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh
      split at h
      · rename_i σ1 v ha
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldIn hh)
        rw [ha] at this
        exact (hl.trans (Gut.weiter hw hg this)).toRet
      · simp only [Ausgang.welt, reduceCtorEq] at h
  | .regWrite r _ e, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (gut_lese σ Λ _ e.orte_darf hh).toRet
  | .transition .., _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact (gut_fragt _ _).toRet
  | .publish g e _ _ hw hL, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh
      exact (hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldIn hh))).toRet
  | .advances .., _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact (Gut.refl _ _ _).toRet
  | .retires .., _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact (Gut.refl _ _ _).toRet
  | .ret e _, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact (gut_lese σ Λ _ e.orte_darf hh).toRet
  | .retWhy .., _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact (Gut.refl _ _ _).toRet
  | .retScoped e R, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact gutRet_retScoped R.scopes (gut_lese σ Λ _ e.orte_darf hh)
  | .retWhyScoped _ R, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact gutRet_retWhyScoped σ R.scopes
  | .leave _, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact (Gut.refl _ _ _).toRet
  | .next _, _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact (Gut.refl _ _ _).toRet
  | .ite .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .onOption .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .onTag .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .onWhy .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .call .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .callInd .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .axiomCallElse .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .callIndElse .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .locks .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .breaking .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .traverse .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .consumeTraverse .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .retry .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf
  | .forever .., hleaf, _, _, _, _, _ => by simp only [istBlatt, Bool.false_eq_true] at hleaf


end Gabbro.Grammatik
