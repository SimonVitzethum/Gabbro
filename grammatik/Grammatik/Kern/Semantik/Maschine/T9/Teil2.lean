module

public import Grammatik.Kern.Semantik.Maschine.T8
public import Grammatik.Kern.Semantik.Maschine.T9.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- **Firing a memory-preserving leaf keeps live memory.** From the firing
    evidence alone: excluded shapes die at the `speicherfest` test, the nine
    included shapes compute to a read-only or unchanged world. -/
theorem speicherfest_speicher
    (O : Orakel D) (passes : Nat)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hFest : s.speicherfest = true)
    (σ σ' : World D)
    (hstep : (execStmt O passes keinRuf s σ ρ).welt = some σ') :
    σ'.speicher = σ.speicher := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | assignThru p t ht f i e hw hL =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | assignSlotRef r t ht ho f e hw hL =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | assignGlob g e hw hL =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | putBytes t f hf n i hlo hhi e hw hL =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | assignVar x e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | shift t f hτ i von nach hn he hw hL =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | ite c t e =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | onOption o p a =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | onTag v arms =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | onWhy r arms =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | call f args hp hr =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | callInd p args hp hr =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | locks L hr body =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | breaking i body =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | traverse t inv body =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | retry n bis body ueberlauf =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | forever a inv body =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | axiomCall a args h hw hg hd hgd =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | regWrite r hk e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | publish g e payload hp hw hL =>
      simp only [Stmt.speicherfest, Bool.false_eq_true] at hFest
  | advances m a h hs =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | retires m s h a =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | ret e hΛ =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | retWhy r hΛ =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | leave h =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | next h =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl

#print axioms Gabbro.Grammatik.speicherfest_speicher

/-- **Per-firing preservation for memory-preserving leaves, uniformly over
    every intermediate machine.** The `hBlattAll` conclusion for the
    `speicherfest` fragment, from firing evidence plus memory-only contracts:
    the fired leaf keeps live memory (`speicherfest_speicher`), and contracts
    read only live memory (`hMem`), so `Pre` / `Post` survive with no user
    logic owed. -/
theorem hBlattAll_speicherfest_aus_feuerung
    (O : Orakel D) (passes : Nat)
    (Pre Post : D.Fn → World D → Prop) (fn : D.Fn)
    (hMem : SpeicherVertrag Pre Post fn)
    (M₀ : GenMaschine D) (g : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hFest : s.speicherfest = true)
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M₀.weltVon g) ρ).welt = some σ') :
    (Pre fn (M₀.weltVon g) ↔ Pre fn σ') ∧ (Post fn (M₀.weltVon g) ↔ Post fn σ') := by
  have hspeicher : σ'.speicher = (M₀.weltVon g).speicher :=
    speicherfest_speicher O passes V l Γ Λ Λ' s ρ hFest _ _ hstep
  exact ⟨hMem.memPre _ _ hspeicher.symm, hMem.memPost _ _ hspeicher.symm⟩

#print axioms Gabbro.Grammatik.hBlattAll_speicherfest_aus_feuerung


end Gabbro.Grammatik
