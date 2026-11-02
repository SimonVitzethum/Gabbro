module

public import Grammatik.Nichtinterferenz.LokalSchritt

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Subterm lemmas -/

section Sub

variable {S : D.Tab ⊕ D.Glob → Bool} {Ax : D.Ax → Bool}

theorem nB_alsBlock {V : Vertrag D} {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), nB S Ax e.alsBlock.2 = nE S Ax e
  | _, _, .ret _ _ => by simp only [Endblock.alsBlock, nB, nS, Bool.and_true, nE]
  | _, _, .retWhy _ _ => by simp only [Endblock.alsBlock, nB, nS, Bool.and_self, nE]
  | _, _, .retScoped _ _ => by simp only [Endblock.alsBlock, nB, nS, Bool.and_true, nE]
  | _, _, .retWhyScoped _ _ => by simp only [Endblock.alsBlock, nB, nS, Bool.and_self, nE]
  | _, _, .leave _ => by simp only [Endblock.alsBlock, nB, nS, Bool.and_self, nE]
  | _, _, .next _ => by simp only [Endblock.alsBlock, nB, nS, Bool.and_self, nE]
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .bind e rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .bindCall a args he _ _ rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .bindAxiom a args he hw hg hd hgd rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .bindCallElse a args he _ hr err rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .bindCallIndElse p args he hp hr err rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .narrow e lo' hi' sonst rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .narrowRequired e lo' hi' rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .exchange g neu hw hL rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .ite c t e => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock t]

theorem nB_armWahlG {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    nA S Ax arms = true → nB S Ax (armWahlG arms v).2.1 = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, h => by
      simp only [nA, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, h => by
      simp only [nA, Bool.and_eq_true] at h
      exact nB_armWahlG rest _ h.2

theorem nB_grundWahlG {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    nG S Ax arms = true → nB S Ax (grundWahlG arms r) = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, h => by
      simp only [nG, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨_ + 1, _⟩, h => by
      simp only [nG, Bool.and_eq_true] at h
      exact nB_grundWahlG rest _ h.2

end Sub

/-! ## 2. Results that keep the invariant -/

/-- A step result keeps the flow invariant, given that the function of its
    head frame has a checked body (the premise a push needs). -/
def KErgOk (P : Programm D) (S : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) (x : KErg D) : Prop :=
  ∀ k' sp', x = some (k', sp') → nE S Ax (P.rumpf k'.kopf.f) = true → KNR S Ax k'

section Ok

variable {P : Programm D} {S : D.Tab ⊕ D.Glob → Bool} {Ax : D.Ax → Bool}

/-- The frames of a stack all pass the residue form. -/
def StapelNR (S : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) (st : List (KRahmen D)) : Prop :=
  ∀ F ∈ st, F.rest.2.2.2.2.nR S Ax

theorem KErgOk.none : KErgOk P S Ax none := fun _ _ h => by cases h

theorem KErgOk.lokal {st : List (KRahmen D)} (hst : StapelNR S Ax st) (f : D.Fn)
    (rho : Env D (D.params f)) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    {r : GRest D (vertragVon D f) l Γ Λ} (hr : r.nR S Ax) (spur : List (Ereignis D))
    (sp : Speicher D) : KErgOk P S Ax (kLokal st f rho ρ r spur sp) := by
  intro k' sp' h _
  simp only [kLokal, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hr
  · exact hst F hF

theorem KErgOk.push {st : List (KRahmen D)} (hst : StapelNR S Ax st) (f : D.Fn)
    (rho : Env D (D.params f)) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    {rc : GRest D (vertragVon D f) l Γ Λ} (hr : rc.nR S Ax) (g : D.Fn) (rhog : Env D (D.params g))
    (spur : List (Ereignis D)) (sp : Speicher D) :
    KErgOk P S Ax (kPush P st f rho ρ rc g rhog spur sp) := by
  intro k' sp' h hb
  simp only [kPush, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hb
  · rcases List.mem_cons.mp hF with rfl | hF
    · exact hr
    · exact hst F hF

theorem KErgOk.ite {c : Prop} [Decidable c] {x y : KErg D} (h1 : c → KErgOk P S Ax x)
    (h2 : ¬c → KErgOk P S Ax y) : KErgOk P S Ax (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]; exact h1 hc
  · rw [if_neg hc]; exact h2 hc

theorem KErgOk.dite {c : Prop} [Decidable c] {x : c → KErg D} {y : ¬c → KErg D}
    (h1 : ∀ h, KErgOk P S Ax (x h)) (h2 : ∀ h, KErgOk P S Ax (y h)) :
    KErgOk P S Ax (dite c x y) := by
  by_cases hc : c
  · rw [dif_pos hc]; exact h1 hc
  · rw [dif_neg hc]; exact h2 hc

theorem kPop_ok {st : List (KRahmen D)} (hst : StapelNR S Ax st) (f : D.Fn) (σ : World D)
    (v : ErgVal D (vertragVon D f).erg) : KErgOk P S Ax (kPop st f σ v) := by
  cases st with
  | nil => exact KErgOk.none
  | cons c rst =>
      have hc := hst c List.mem_cons_self
      have hrst : StapelNR S Ax rst := fun F hF => hst F (List.mem_cons_of_mem _ hF)
      simp only [kPop]
      refine KErgOk.ite (fun _ => ?_) (fun _ => ?_)
      · obtain ⟨cf, crho, ⟨l, Γ, Λ, ρc, r⟩⟩ := c
        cases r with
        | wartet restb k =>
            simp only [kBinde]
            refine KErgOk.dite (fun _ => ?_) (fun _ => KErgOk.none)
            intro k' sp' h _
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            intro F hF
            rcases List.mem_cons.mp hF with rfl | hF
            · exact ⟨hc.1, hc.2⟩
            · exact hrst F hF
        | wartetSonst n err restb k =>
            simp only [kBinde]
            refine KErgOk.dite (fun _ => ?_) (fun _ => KErgOk.none)
            intro k' sp' h _
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            intro F hF
            rcases List.mem_cons.mp hF with rfl | hF
            · exact ⟨hc.2.1, hc.2.2⟩
            · exact hrst F hF
        | _ => exact KErgOk.none
      · intro k' sp' h _
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro F hF
        rcases List.mem_cons.mp hF with rfl | hF
        · exact hc
        · exact hrst F hF

theorem kPopGrund_ok {st : List (KRahmen D)} (hst : StapelNR S Ax st) (f : D.Fn)
    (spur : List (Ereignis D)) (sp : Speicher D) (r : Fin (vertragVon D f).gruende) :
    KErgOk P S Ax (kPopGrund st f spur sp r) := by
  cases st with
  | nil => exact KErgOk.none
  | cons c rst =>
      have hc := hst c List.mem_cons_self
      have hrst : StapelNR S Ax rst := fun F hF => hst F (List.mem_cons_of_mem _ hF)
      obtain ⟨cf, crho, ⟨l, Γ, Λ, ρc, rr⟩⟩ := c
      cases rr with
      | wartetSonst n err restb k =>
          simp only [kPopGrund]
          refine KErgOk.dite (fun _ => ?_) (fun _ => KErgOk.none)
          intro k' sp' h _
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          intro F hF
          rcases List.mem_cons.mp hF with rfl | hF
          · exact ⟨by rw [nB_alsBlock]; exact hc.1, hc.2.2⟩
          · exact hrst F hF
      | _ => exact KErgOk.none


end Ok

end Gabbro.Grammatik
