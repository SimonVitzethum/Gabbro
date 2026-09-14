/-
  File:      Grammatik/Nichtinterferenz/Invariante.lean
  Subject:   THE FLOW CHECK IS AN INVARIANT OF EVERY THREAD (`knr_erreichbar`).

  If every function a thread can run passes the flow check (`nE` of its
  body for the thread's carrier set and axiom set), then on every
  reachable machine every frame of that thread -- head and stack -- has a
  residue that passes the residue form `GRest.nR`. The step is read
  through the function `kSchrittK` (`schrittK_von`): one case analysis over
  the residue, single-sided; the function a push enters is in the thread's
  call graph by the thread invariant `merkInvG_erreichbar`.
-/
import Grammatik.Nichtinterferenz.LokalSchritt

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Subterm lemmas -/

section Sub

variable {S : D.Tab ⊕ D.Glob → Bool} {Ax : D.Ax → Bool}

theorem nB_alsBlock {V : Vertrag D} {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), nB S Ax e.alsBlock.2 = nE S Ax e
  | _, _, .ret _ _ => by simp [Endblock.alsBlock, nB, nS, nE]
  | _, _, .retGrund _ _ => by simp [Endblock.alsBlock, nB, nS, nE]
  | _, _, .leave _ => by simp [Endblock.alsBlock, nB, nS, nE]
  | _, _, .next _ => by simp [Endblock.alsBlock, nB, nS, nE]
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]
  | _, _, .bind e rest => by
      simp only [Endblock.alsBlock, nB, nE, nB_alsBlock rest]

theorem nB_armWahlG {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
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

variable (P) (O : Orakel D) (passes : Nat) {st : List (KRahmen D)} (hst : StapelNR S Ax st)
  (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D)) (sp : Speicher D)
include hst

theorem kLeave_ok {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D (vertragVon D f) l Γ Λ)
    (hk : k.nR S Ax) (hl : l = true) (σ : World D) (ρ : Env D Γ) :
    KErgOk P S Ax (kLeave st f rho k hl σ ρ) := by
  cases k with
  | travRest t inv body is k =>
      try simp only [kLeave]
      exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact hk.2.2 | (simp only [GRest.nR]; exact hk.2.2)) _ _) (fun _ => KErgOk.none)
  | wiederRest n bis body ueber k =>
      try simp only [kLeave]
      exact KErgOk.lokal hst _ _ _ (by first | exact hk.2.2.2 | (simp only [GRest.nR]; exact hk.2.2.2)) _ _
  | ewigRest a n inv body k =>
      try simp only [kLeave]
      exact KErgOk.lokal hst _ _ _ (by first | exact hk.2.2 | (simp only [GRest.nR]; exact hk.2.2)) _ _
  | dann b k =>
      try simp only [kLeave]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp [nB, nS], hk.2⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk.2⟩)) _ _
  | schrumpf k =>
      try simp only [kLeave]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp [nB, nS], hk⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk⟩)) _ _
  | frei L k =>
      try simp only [kLeave]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp [nB, nS], hk⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk⟩)) _ _
  | abbruch k =>
      try simp only [kLeave]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp [nB, nS], hk⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk⟩)) _ _
  | _ => exact KErgOk.none

theorem kNext_ok {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D (vertragVon D f) l Γ Λ)
    (hk : k.nR S Ax) (hl : l = true) (σ : World D) (ρ : Env D Γ) :
    KErgOk P S Ax (kNext st f rho k hl σ ρ) := by
  cases k with
  | travRest t inv body is k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact hk | (simp only [GRest.nR]; exact hk)) _ _
  | wiederRest n bis body ueber k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact hk | (simp only [GRest.nR]; exact hk)) _ _
  | ewigRest a n inv body k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact hk | (simp only [GRest.nR]; exact hk)) _ _
  | dann b k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp [nB, nS], hk.2⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk.2⟩)) _ _
  | schrumpf k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp [nB, nS], hk⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk⟩)) _ _
  | frei L k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp [nB, nS], hk⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk⟩)) _ _
  | abbruch k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp [nB, nS], hk⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk⟩)) _ _
  | _ => exact KErgOk.none

theorem kAusDann_ok {l : Bool} {Γ : Ctx} {Λ' Λ'' : List (Res D)}
    (rest : Block D (vertragVon D f) l Γ Λ' Λ'') (k : GRest D (vertragVon D f) l Γ Λ'')
    (hr : nB S Ax rest = true) (hk : k.nR S Ax) (o : Ausgang (vertragVon D f) l Γ) :
    KErgOk P S Ax (kAusDann st f rho rest k o) := by
  cases o with
  | ok σ' ρ' =>
      try simp only [kAusDann]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hr, hk⟩)) _ _
  | zurueck σ v => exact kPop_ok hst f σ v
  | grund σ r => exact kPopGrund_ok hst f _ _ r
  | leave h σ' ρ' => exact kLeave_ok P hst f rho k hk h σ' ρ'
  | next h σ' ρ' => exact kNext_ok P hst f rho k hk h σ' ρ'
  | logik _ => exact KErgOk.none
  | hardware _ => exact KErgOk.none

theorem kAusEnde_ok {l : Bool} {Γ : Ctx} {Λ' : List (Res D)}
    (rest : Endblock D (vertragVon D f) l Γ Λ') (hr : nE S Ax rest = true)
    (o : Ausgang (vertragVon D f) l Γ) : KErgOk P S Ax (kAusEnde st f rho rest o) := by
  cases o with
  | ok σ' ρ' =>
      try simp only [kAusEnde]
      exact KErgOk.lokal hst _ _ _ (by first | exact hr | (simp only [GRest.nR]; exact hr)) _ _
  | zurueck σ v => exact kPop_ok hst f σ v
  | grund σ r => exact kPopGrund_ok hst f _ _ r
  | _ => exact KErgOk.none

theorem kRufEnde_ok {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (ρ : Env D Γ)
    (s : Stmt D (vertragVon D f) l Γ Λ Λ') (rest : Endblock D (vertragVon D f) l Γ Λ')
    (hr : nE S Ax rest = true) : KErgOk P S Ax (kRufEnde P st f rho spur sp ρ s rest) := by
  cases s with
  | call g args hp hr' =>
      try simp only [kRufEnde]
      exact KErgOk.push hst _ _ _ (by first | exact hr | (simp only [GRest.nR]; exact hr)) _ _ _ _
  | callInd p args hp hr' =>
      try simp only [kRufEnde]
      split
      exact KErgOk.push hst _ _ _ (by first | exact hr | (simp only [GRest.nR]; exact hr)) _ _ _ _
  | _ => exact KErgOk.none

theorem kRufDann_ok {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} (ρ : Env D Γ)
    (s : Stmt D (vertragVon D f) l Γ Λ Λ') (rest : Block D (vertragVon D f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D f) l Γ Λ'') (hr : nB S Ax rest = true) (hk : k.nR S Ax) :
    KErgOk P S Ax (kRufDann P st f rho spur sp ρ s rest k) := by
  cases s with
  | call g args hp hr' =>
      try simp only [kRufDann]
      exact KErgOk.push hst _ _ _ (by first | exact ⟨hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hr, hk⟩)) _ _ _ _
  | callInd p args hp hr' =>
      try simp only [kRufDann]
      split
      exact KErgOk.push hst _ _ _ (by first | exact ⟨hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hr, hk⟩)) _ _ _ _
  | _ => exact KErgOk.none

theorem kEntf_ok {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} (ρ : Env D Γ)
    (s : Stmt D (vertragVon D f) l Γ Λ Λ') (rest : Block D (vertragVon D f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D f) l Γ Λ'') (hs : nS S Ax s = true) (hr : nB S Ax rest = true)
    (hk : k.nR S Ax) : KErgOk P S Ax (kEntf passes st f rho spur sp ρ s rest k) := by
  cases s with
  | ite c t e =>
      simp only [nS, Bool.and_eq_true] at hs
      try simp only [kEntf]
      exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hs.1.2, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hs.1.2, hr, hk⟩)) _ _)
        (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hs.2, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hs.2, hr, hk⟩)) _ _)
  | onOption o p a =>
      simp only [nS, Bool.and_eq_true] at hs
      try simp only [kEntf]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hs.1.2, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hs.1.2, hr, hk⟩)) _ _
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hs.2, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hs.2, hr, hk⟩)) _ _
  | onTag v arms =>
      simp only [nS, Bool.and_eq_true] at hs
      try simp only [kEntf]
      split <;> rename_i heq
      · have hb : nB S Ax _ = true :=
          (congrArg (fun x => nB S Ax x.2.1) heq).symm.trans (nB_armWahlG arms _ hs.2)
        try simp only [kEntf]
        exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hb, hr, hk⟩)) _ _
      · have hb : nB S Ax _ = true :=
          (congrArg (fun x => nB S Ax x.2.1) heq).symm.trans (nB_armWahlG arms _ hs.2)
        try simp only [kEntf]
        exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hb, hr, hk⟩)) _ _
  | onGrund r arms =>
      simp only [nS, Bool.and_eq_true] at hs
      try simp only [kEntf]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨nB_grundWahlG arms _ hs.2, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨nB_grundWahlG arms _ hs.2, hr, hk⟩)) _ _
  | locks L hr' body =>
      simp only [nS] at hs
      try simp only [kEntf]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hs, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hs, hr, hk⟩)) _ _
  | breaking i body =>
      simp only [nS] at hs
      try simp only [kEntf]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hs, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hs, hr, hk⟩)) _ _
  | traverse t inv body =>
      simp only [nS, Bool.and_eq_true] at hs
      try simp only [kEntf]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hs.1, hs.2, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hs.1, hs.2, hr, hk⟩)) _ _
  | retry n bis body ueber =>
      simp only [nS, Bool.and_eq_true] at hs
      try simp only [kEntf]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hs.1.1, hs.1.2, hs.2, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hs.1.1, hs.1.2, hs.2, hr, hk⟩)) _ _
  | forever a inv body =>
      simp only [nS, Bool.and_eq_true] at hs
      try simp only [kEntf]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hs.1, hs.2, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hs.1, hs.2, hr, hk⟩)) _ _
  | _ => exact KErgOk.none

theorem kDannCons_ok {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} (ρ : Env D Γ)
    (s : Stmt D (vertragVon D f) l Γ Λ Λ') (rest : Block D (vertragVon D f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D f) l Γ Λ'') (hs : nS S Ax s = true) (hr : nB S Ax rest = true)
    (hk : k.nR S Ax) : KErgOk P S Ax (kDannCons P O passes st f rho spur sp ρ s rest k) := by
  unfold kDannCons
  refine KErgOk.ite (fun _ => kEntf_ok P passes hst f rho spur sp ρ s rest k hs hr hk)
    (fun _ => KErgOk.ite (fun _ => kAusDann_ok P hst f rho rest k hr hk _)
      (fun _ => kRufDann_ok P hst f rho spur sp ρ s rest k hr hk))

theorem kEndeCons_ok {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (ρ : Env D Γ)
    (s : Stmt D (vertragVon D f) l Γ Λ Λ') (rest : Endblock D (vertragVon D f) l Γ Λ')
    (hs : nS S Ax s = true) (hr : nE S Ax rest = true) :
    KErgOk P S Ax (kEndeCons P O passes st f rho spur sp ρ s rest) := by
  unfold kEndeCons
  refine KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp [nB, hs], hr⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, hs], hr⟩)) _ _)
    (fun _ => KErgOk.ite (fun _ => kAusEnde_ok P hst f rho rest hr _)
      (fun _ => kRufEnde_ok P hst f rho spur sp ρ s rest hr))

theorem kEnde_ok {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (e : Endblock D (vertragVon D f) l Γ Λ) (he : nE S Ax e = true) :
    KErgOk P S Ax (kEnde P O passes st f rho spur sp ρ e) := by
  cases e with
  | cons s rest =>
      simp only [nE, Bool.and_eq_true] at he
      exact kEndeCons_ok P O passes hst f rho spur sp ρ s rest he.1 he.2
  | bind e rest =>
      simp only [nE, Bool.and_eq_true] at he
      try simp only [kEnde]
      exact KErgOk.lokal hst _ _ _ (by first | exact he.2 | (simp only [GRest.nR]; exact he.2)) _ _
  | ret e _ => exact kPop_ok hst f _ _
  | retGrund r _ => exact kPopGrund_ok hst f _ _ r
  | leave _ => exact KErgOk.none
  | next _ => exact KErgOk.none

theorem kDann_ok {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (ρ : Env D Γ)
    (b : Block D (vertragVon D f) l Γ Λ Λ') (k : GRest D (vertragVon D f) l Γ Λ')
    (hb : nB S Ax b = true) (hk : k.nR S Ax) :
    KErgOk P S Ax (kDann P O passes st f rho spur sp ρ b k) := by
  cases b with
  | nil =>
      try simp only [kDann]
      exact KErgOk.lokal hst _ _ _ (by first | exact hk | (simp only [GRest.nR]; exact hk)) _ _
  | cons s rest =>
      simp only [nB, Bool.and_eq_true] at hb
      exact kDannCons_ok P O passes hst f rho spur sp ρ s rest k hb.1 hb.2 hk
  | bind e rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _
  | bindCall g args he hp hr rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      exact KErgOk.push hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _ _ _
  | bindCallInd p args he hp hr rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      try simp only [kDann]
      exact KErgOk.push hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _ _ _
  | bindCallElse g args he hp hr err rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      exact KErgOk.push hst _ _ _ (by first | exact ⟨hb.1.2, hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.1.2, hb.2, hk⟩)) _ _ _ _
  | bindAxiom a args he hw hg hd hgd rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _
      · exact KErgOk.none
  | regLies r hk' rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      · exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _) (fun _ => KErgOk.none)
      · exact KErgOk.none
  | regLiesElse r hk' zusage sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      · exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _)
          (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩)) _ _)
      · exact KErgOk.none
  | awaits g payload hp hL rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _) (fun _ => KErgOk.none)
  | exchange g neuE hw hL rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _
  | narrow e lo' hi' sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      exact KErgOk.dite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _)
        (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩)) _ _)
  | pruefung c sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _)
        (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩)) _ _)
  | gleit op a b lo hi rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _
      · exact KErgOk.none
  | gleitLit q lo hi rest =>
      simp only [nB] at hb
      try simp only [kDann]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb, hk⟩ | (simp only [GRest.nR]; exact ⟨hb, hk⟩)) _ _
      · exact KErgOk.none
  | gleitVon e lo hi rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _
      · exact KErgOk.none
  | gleitNarrow e lo hi sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩)) _ _

theorem kr_ok {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D f) l Γ Λ) (hr : r.nR S Ax) :
    KErgOk P S Ax (kr P O passes st f rho spur sp ρ r) := by
  cases r with
  | ende e => exact kEnde_ok P O passes hst f rho spur sp ρ e hr
  | dann b k => exact kDann_ok P O passes hst f rho spur sp ρ b k hr.1 hr.2
  | schrumpf k =>
      cases ρ
      show KErgOk P S Ax (kLokal st f rho _ k spur sp)
      exact KErgOk.lokal hst _ _ _ (by first | exact hr | (simp only [GRest.nR]; exact hr)) _ _
  | frei L k =>
      try simp only [kr]
      exact KErgOk.lokal hst _ _ _ (by first | exact hr | (simp only [GRest.nR]; exact hr)) _ _
  | trav t inv body ks k =>
      cases ks with
      | nil =>
          try simp only [kr]
          exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact hr.2.2 | (simp only [GRest.nR]; exact hr.2.2)) _ _) (fun _ => KErgOk.none)
      | cons i is =>
          try simp only [kr]
          exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hr.2.1, hr.1, hr.2.1, hr.2.2⟩ | (simp only [GRest.nR]; exact ⟨hr.2.1, hr.1, hr.2.1, hr.2.2⟩)) _ _)
            (fun _ => KErgOk.none)
  | travRest t inv body is k =>
      cases ρ
      show KErgOk P S Ax (kLokal st f rho _ (.trav t inv body is k) spur sp)
      exact KErgOk.lokal hst _ _ _ (by first | exact hr | (simp only [GRest.nR]; exact hr)) _ _
  | wieder n bis body ueber k =>
      cases n with
      | zero =>
          try simp only [kr]
          exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp [nB, nS, hr.1, hr.2.2.1], hr.2.2.2⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS, hr.1, hr.2.2.1], hr.2.2.2⟩)) _ _
      | succ n =>
          try simp only [kr]
          exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact hr.2.2.2 | (simp only [GRest.nR]; exact hr.2.2.2)) _ _)
            (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hr.2.1, hr⟩ | (simp only [GRest.nR]; exact ⟨hr.2.1, hr⟩)) _ _)
  | wiederRest n bis body ueber k =>
      try simp only [kr]
      exact KErgOk.lokal hst _ _ _ (by first | exact hr | (simp only [GRest.nR]; exact hr)) _ _
  | ewig a n inv body k =>
      cases n with
      | zero => exact KErgOk.none
      | succ n =>
          try simp only [kr]
          exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hr.2.1, hr⟩ | (simp only [GRest.nR]; exact ⟨hr.2.1, hr⟩)) _ _)
            (fun _ => KErgOk.none)
  | ewigRest a n inv body k =>
      try simp only [kr]
      exact KErgOk.lokal hst _ _ _ (by first | exact hr | (simp only [GRest.nR]; exact hr)) _ _
  | wartet b k => exact KErgOk.none
  | wartetSonst n err b k => exact KErgOk.none
  | abbruch k => exact KErgOk.none

end Ok

/-- **One step keeps the flow invariant of the acting thread**: the head
    and stack of `k` pass the residue form, the function of the new head
    has a checked body; then every frame of the new state passes. -/
theorem schrittK_knr {S : D.Tab ⊕ D.Glob → Bool} {Ax : D.Ax → Bool} (P : Programm D)
    (O : Orakel D) (passes : Nat) {k k' : KFaden D} {sp sp' : Speicher D} (hk : KNR S Ax k)
    (h : kSchrittK P O passes k sp = some (k', sp')) (hb : nE S Ax (P.rumpf k'.kopf.f) = true) :
    KNR S Ax k' :=
  kr_ok P O passes (fun F hF => hk F (List.mem_cons_of_mem _ hF)) k.kopf.f k.kopf.rho k.spur sp
    _ _ (hk _ List.mem_cons_self) k' sp' h hb

/-- **The flow invariant on every reachable machine** (`knr_erreichbar`).
    Per thread `t`: a carrier set `Sf t` and an axiom set `Axf t`; every
    function the thread's call graph `K t` admits has a body passing the
    flow check; the call graph is closed and holds the start function. Then
    every frame of `t` on every reachable machine passes the residue form. -/
theorem knr_erreichbar [DecidableEq D.Fn] (P : Programm D) (O : Orakel D) (passes : Nat)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (K : Faden → D.Fn → Bool) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) (Sf : Faden → D.Tab ⊕ D.Glob → Bool)
    (Axf : Faden → D.Ax → Bool) (hfl : ∀ t g, K t g = true → nE (Sf t) (Axf t) (P.rumpf g) = true)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    ∀ t, KNR (Sf t) (Axf t) (M.faeden t).kern := by
  induction hr with
  | start =>
      intro t F hF
      have e : ((RufStartG P sp init).faeden t).kern =
          ⟨[], ⟨(init t).1, (init t).2, ⟨false, D.params (init t).1,
            Signatur.anfang D (D.signatur (init t).1), (init t).2, .ende (P.rumpf (init t).1)⟩⟩,
            startSpur (init t).1⟩ := by
        show RufFadenG.kern (match init t with
          | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
              Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
              [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)) = _
        cases init t
        rfl
      rw [e] at hF
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      subst hF
      exact hfl t _ (hWurzel t)
  | schritt M M' u hr' hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        have hInv := merkInvG_erreichbar (O := O) (pa := passes) sp init
          (fun t f => K t f = true) (fun t _ => rufM fs (K t))
          (fun t => merkAbg_rufM hvoll (hAbg t)) hWurzel (RufErreichbarG.schritt _ _ _ hr' hs)
        have hk := (hInv t _ List.mem_cons_self).1
        exact schrittK_knr P O passes (ih t) (schrittK_von P O passes hs) (hfl t _ hk)
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

end Gabbro.Grammatik
