module
public import Grammatik.Nichtinterferenz.Invariante.Teil1Basis
import all Grammatik.Nichtinterferenz.Invariante.Teil1Basis

public import Grammatik.Nichtinterferenz.LokalSchritt

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
section Ok

variable {P : Programm D} {S : D.Tab ⊕ D.Glob → Bool} {Ax : D.Ax → Bool}
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
  | verbrauchRest t member edge inv bound mass body rest vor k =>
      simp only [GRest.nR] at hk
      simp only [kLeave]
      exact KErgOk.ite
        (fun _ => KErgOk.ite
          (fun _ => KErgOk.lokal hst _ _ _ hk.2.2.2.2.2 _ _)
          (fun _ => KErgOk.none)) (fun _ => KErgOk.none)
  | wiederRest n bis body ueber k =>
      try simp only [kLeave]
      exact KErgOk.lokal hst _ _ _ (by first | exact hk.2.2.2 | (simp only [GRest.nR]; exact hk.2.2.2)) _ _
  | ewigRest a n inv body k =>
      try simp only [kLeave]
      exact KErgOk.lokal hst _ _ _ (by first | exact hk.2.2 | (simp only [GRest.nR]; exact hk.2.2)) _ _
  | dann b k =>
      try simp only [kLeave]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp only [nB, nS, Bool.and_self], hk.2⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk.2⟩)) _ _
  | schrumpf k =>
      try simp only [kLeave]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp only [nB, nS, Bool.and_self], hk⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk⟩)) _ _
  | frei L k =>
      try simp only [kLeave]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp only [nB, nS, Bool.and_self], hk⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk⟩)) _ _
  | abbruch k =>
      try simp only [kLeave]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp only [nB, nS, Bool.and_self], hk⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk⟩)) _ _
  | _ => exact KErgOk.none

theorem kNext_ok {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D (vertragVon D f) l Γ Λ)
    (hk : k.nR S Ax) (hl : l = true) (σ : World D) (ρ : Env D Γ) :
    KErgOk P S Ax (kNext st f rho k hl σ ρ) := by
  cases k with
  | travRest t inv body is k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact hk | (simp only [GRest.nR]; exact hk)) _ _
  | verbrauchRest t member edge inv bound mass body rest vor k =>
      simp only [kNext]
      exact KErgOk.ite
        (fun _ => KErgOk.lokal hst _ _ _ (by simp only [GRest.nR] at hk ⊢; exact hk) _ _)
        (fun _ => KErgOk.none)
  | wiederRest n bis body ueber k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact hk | (simp only [GRest.nR]; exact hk)) _ _
  | ewigRest a n inv body k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact hk | (simp only [GRest.nR]; exact hk)) _ _
  | dann b k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp only [nB, nS, Bool.and_self], hk.2⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk.2⟩)) _ _
  | schrumpf k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp only [nB, nS, Bool.and_self], hk⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk⟩)) _ _
  | frei L k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp only [nB, nS, Bool.and_self], hk⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk⟩)) _ _
  | abbruch k =>
      try simp only [kNext]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp only [nB, nS, Bool.and_self], hk⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS], hk⟩)) _ _
  | _ => exact KErgOk.none

theorem kAusDann_ok {l : Bool} {Γ : Ctx} {Λ' Λ'' : List (Res D)}
    (rest : Block D (vertragVon D f) l Γ Λ' Λ'') (k : GRest D (vertragVon D f) l Γ Λ'')
    (hr : nB S Ax rest = true) (hk : k.nR S Ax) (o : Ausgang (vertragVon D f) l Γ) :
    KErgOk P S Ax (kAusDann st f rho rest k o) := by
  cases o with
  | ok σ' ρ' =>
      try simp only [kAusDann]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hr, hk⟩)) _ _
  | zurueck σ v => exact kPop_ok hst f rho σ v
  | why σ r => exact kPopGrund_ok hst f rho _ _ r
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
  | zurueck σ v => exact kPop_ok hst f rho σ v
  | why σ r => exact kPopGrund_ok hst f rho _ _ r
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
    (hk : k.nR S Ax) : KErgOk P S Ax (kEntf P O passes st f rho spur sp ρ s rest k) := by
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
  | onWhy r arms =>
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
  | consumeTraverse t member edge inv bound mass body =>
      simp only [nS, Bool.and_eq_true] at hs
      simp only [kEntf]
      exact KErgOk.lokal hst _ _ _
        (by simp only [GRest.nR]; exact ⟨hs.1.1.1.1, hs.1.1.1.2, hs.1.1.2, hs.1.2, hs.2, hr, hk⟩) _ _
  | retry n bis body ueber =>
      simp only [nS, Bool.and_eq_true] at hs
      try simp only [kEntf]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hs.1.1, hs.1.2, hs.2, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hs.1.1, hs.1.2, hs.2, hr, hk⟩)) _ _
  | forever a inv body =>
      simp only [nS, Bool.and_eq_true] at hs
      try simp only [kEntf]
      exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hs.1, hs.2, hr, hk⟩ | (simp only [GRest.nR]; exact ⟨hs.1, hs.2, hr, hk⟩)) _ _
  | callIndElse p args he hp hr' err =>
      simp only [nS, Bool.and_eq_true] at hs
      simp only [kEntf]
      split
      exact KErgOk.push hst _ _ _ (by simp only [GRest.nR]; exact ⟨hs.2, rfl, hr, hk⟩) _ _ _ _
  | axiomCallElse e a args he hp hd hgd hr' err =>
      simp only [nS, Bool.and_eq_true] at hs
      simp only [kEntf]
      split
      · exact KErgOk.lokal hst _ _ _ (by simp only [GRest.nR]; exact ⟨hr, hk⟩) _ _
      · exact KErgOk.lokal hst _ _ _ (by simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact hs.2, hk⟩) _ _
      · exact KErgOk.none
  | _ => exact KErgOk.none

theorem kDannCons_ok {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} (ρ : Env D Γ)
    (s : Stmt D (vertragVon D f) l Γ Λ Λ') (rest : Block D (vertragVon D f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D f) l Γ Λ'') (hs : nS S Ax s = true) (hr : nB S Ax rest = true)
    (hk : k.nR S Ax) : KErgOk P S Ax (kDannCons P O passes st f rho spur sp ρ s rest k) := by
  unfold kDannCons
  refine KErgOk.ite (fun _ => kEntf_ok P O passes hst f rho spur sp ρ s rest k hs hr hk)
    (fun _ => KErgOk.ite (fun _ => kAusDann_ok P hst f rho rest k hr hk _)
      (fun _ => kRufDann_ok P hst f rho spur sp ρ s rest k hr hk))

theorem kEndeCons_ok {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (ρ : Env D Γ)
    (s : Stmt D (vertragVon D f) l Γ Λ Λ') (rest : Endblock D (vertragVon D f) l Γ Λ')
    (hs : nS S Ax s = true) (hr : nE S Ax rest = true) :
    KErgOk P S Ax (kEndeCons P O passes st f rho spur sp ρ s rest) := by
  unfold kEndeCons
  refine KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp only [nB, hs, Bool.and_self], hr⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, hs], hr⟩)) _ _)
    (fun _ => KErgOk.ite (fun _ => kAusEnde_ok P hst f rho rest hr _)
      (fun _ => kRufEnde_ok P hst f rho spur sp ρ s rest hr))

end Ok
end Gabbro.Grammatik
