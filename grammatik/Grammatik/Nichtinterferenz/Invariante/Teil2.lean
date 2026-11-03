module

public import Grammatik.Nichtinterferenz.LokalSchritt
public import Grammatik.Nichtinterferenz.Invariante.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Ok
variable {P : Programm D} {S : D.Tab ⊕ D.Glob → Bool} {Ax : D.Ax → Bool}
variable (P) (O : Orakel D) (passes : Nat) {st : List (KRahmen D)} (hst : StapelNR S Ax st)
  (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D)) (sp : Speicher D)
include hst

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
  | bindCall g args he' hp hr rest =>
      try simp only [kEnde]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩)) _ _
      · exact KErgOk.none
  | bindCallElse g args he' hp hr err rest =>
      try simp only [kEnde]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩)) _ _
      · exact KErgOk.none
  | regRead r hk rest =>
      try simp only [kEnde]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩)) _ _
      · exact KErgOk.none
  | regReadElse r hk z sonst rest =>
      try simp only [kEnde]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩)) _ _
      · exact KErgOk.none
  | awaits g pl hp hL hat rest =>
      try simp only [kEnde]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩)) _ _
      · exact KErgOk.none
  | bindCallInd p args he' hp hr rest =>
      try simp only [kEnde]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩)) _ _
      · exact KErgOk.none
  | bindCallIndElse p args he' hp hr err rest =>
      try simp only [kEnde]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩)) _ _
      · exact KErgOk.none
  | narrow e lo' hi' sonst rest =>
      try simp only [kEnde]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩)) _ _
      · exact KErgOk.none
  | exchange g neu hw hL rest =>
      try simp only [kEnde]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩)) _ _
      · exact KErgOk.none
  | ite c t e =>
      try simp only [kEnde]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact he, trivial⟩)) _ _
      · exact KErgOk.none
  | bindAxiom a args he' hw hg hd hgd rest =>
      simp only [nE, Bool.and_eq_true] at he
      try simp only [kEnde]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact he.2 | (simp only [GRest.nR]; exact he.2)) _ _
      · exact KErgOk.none
  | bindAxiomElse a args he' hr hw hg hd hgd err rest =>
      simp only [nE, Bool.and_eq_true] at he
      try simp only [kEnde]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact he.2 | (simp only [GRest.nR]; exact he.2)) _ _
      · exact KErgOk.lokal hst _ _ _ (by first | exact he.1.2 | (simp only [GRest.nR]; exact he.1.2)) _ _
      · exact KErgOk.none
  | ret e _ => exact kPop_ok hst f _ _
  | retScoped e R => exact kPop_ok hst f _ _
  | retWhy r _ => exact kPopGrund_ok hst f _ _ r
  | retWhyScoped r R => exact kPopGround_ok hst f _ _ r
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
  | bindCallIndElse p args he hp hr err rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      try simp only [kDann]
      exact KErgOk.push hst _ _ _ (by first | exact ⟨hb.1.2, hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.1.2, hb.2, hk⟩)) _ _ _ _
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
  | bindAxiomElse a args he hr hw hg hd hgd err rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _
      · exact KErgOk.lokal hst _ _ _ (by first
          | exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩
          | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩)) _ _
      · exact KErgOk.none
  | regRead r hk' rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      · exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _) (fun _ => KErgOk.none)
      · exact KErgOk.none
  | regReadElse r hk' zusage sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      · exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _)
          (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩)) _ _)
      · exact KErgOk.none
  | awaits g payload hp hL hat rest =>
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
  | check c sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      exact KErgOk.ite (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _)
        (fun _ => KErgOk.lokal hst _ _ _ (by first | exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩ | (simp only [GRest.nR]; exact ⟨by rw [nB_alsBlock]; exact hb.1.2, hk⟩)) _ _)
  | float op a b lo hi rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _
      · exact KErgOk.none
  | floatLit q lo hi rest =>
      simp only [nB] at hb
      try simp only [kDann]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb, hk⟩ | (simp only [GRest.nR]; exact ⟨hb, hk⟩)) _ _
      · exact KErgOk.none
  | floatOf e lo hi rest =>
      simp only [nB, Bool.and_eq_true] at hb
      try simp only [kDann]
      split
      · exact KErgOk.lokal hst _ _ _ (by first | exact ⟨hb.2, hk⟩ | (simp only [GRest.nR]; exact ⟨hb.2, hk⟩)) _ _
      · exact KErgOk.none
  | floatNarrow e lo hi sonst rest =>
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
          exact KErgOk.lokal hst _ _ _ (by first | exact ⟨by simp only [nB, nS, hr.1, Bool.and_self, hr.2.2.1], hr.2.2.2⟩ | (simp only [GRest.nR]; exact ⟨by simp [nB, nS, hr.1, hr.2.2.1], hr.2.2.2⟩)) _ _
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
  | leer => exact KErgOk.none

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
