/- Part 3 of 3 of `ZielOrtVoll` (split by hand; the umbrella `ZielOrtVoll.lean` imports all parts). -/
module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll.T1
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 3. Reason returns: what the machine logs and where the caller goes

    Contracts say nothing about a reason return (`RespektiertVertraege` and
    `EnsAmRueck` are about normal returns; `VertragAmOrtG` checks entries
    and normal returns). The statement for reasons is the machine's own:
    every step that logs `grund g rho r s0 s1` pops a head frame of `g`
    whose residue is returning exactly that reason, into a caller waiting in
    `let x = g(…) else { err }`, which continues with `err` and the reason
    bound. -/

/-- The reason returned by a source head or already saved during cleanup. -/
def GRest.grundJetzt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Option (Fin V.gruende)
  | .ende (.retWhy r _) => some r
  | .ende (.cons (.retWhy r _) _) => some r
  | .dann (.cons (.retWhy r _) _) _ => some r
  | .ende (.retWhyScoped r _) => some r
  | .ende (.cons (.retWhyScoped r _) _) => some r
  | .dann (.cons (.retWhyScoped r _) _) _ => some r
  | .aufraeumen ⟨.inr r, _⟩ _ => some r
  | _ => none

/-- Delivering a value cannot prepend a reason event. -/
private theorem rufAntwortG_wert_ne_why {z z' : RufFadenG D} {vor σ : World D}
    {v : ErgVal D (vertragVon D z.kopf.f).erg}
    (ha : rufAntwortG z vor σ (.inl v) = some z')
    (g : D.Fn) (rho : Env D (D.params g)) (r : Fin (D.gruende g)) (s0 s1 : World D)
    (hlog : z'.log = RufEreignisF.why g rho r s0 s1 :: z.log) : False := by
  cases hs : z.stapel with
  | nil =>
    simp only [rufAntwortG, hs, Option.some.injEq] at ha
    subst z'
    exact absurd hlog.symm (List.cons_ne_self _ _)
  | cons caller rst =>
    cases hr : antwortRestG z.kopf.f (.inl v) caller.rest with
    | none => simp [rufAntwortG, hs, hr] at ha
    | some resp =>
      simp [rufAntwortG, hs, hr] at ha
      subst ha
      simp only [List.cons.injEq, reduceCtorEq, false_and] at hlog

/-- Reason delivery resumes exactly a caller waiting with an else block. -/
private theorem rufAntwortG_grund_treu {z z' : RufFadenG D} {vor σ : World D}
    {grund : Fin (vertragVon D z.kopf.f).gruende}
    (ha : rufAntwortG z vor σ (.inr grund) = some z')
    (hgrund : z.kopf.rest.2.2.2.2.grundJetzt = some grund)
    (g : D.Fn) (rho : Env D (D.params g)) (r : Fin (D.gruende g)) (s0 s1 : World D)
    (hlog : z'.log = RufEreignisF.why g rho r s0 s1 :: z.log) :
    z.kopf.f = g ∧
    (∃ r' : Fin (vertragVon D z.kopf.f).gruende,
      z.kopf.rest.2.2.2.2.grundJetzt = some r' ∧ HEq r' r) ∧
    ∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (l : Bool) (Γ : Ctx)
      (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ) (hn : D.gruende g = n),
      z.stapel = caller :: rst ∧
      caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ ∧
      z'.stapel = rst ∧
      z'.kopf =
        ⟨caller.f, caller.rho, caller.s0,
          ⟨l, .why n :: Γ, Λ, Env.cons (τ := .why n) (Fin.cast hn r) ρc,
            .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩ := by
  cases hs : z.stapel with
  | nil =>
    simp only [rufAntwortG, hs, Option.some.injEq] at ha
    subst z'
    exact absurd hlog.symm (List.cons_ne_self _ _)
  | cons caller rst =>
    cases hr : antwortRestG z.kopf.f (.inr grund) caller.rest with
    | none => simp [rufAntwortG, hs, hr] at ha
    | some resp =>
      simp [rufAntwortG, hs, hr] at ha
      subst ha
      simp only [List.cons.injEq] at hlog
      obtain ⟨hev, _⟩ := hlog
      injection hev with hg _ heq _ _
      subst hg
      have hreason : grund = r := eq_of_heq heq
      subst r
      refine ⟨rfl, ⟨grund, hgrund, ?_⟩, ?_⟩
      · rfl
      · rcases caller with ⟨cf, crho, cs0, lc, Γc, Λc, ρc, rc⟩
        cases rc with
        | wartetSonst n err restb k =>
          simp only [antwortRestG] at hr
          split at hr
          · rename_i hn
            cases hr
            exact ⟨⟨cf, crho, cs0, ⟨lc, Γc, Λc, ρc, .wartetSonst n err restb k⟩⟩,
              rst, lc, Γc, Λc, _, _, n, err, restb, k, ρc, hn, rfl, rfl, rfl, rfl⟩
          · cases hr
        | _ => cases hr

/-- **Reason returns are logged faithfully.** -/
theorem rufG_grund_treu {P : Programm D} {O : Orakel D} {passes : Nat} {M M' : RufMaschineG D}
    {u : Faden} (hs : RufSchrittG P O passes M u M') (g : D.Fn) (rho : Env D (D.params g))
    (r : Fin (D.gruende g)) (s0 s1 : World D)
    (hlog : (M'.faeden u).log = RufEreignisF.why g rho r s0 s1 :: (M.faeden u).log) :
    (M.faeden u).kopf.f = g ∧
    (∃ r' : Fin (vertragVon D (M.faeden u).kopf.f).gruende,
      (M.faeden u).kopf.rest.2.2.2.2.grundJetzt = some r' ∧ HEq r' r) ∧
    ∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (l : Bool) (Γ : Ctx)
      (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ) (hn : D.gruende g = n),
      (M.faeden u).stapel = caller :: rst ∧
      caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ ∧
      (M'.faeden u).stapel = rst ∧
      (M'.faeden u).kopf =
        ⟨caller.f, caller.rho, caller.s0,
          ⟨l, .why n :: Γ, Λ, Env.cons (τ := .why n) (Fin.cast hn r) ρc,
            .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩ := by
  cases hs with
  | g1 hs =>
    cases hs with
    | _ =>
      simp only [rufUpdateG_self] at hlog
      first
        | exact absurd hlog.symm (List.cons_ne_self _ _)
        | (simp only [List.cons.injEq, reduceCtorEq, false_and] at hlog)
  | g2 hs =>
    cases hs with
    | _ =>
      simp only [rufUpdateG_self] at hlog
      first
        | exact absurd hlog.symm (List.cons_ne_self _ _)
        | (simp only [List.cons.injEq, reduceCtorEq, false_and] at hlog)
  | g3 hs =>
    cases hs with
    | _ =>
      simp only [rufUpdateG_self] at hlog
      first
        | exact absurd hlog.symm (List.cons_ne_self _ _)
        | (simp only [List.cons.injEq, reduceCtorEq, false_and] at hlog)
  | g4 hs =>
    cases hs with
    | rueckGrund r0 hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g' hfg rho'
        hrho s0' hs0 rg hrg hn =>
      simp only [rufUpdateG_self, List.cons.injEq, RufEreignisF.why.injEq] at hlog ⊢
      obtain ⟨⟨hg, hrho', hr, _, _⟩, _⟩ := hlog
      subst hg
      subst hfg
      subst hrg
      refine ⟨rfl, ⟨rg, by rw [hhead]; rfl, hr⟩, caller, rst, l, Γ, Λ, Λ', τ, n, err, restb, k, ρc,
        hn, hpop, hcaller, rfl, ?_⟩
      cases hr
      rfl
    | _ =>
      simp only [rufUpdateG_self] at hlog
      first
        | exact absurd hlog.symm (List.cons_ne_self _ _)
        | (simp only [List.cons.injEq, reduceCtorEq, false_and] at hlog)
  | g5 hs =>
    cases hs with
    | rueckConsGrund _ _ r0 hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g'
        hfg rho' hrho s0' hs0 rg hrg hn =>
      simp only [rufUpdateG_self, List.cons.injEq, RufEreignisF.why.injEq] at hlog ⊢
      obtain ⟨⟨hg, hrho', hr, _, _⟩, _⟩ := hlog
      subst hg
      subst hfg
      subst hrg
      refine ⟨rfl, ⟨rg, by rw [hhead]; rfl, hr⟩, caller, rst, l, Γ, Λ, Λ', τ, n, err, restb, k, ρc,
        hn, hpop, hcaller, rfl, ?_⟩
      cases hr
      rfl
    | dannRetGrund _ _ r0 hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g'
        hfg rho' hrho s0' hs0 rg hrg hn =>
      simp only [rufUpdateG_self, List.cons.injEq, RufEreignisF.why.injEq] at hlog ⊢
      obtain ⟨⟨hg, hrho', hr, _, _⟩, _⟩ := hlog
      subst hg
      subst hfg
      subst hrg
      refine ⟨rfl, ⟨rg, by rw [hhead]; rfl, hr⟩, caller, rst, l, Γ, Λ, Λ', τ, n, err, restb, k, ρc,
        hn, hpop, hcaller, rfl, ?_⟩
      cases hr
      rfl
    | _ =>
      simp only [rufUpdateG_self] at hlog
      first
        | exact absurd hlog.symm (List.cons_ne_self _ _)
        | (simp only [List.cons.injEq, reduceCtorEq, false_and] at hlog)
  | g6 hs =>
    cases hs with
    | _ =>
      simp only [rufUpdateG_self] at hlog
      first
        | exact absurd hlog.symm (List.cons_ne_self _ _)
        | (simp only [List.cons.injEq, reduceCtorEq, false_and] at hlog)
  | g7 hs =>
    cases hs with
    | rueckScopedWert ρ rest e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hnonempty =>
      simp only [rufUpdateG_self] at hlog
      exact absurd hlog.symm (List.cons_ne_self _ _)
    | rueckScopedGrund ρ rest grund R hhead hret hscope hΛ hnonempty =>
      simp only [rufUpdateG_self] at hlog
      exact absurd hlog.symm (List.cons_ne_self _ _)
    | rueckFreigabe ρ a L remaining hhead hnonempty =>
      simp only [rufUpdateG_self] at hlog
      exact absurd hlog.symm (List.cons_ne_self _ _)
    | rueckFreigabeLetzte ρ a L hhead z hantwort =>
      simp only [rufUpdateG_self] at hlog ⊢
      obtain ⟨answer, vor⟩ := a
      cases answer with
      | inl v =>
        exact False.elim (rufAntwortG_wert_ne_why hantwort g rho r s0 s1 hlog)
      | inr grund =>
        refine rufAntwortG_grund_treu hantwort ?_ g rho r s0 s1 hlog
        rw [hhead]; rfl
    | rueckScopedWertDirekt ρ rest e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hempty z hantwort =>
      simp only [rufUpdateG_self] at hlog
      exact False.elim (rufAntwortG_wert_ne_why hantwort g rho r s0 s1 hlog)
    | rueckScopedGrundDirekt ρ rest grund R hhead hret hscope hΛ hempty z hantwort =>
      simp only [rufUpdateG_self] at hlog ⊢
      refine rufAntwortG_grund_treu hantwort ?_ g rho r s0 s1 hlog
      rw [hhead]
      obtain h | ⟨restb, h⟩ | ⟨Λ', restb, k, h⟩ := GRest.scopedGrund_faelle hret
      all_goals rw [h]; rfl
    | _ =>
      simp only [rufUpdateG_self] at hlog
      first
        | exact absurd hlog.symm (List.cons_ne_self _ _)
        | (simp only [List.cons.injEq, reduceCtorEq, false_and] at hlog)


end Gabbro.Grammatik
