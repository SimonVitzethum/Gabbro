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

/-- The reason a residue returns right now, if its head is a reason return. -/
def GRest.grundJetzt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Option (Fin V.gruende)
  | .ende (.retWhy r _) => some r
  | .ende (.cons (.retWhy r _) _) => some r
  | .dann (.cons (.retWhy r _) _) _ => some r
  | .ende (.retWhyScoped r _) => some r
  | .ende (.cons (.retWhyScoped r _) _) => some r
  | .dann (.cons (.retWhyScoped r _) _) _ => some r
  | _ => none

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
    | rueckConsGrund r0 hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g'
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
    | dannRetGrund r0 hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g'
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


end Gabbro.Grammatik
