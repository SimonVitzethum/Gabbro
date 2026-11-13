/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
module
public import Stage0.Senke.Anweisung.Faelle.Kontext
public import Stage0.Senke.Tore.FallibleRun
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}
variable {H : List D.Lock}
variable {sc : List D.Lock}

theorem endAxiomElse_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {he : D.aerg a = some τ} {proof0 : _} {proof1 : _} {proof2 : _} {proof3 : _} {proof4 : _} {err : Endblock D (vertragVon D f) l (.why (D.agruende a) :: Γ) Λ} {rest : Endblock D (vertragVon D f) l (τ :: Γ) Λ} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc err reserved) →
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc rest reserved) →
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc (show Endblock D (vertragVon D f) l Γ Λ from .bindAxiomElse a args he proof0 proof1 proof2 proof3 proof4 err rest) reserved := by
  intro ihErr ihRest c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  simp only [lowEnd, ← hlo0, resultWords_vertragVon, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ce, te⟩, hce, ⟨cr, tr⟩, hr, ⟨cg, tg⟩, hg, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have metadata := fallibleForeignC_top hg
  have hwhy := metadata.2.2
  have hks := hW.ks
  have framePrefix := functionFrame_prefix P f
  have frameBase : FB = 4 := rfl
  simp only [List.length_append, List.length_singleton] at hs
  simp only [execEnd]
  rcases fallibleForeignC_ok (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ) he hg
    (by omega) hW (by simpa only [List.append_assoc] using hp) hWa with
    ⟨v, m2, hAA, s12, a12, value, hW2⟩ | ⟨r, m2, hAA, s12, a12, hw2, hW2⟩ | ⟨hAA, hst⟩
  · rw [hAA]
    have hp2 : PreS L m pc fp K (frei Γ reserved) ((cg) ++ (cr ++ ce)) ρ reserved := by simpa only [List.append_assoc] using hp
    have hq := hp2.nextW hW a12 (d' := frei Γ reserved + valueWords τ) (by have := hp.ctx; omega) (by omega) (by omega)
    have hp3 : PreS L m2 _ fp K (frei (τ :: Γ) reserved) cr (Env.cons (ergWert he v) ρ) reserved :=
      ⟨by simp only [frei, contextWords_cons, hwhy]; omega, hq.small, hq.frame, hq.left.code, hq.left.far,
       envAt_cons hq.env value, trivial, wstab_true _ _⟩
    have ih := ihRest (ex := exPlus ex ce.length) cr tr hr (by omega) (by omega) hW m2 _ _ _ hp3
      (by simp only [frei, contextWords_cons, hwhy] at hlo ⊢; omega)
      (hu.agreeW hW a12 (by omega)) (hk.agreeW hW a12 (by omega)) hW2
      (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons, hwhy] at this ⊢; omega)
    refine Ret.prefix (by omega) s12 (a12.mono (by omega)) (keeps_of_agreeW hW a12 hpr (by omega))
      (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_)
    · simp only [exPlus, List.length_append, fehlC_len, addr_norm]
      exact tgt_eq (by omega)
    · simp only [exPlus, List.length_append, fehlC_len, addr_norm]
      exact tgt_eq (by omega)
  · rw [hAA]
    have hp2 : PreS L m pc fp K (frei Γ reserved) ((cg ++ cr) ++ ce) ρ reserved := by simpa only [List.append_assoc] using hp
    have hq := hp2.nextW hW a12 (d' := frei Γ reserved + 1) (by have := hp.ctx; omega) (by omega) (by omega)
    simp only [List.length_append, fehlC_len] at hq
    have hp3 : PreS L m2 _ fp K (frei (.why (D.agruende a) :: Γ) reserved) ce (Env.cons (τ := .why (D.agruende a)) r ρ) reserved :=
      ⟨by simp only [frei, contextWords_cons, hwhy]; omega, hq.small, hq.frame, hq.code, hq.far,
       envAt_cons hq.env (ValueAt.of_enc hwhy hw2 rfl), trivial, wstab_true _ _⟩
    have ih := ihErr (ex := ex) ce te hce (by omega) (by omega) hW m2 _ _ _ hp3
      (by simp only [frei, contextWords_cons, hwhy] at hlo ⊢; omega)
      (hu.agreeW hW a12 (by omega)) (hk.agreeW hW a12 (by omega)) hW2
      (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons, hwhy] at this ⊢; omega)
    refine Ret.prefix (by omega) s12 (a12.mono (by omega)) (keeps_of_agreeW hW a12 hpr (by omega))
      (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_)
    · simp only [List.length_append, fehlC_len, addr_norm]
      exact tgt_eq0 (by omega)
    · simp only [List.length_append, fehlC_len, addr_norm]
      exact tgt_eq0 (by omega)
  · rw [hAA]
    exact hst

end Gabbro.Stage0.Senke
