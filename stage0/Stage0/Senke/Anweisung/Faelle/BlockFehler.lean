/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
import Stage0.Senke.Anweisung.Faelle.Kontext
import Stage0.Senke.Anweisung.FehlerLauf
import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem blockAxiomElse_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {τ : Ty} {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {he : D.aerg a = some τ} {proof0 : _} {proof1 : _} {proof2 : _} {proof3 : _} {proof4 : _} {err : Endblock D (vertragVon D f) l (.why (D.agruende a) :: Γ) Λ} {rest : Block D (vertragVon D f) l (τ :: Γ) Λ Λ'} :
    (∀ {pr ex}, EndCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex err) →
    (∀ {pr ex}, BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .bindAxiomElse a args he proof0 proof1 proof2 proof3 proof4 err rest) := by
  intro ihErr ihRest c top h hK hs hW m pc σ ρ hp hlo0b hlo hu hk hWa hpr
  simp only [lowB] at h
  split at h
  · next b lo' hi' hb hτ =>
    split at h
    · next hc =>
      obtain ⟨hf, hlo', hn⟩ := hc
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ct, tt⟩, ht, ck, hck, ⟨ce, te⟩, hce, ⟨cr, tr⟩, hr, hc⟩ := h
      split at hc
      · next hJ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        simp only [List.length_append, List.length_singleton, fehlC_len] at hs
        have hFB3 : FB = 4 := rfl
        have hks := hW.ks
        have h7 := torC_top1 ht
        simp only [execBlock]
        rcases torElse_ok (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ) he hτ hb hf hlo' hn ht hck hJ (by omega)
          (by omega) hW hp hWa with ⟨v, m2, w, hAA, s12, a12, hw2, hen, hW2⟩ | ⟨r, m2, hAA, s12, a12, hw2, hW2⟩ |
          ⟨hAA, hst⟩
        · rw [hAA]
          have hp2 : PreS (reserved := reserved) L m pc fp K (frei Γ reserved) ((ct ++ fehlC (frei Γ reserved) b.fehler ((16 * (ck.length + (cr ++ [ci 18 (16 * (ce.length + 1)) 0 0]).length) : Nat) : Int)
              ++ ck) ++ ((cr ++ [ci 18 (16 * (ce.length + 1)) 0 0]) ++ ce)) ρ := by simpa only [List.append_assoc] using hp
          have hq := hp2.nextW hW a12 (d' := frei Γ reserved + 1) (by have := hp.ctx; omega) (by omega) (by omega)
          simp only [List.length_append, fehlC_len] at hq
          have hp3 : PreS (reserved := reserved) L m2 _ fp K (frei Γ reserved + 1) cr (Env.cons (ergWert he v) ρ) :=
            ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.left.left.code, hq.left.left.far,
             envAt_cons hq.env hw2 hen, trivial, wstab_true _ _⟩
          have ih := ihRest (ex := exPlus ex (ce.length + 1)) cr tr hr (by omega) (by omega) hW m2 _ _ _ hp3 hlo0b
            (by simp only [frei, List.length_cons] at hlo ⊢; omega)
            (hu.agreeW hW a12 (by omega)) (hk.agreeW hW a12 (by omega)) hW2
            (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
          have ihS := Sim.schrumpf ih
          refine Sim.prefix hlo0b s12 (a12.mono (by omega)) (keeps_of_agreeW hW a12 hpr (by omega))
            (Sim.cont ihS ?_ ?_ ?_)
          · intro m3 a3
            have hc3 := codeAt_agreeWIn hW a3 (codeAt_right hq.left.code)
              (codeFar_right (n := cr.length) (k := 1) (by simpa using hq.left.far))
            have hj := hc3 0 (by simp)
            simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hj
            have sj := Star.one (run_step (t := ⟨_, fp⟩) hj (by decide) (run_jmp (t := ⟨_, fp⟩) hj))
            have hl : sx (II.f (16 * ((ce.length : Int) + 1))) = BitVec.ofNat 64 (16 * (ce.length + 1)) := by
              have := sx_nat (d := 16 * (ce.length + 1)) (by omega); simpa using this
            rw [hl] at sj
            refine star_cast sj rfl ?_
            simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, fehlC_len, addr_norm]
            congr 2 <;> omega
          · simp only [exPlus, List.length_append, List.length_singleton, fehlC_len, addr_norm]
            exact tgt_eq (by omega)
          · simp only [exPlus, List.length_append, List.length_singleton, fehlC_len, addr_norm]
            exact tgt_eq (by omega)
        · rw [hAA]
          have hp2 : PreS (reserved := reserved) L m pc fp K (frei Γ reserved) ((ct ++ fehlC (frei Γ reserved) b.fehler ((16 * (ck.length + (cr ++ [ci 18 (16 * (ce.length + 1)) 0 0]).length) : Nat) : Int)
              ++ ck ++ (cr ++ [ci 18 (16 * (ce.length + 1)) 0 0])) ++ ce) ρ := by simpa only [List.append_assoc] using hp
          have hq := hp2.nextW hW a12 (d' := frei Γ reserved + 1) (by have := hp.ctx; omega) (by omega) (by omega)
          simp only [List.length_append, fehlC_len] at hq
          have hp3 : PreS (reserved := reserved) L m2 _ fp K (frei Γ reserved + 1) ce (Env.cons (τ := .why (D.agruende a)) r ρ) :=
            ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
             envAt_cons hq.env hw2 rfl, trivial, wstab_true _ _⟩
          have ih := ihErr (ex := ex) ce te hce (by omega) (by omega) hW m2 _ _ _ hp3
            (by simp only [frei, List.length_cons] at hlo ⊢; omega)
            (hu.agreeW hW a12 (by omega)) (hk.agreeW hW a12 (by omega)) hW2
            (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
          refine Sim.prefix hlo0b s12 (a12.mono (by omega)) (keeps_of_agreeW hW a12 hpr (by omega))
            (Ret.toSim (Ret.cast (Ret.schrumpf ih) ?_ ?_ ?_))
          · simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, fehlC_len, addr_norm]
          · simp only [List.length_append, List.length_singleton, fehlC_len, addr_norm]
            exact tgt_eq0 (by omega)
          · simp only [List.length_append, List.length_singleton, fehlC_len, addr_norm]
            exact tgt_eq0 (by omega)
        · rw [hAA]
          exact hst
      · cases hc
    · cases h
  · cases h

end Gabbro.Stage0.Senke
