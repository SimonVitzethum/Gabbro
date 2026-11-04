/-
  Subject: Case theorems for fallible indirect calls: `Stmt.callIndElse`,
  `Block.bindCallIndElse`, `Endblock.bindCallIndElse`.
-/
module
public import Stage0.Senke.Anweisung.Faelle.IndElse
public import Stage0.Senke.Anweisung.Faelle.CallElse
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
variable [Kern] {D : Deklaration} {L : Lay D}

theorem stmtIndElse_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} {τ : Ty} {p : Expr D Γ Λ (.fnptr n)} {args : Args D Γ Λ (D.sigNr n).params}
    {he : (D.sigNr n).erg = some τ} {proof0 : RufPasst D (vertragVon D f) (D.sigNr n) Λ} {proof1 : 0 < (D.sigNr n).gruende}
    {err : Endblock D (vertragVon D f) l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ)} :
    (∀ {pr ex}, EndCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex err) →
    StmtCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ _ from .callIndElse p args he proof0 proof1 err) := by
  intro ihErr c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowS, ← hlo0, resultWords_vertragVon, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, hce, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have hFB3 : FB = 4 := rfl
  have hFramePrefix := functionFrame_prefix P f
  have hks := hW.ks
  have hprE : ∀ j ∈ pr, j < frei (.why (D.sigNr n).gruende :: Γ) reserved := by
    intro j hj; have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega
  have hcall := callIndElse_ok (cr := []) hS hA p args he (σ.lese Λ (p.orte ++ args.orte)) hcc (by omega) hp hs hu hW hWa
  simp only [execStmt, indSonst]
  generalize pointerEq :
      eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pointer at hcall ⊢
  rcases pointer with ⟨callee, hf⟩
  dsimp only at hcall ⊢
  rcases hcall with
    ⟨σ', v, m2, hR, st, a, hp2, hw2⟩ | ⟨σ', r, m2, hR, st, a, hp2, hw2⟩ |
    ⟨e, hR, st⟩ | ⟨e, hR, st⟩
  · erw [hR]
    have hj := callElse_jump (cr := []) hp hs hW (a.mono hlo2)
    have hj2 : Star ⟨callBranchPC pc cc [] (returnWords (D.sigNr n).erg (D.sigNr n).gruende) true, fp⟩ m2
        ⟨pc + BitVec.ofNat 64 (16 * (elseC (D.sigNr n) (frei Γ reserved) cc [] ce).length), fp⟩ m2 := by
      simpa using hj
    refine ⟨m2, st.trans hj2, (a.mono hlo2),
      envAt_agreeWIn hW hp.env a (Nat.le_refl _) (by have := hp.ctx; omega), hw2,
      keeps_of_agreeW hW a hpr (by omega)⟩
  · erw [hR]
    have ih := ihErr (ex := ex) ce te hce (by omega)
      (by simp only [elseC, List.length_append, List.length_singleton] at hs; omega) hW m2 _ σ' _ hp2
      (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega)
      (hu.agreeW hW a (by omega)) (hk.agreeW hW a (by omega)) hw2 hprE
    refine Sim.prefix hlo st (a.mono hlo2) (keeps_of_agreeW hW a hpr (by have := hW.ks; omega))
      (Ret.zuAusgang (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_))
    · simp only [Deklaration.erg, Deklaration.gruende, receiveC, copyWords_length, callBranchPC, elseC, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
    · simp only [Deklaration.erg, Deklaration.gruende, receiveC, copyWords_length, callBranchPC, elseC, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
  · erw [hR]; exact st
  · erw [hR]; exact st

theorem blockIndElse_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} {τ : Ty} {p : Expr D Γ Λ (.fnptr n)} {args : Args D Γ Λ (D.sigNr n).params}
    {he : (D.sigNr n).erg = some τ} {proof0 : RufPasst D (vertragVon D f) (D.sigNr n) Λ} {proof1 : 0 < (D.sigNr n).gruende}
    {err : Endblock D (vertragVon D f) l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ)}
    {rest : Block D (vertragVon D f) l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ'} :
    (∀ {pr ex}, EndCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex err) →
    (∀ {pr ex}, BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .bindCallIndElse p args he proof0 proof1 err rest) := by
  intro ihErr ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, ← hlo0, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, hce, ⟨cr, tr⟩, hcr, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [elseTopInd] at hK
  have hFB3 : FB = 4 := rfl
  have hFramePrefix := functionFrame_prefix P f
  have hpr' : ∀ j ∈ pr, j < frei (τ :: Γ) reserved := by
    intro j hj; have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega
  have hprE : ∀ j ∈ pr, j < frei (.why (D.sigNr n).gruende :: Γ) reserved := by
    intro j hj; have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega
  have hcall := callIndElse_ok hS hA p args he (σ.lese Λ (p.orte ++ args.orte)) hcc (by omega) hp hs hu hW hWa
  simp only [execBlock, indSonst]
  generalize pointerEq :
      eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pointer at hcall ⊢
  rcases pointer with ⟨callee, hf⟩
  dsimp only at hcall ⊢
  rcases hcall with
    ⟨σ', v, m2, hR, st, a, hp2, hw2⟩ | ⟨σ', r, m2, hR, st, a, hp2, hw2⟩ |
    ⟨e, hR, st⟩ | ⟨e, hR, st⟩
  · erw [hR]
    have ih := ihRest (ex := exPlus ex (ce.length + 1)) cr tr hcr (by omega)
      (by simp only [elseC, List.length_append, List.length_singleton] at hs; omega) hW m2 _ σ' _ hp2 hlo
      (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega)
      (hu.agreeW hW a (by omega)) (hk.agreeW hW a (by omega)) hw2 hpr'
    refine Sim.prefix hlo st (a.mono hlo2) (keeps_of_agreeW hW a hpr (by have := hW.ks; omega))
      (Sim.cont (Sim.schrumpf ih) (fun m3 a3 => callElse_jump hp hs hW ((a.mono hlo2).trans a3)) ?_ ?_)
    · simp only [Deklaration.erg, Deklaration.gruende, receiveC, copyWords_length, callBranchPC, exPlus, elseC, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq (by omega)
    · simp only [Deklaration.erg, Deklaration.gruende, receiveC, copyWords_length, callBranchPC, exPlus, elseC, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq (by omega)
  · erw [hR]
    have ih := ihErr (ex := ex) ce te hce (by omega)
      (by simp only [elseC, List.length_append, List.length_singleton] at hs; omega) hW m2 _ σ' _ hp2
      (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega)
      (hu.agreeW hW a (by omega)) (hk.agreeW hW a (by omega)) hw2 hprE
    refine Sim.prefix hlo st (a.mono hlo2) (keeps_of_agreeW hW a hpr (by have := hW.ks; omega))
      (Ret.zuAusgang (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_))
    · simp only [Deklaration.erg, Deklaration.gruende, receiveC, copyWords_length, callBranchPC, elseC, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
    · simp only [Deklaration.erg, Deklaration.gruende, receiveC, copyWords_length, callBranchPC, elseC, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
  · erw [hR]; exact st
  · erw [hR]; exact st

theorem endIndElse_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {n : Nat} {τ : Ty} {p : Expr D Γ Λ (.fnptr n)} {args : Args D Γ Λ (D.sigNr n).params}
    {he : (D.sigNr n).erg = some τ} {proof0 : RufPasst D (vertragVon D f) (D.sigNr n) Λ} {proof1 : 0 < (D.sigNr n).gruende}
    {err : Endblock D (vertragVon D f) l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ)}
    {rest : Endblock D (vertragVon D f) l (τ :: Γ) (nachSig D (D.sigNr n) Λ)} :
    (∀ {pr ex}, EndCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex err) →
    (∀ {pr ex}, EndCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    EndCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .bindCallIndElse p args he proof0 proof1 err rest) := by
  intro ihErr ihRest c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  simp only [lowEnd, ← hlo0, resultWords_vertragVon, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, hce, ⟨cr, tr⟩, hcr, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [elseTopInd] at hK
  have hFB3 : FB = 4 := rfl
  have hFramePrefix := functionFrame_prefix P f
  have hpr' : ∀ j ∈ pr, j < frei (τ :: Γ) reserved := by
    intro j hj; have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega
  have hprE : ∀ j ∈ pr, j < frei (.why (D.sigNr n).gruende :: Γ) reserved := by
    intro j hj; have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega
  have hcall := callIndElse_ok hS hA p args he (σ.lese Λ (p.orte ++ args.orte)) hcc (by omega) hp hs hu hW hWa
  simp only [execEnd, indSonstE]
  generalize pointerEq :
      eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pointer at hcall ⊢
  rcases pointer with ⟨callee, hf⟩
  dsimp only at hcall ⊢
  rcases hcall with
    ⟨σ', v, m2, hR, st, a, hp2, hw2⟩ | ⟨σ', r, m2, hR, st, a, hp2, hw2⟩ |
    ⟨e, hR, st⟩ | ⟨e, hR, st⟩
  · erw [hR]
    have ih := ihRest (ex := exPlus ex (ce.length + 1)) cr tr hcr (by omega)
      (by simp only [elseC, List.length_append, List.length_singleton] at hs; omega) hW m2 _ σ' _ hp2
      (by simp only [frei, contextWords_cons] at hlo ⊢; omega)
      (hu.agreeW hW a (by omega)) (hk.agreeW hW a (by omega)) hw2 hpr'
    refine Ret.prefix (by omega) st (a.mono hlo) (keeps_of_agreeW hW a hpr (by have := hW.ks; omega))
      (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_)
    · simp only [Deklaration.erg, Deklaration.gruende, receiveC, copyWords_length, callBranchPC, exPlus, elseC, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq (by omega)
    · simp only [Deklaration.erg, Deklaration.gruende, receiveC, copyWords_length, callBranchPC, exPlus, elseC, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq (by omega)
  · erw [hR]
    have ih := ihErr (ex := ex) ce te hce (by omega)
      (by simp only [elseC, List.length_append, List.length_singleton] at hs; omega) hW m2 _ σ' _ hp2
      (by simp only [frei, contextWords_cons] at hlo ⊢; omega)
      (hu.agreeW hW a (by omega)) (hk.agreeW hW a (by omega)) hw2 hprE
    refine Ret.prefix (by omega) st (a.mono hlo) (keeps_of_agreeW hW a hpr (by have := hW.ks; omega))
      (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_)
    · simp only [Deklaration.erg, Deklaration.gruende, receiveC, copyWords_length, callBranchPC, elseC, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
    · simp only [Deklaration.erg, Deklaration.gruende, receiveC, copyWords_length, callBranchPC, elseC, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
  · erw [hR]; exact st
  · erw [hR]; exact st

end Gabbro.Stage0.Senke
