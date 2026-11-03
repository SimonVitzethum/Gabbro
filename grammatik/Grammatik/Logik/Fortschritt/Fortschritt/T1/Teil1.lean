module
public import Grammatik.Logik.Fortschritt.Fortschritt.T1.Teil1Basis
import all Grammatik.Logik.Fortschritt.Fortschritt.T1.Teil1Basis

public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
section Inv

variable {P : Programm D} {O : Orakel D} {passes : Nat}

private theorem weiterOpt_fOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (e : Option Ty) (k : GRest D V l Γ Λ') :
    (GRest.weiterOpt (Λ := Λ) e k).fOk = k.fOk := by
  cases e <;> rfl

private theorem weiterOpt_absorb {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (e : Option Ty) (k : GRest D V l Γ Λ') :
    (GRest.weiterOpt (Λ := Λ) e k).absorb = k.absorb := by
  cases e <;> rfl

private theorem weiterOpt_blockiert {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (e : Option Ty) (k : GRest D V l Γ Λ') :
    (GRest.weiterOpt (Λ := Λ) e k).blockiert = k.blockiert := by
  cases e <;> rfl

set_option hygiene false in
/-- A head-local rule: the stack and the function are kept; the new head
    residue is in shape by Boolean bookkeeping over the old one. -/
macro "kopfLokal" : tactic => `(tactic| (
  simp only [rufUpdateG_self]
  obtain ⟨hk, hb, hst, hkt⟩ := h
  rw [‹(M.faeden f).kopf.rest = _›] at hk hb
  refine ⟨?_, ?_, hst, hkt⟩ <;> clear hst hkt hpopS <;>
  (revert hk hb
   simp only [weiterOpt_fOk, weiterOpt_absorb, weiterOpt_blockiert,
     GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Block.terminal,
     Stmt.istAbschluss, Endblock.alsBlock_terminal, Bool.and_eq_true, Bool.or_eq_true,
     Bool.not_eq_true', Bool.not_true, Bool.not_false, Bool.true_or, Bool.or_true,
     Bool.false_or, Bool.or_false]
   intro hk hb
   simp_all)))

/-- **Every rule keeps `FortInvG` of the acting thread.** -/
theorem fortInvG_schritt {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O passes M f M') (h : FortInvG (M.faeden f)) :
    FortInvG (M'.faeden f) := by
  have hpopS : ∀ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst →
      (caller.rest.2.2.2.2.fOk = true ∧ caller.rest.2.2.2.2.blockiert = false) ∧
        (∀ c ∈ rst, c.rest.2.2.2.2.fOk = true ∧ c.rest.2.2.2.2.blockiert = false) ∧
        FormG caller (M.faeden f).kopf.f ∧ FormKette caller.f rst := by
    intro caller rst hpop
    obtain ⟨_, _, hst, hkt⟩ := h
    rw [hpop] at hst hkt
    exact ⟨hst caller List.mem_cons_self, fun c hc => hst c (List.mem_cons_of_mem _ hc), hkt.1,
      hkt.2⟩
  cases hs with
  -- pops into a caller that does not wait
  | g1 hs =>
    cases hs with
    | rueck caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
      obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      exact ⟨hc.1, hc.2, hr, hkt⟩
    | ruf l Γ Λ g args hp hr rest ρ hhead =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_, ⟨Or.inl ⟨rfl, hr⟩, hkt⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨hk, rfl⟩
      · exact hst c hc
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep =>
      have ha := Stmt.istAbschluss_ok O passes keinRuf s _ _ _ _ hstep
      simp only [rufUpdateG_self]
      obtain ⟨hk, hb, hst, hkt⟩ := h
      rw [hhead] at hk hb
      refine ⟨?_, rfl, hst, hkt⟩
      revert hk
      simp only [GRest.fOk, Block.terminal, ha, Bool.false_or, imp_self]
    | _ => kopfLokal
  | g2 hs =>
    cases hs with
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_, ⟨Or.inl ⟨rfl, hr⟩, hkt⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · refine ⟨?_, rfl⟩
        revert hk
        simp only [GRest.fOk, Block.terminal, Stmt.istAbschluss, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, imp_self]
      · exact hst c hc
    | _ => kopfLokal
  | g3 hs =>
    cases hs with
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      refine ⟨?_, rfl, hr, hkt⟩
      have hc1 := hc.1
      clear hr hkt hpopS h
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] at hc1 <;>
        (revert hc1
         simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Bool.and_eq_true,
           Bool.or_eq_true, Bool.not_eq_true']
         intro hc1
         simp_all)
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_, ⟨Or.inl ⟨rfl, (D.passt_sig hg).gruende.trans hr⟩, hkt⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · refine ⟨?_, rfl⟩
        revert hk
        simp only [GRest.fOk, Block.terminal, Stmt.istAbschluss, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, imp_self]
      · exact hst c hc
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_, ⟨Or.inl ⟨rfl, (D.passt_sig hg).gruende.trans hr⟩, hkt⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨hk, rfl⟩
      · exact hst c hc
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_, ⟨Or.inr (Or.inl ⟨_, _, _, _, _, rest, k, ρ, rfl, he, hr⟩), hkt⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨hk, rfl⟩
      · exact hst c hc
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_, ⟨Or.inr (Or.inl ⟨_, _, _, _, _, rest, k, ρ, rfl,
        ergSig hg he, (D.passt_sig hg).gruende.trans hr⟩), hkt⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨hk, rfl⟩
      · exact hst c hc
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_,
        ⟨Or.inr (Or.inr ⟨_, _, _, _, _, _, err, rest, k, ρ, rfl, he, rfl⟩), hkt⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨hk, rfl⟩
      · exact hst c hc
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho
        hrho neu hneu =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_,
        ⟨Or.inr (Or.inr ⟨_, _, _, _, _, _, err, rest, k, ρ, rfl, ergSig hg he,
          (D.passt_sig hg).gruende⟩), hkt⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨hk, rfl⟩
      · exact hst c hc
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho
        hrho neu hneu =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_,
        ⟨Or.inr (Or.inr ⟨_, _, _, _, _, _, err, .nil, (.dann rest k), ρ, rfl, ergSig hg he,
          (D.passt_sig hg).gruende⟩), hkt⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · refine ⟨?_, rfl⟩
        revert hk
        simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert,
          Block.terminal, Stmt.istAbschluss, Bool.false_or, Bool.not_false,
          Bool.true_or, Bool.and_true, Bool.and_eq_true, Bool.or_eq_true,
          Bool.not_eq_true']
        intro hk
        simp_all
      · exact hst c hc
    -- a leaf in a block: it ended normally, so it was no return
    | _ => kopfLokal
  | g4 hs =>
    cases hs with
    | rueckCons caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
      obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      exact ⟨hc.1, hc.2, hr, hkt⟩
    | dannRet _ _ _ _ _ _ _ _ _ _ caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
      obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      exact ⟨hc.1, hc.2, hr, hkt⟩
    -- binding pops
    | dannRetBind _ _ _ _ _ _ _ _ _ _ caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      refine ⟨?_, rfl, hr, hkt⟩
      have hc1 := hc.1
      clear hr hkt hpopS h
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] at hc1 <;>
        (revert hc1
         simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Bool.and_eq_true,
           Bool.or_eq_true, Bool.not_eq_true']
         intro hc1
         simp_all)
    | rueckConsBind _ _ _ _ _ _ _ _ caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      refine ⟨?_, rfl, hr, hkt⟩
      have hc1 := hc.1
      clear hr hkt hpopS h
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] at hc1 <;>
        (revert hc1
         simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Bool.and_eq_true,
           Bool.or_eq_true, Bool.not_eq_true']
         intro hc1
         simp_all)
    -- reason pops
    | rueckGrund _ _ _ _ caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      refine ⟨?_, rfl, hr, hkt⟩
      have hc1 := hc.1
      rw [hcaller] at hc1
      clear hr hkt hpopS h
      revert hc1
      simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Bool.and_eq_true,
        Bool.or_eq_true, Bool.not_eq_true', Endblock.alsBlock_terminal, Bool.or_true, and_true]
      intro hc1
      simp_all
    | _ => kopfLokal
  | g5 hs =>
    cases hs with
    | rueckConsGrund _ _ _ _ _ _ _ caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      refine ⟨?_, rfl, hr, hkt⟩
      have hc1 := hc.1
      rw [hcaller] at hc1
      clear hr hkt hpopS h
      revert hc1
      simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Bool.and_eq_true,
        Bool.or_eq_true, Bool.not_eq_true', Endblock.alsBlock_terminal, Bool.or_true, and_true]
      intro hc1
      simp_all
    | dannRetGrund _ _ _ _ _ _ _ _ caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      refine ⟨?_, rfl, hr, hkt⟩
      have hc1 := hc.1
      rw [hcaller] at hc1
      clear hr hkt hpopS h
      revert hc1
      simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Bool.and_eq_true,
        Bool.or_eq_true, Bool.not_eq_true', Endblock.alsBlock_terminal, Bool.or_true, and_true]
      intro hc1
      simp_all
    -- pushes
    | _ => kopfLokal
  | g6 hs =>
    cases hs with
    | _ => kopfLokal
  | g7 hs =>
    cases hs with
    | _ => kopfLokal

/-- Every rule keeps `FortInvG` at every thread. -/
theorem fortInvG_schritt_alle {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O passes M f M') (h : ∀ g, FortInvG (M.faeden g)) :
    ∀ g, FortInvG (M'.faeden g) := by
  intro g
  by_cases hg : g = f
  · subst hg
    exact fortInvG_schritt hs (h g)
  · rw [rufSchrittG_fremd hs g hg]
    exact h g

/-- **`FortInvG` holds on every reachable machine.** -/
theorem fortInvG_erreichbar (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    ∀ t, FortInvG (M.faeden t) := by
  induction hr with
  | start =>
      intro t
      rw [start_faden]
      exact ⟨rfl, rfl, fun c hc => absurd hc List.not_mem_nil, trivial⟩
  | schritt M M' u _ hs ih => exact fortInvG_schritt_alle hs ih

end Inv
/-! ## 4. Leaves -/

/-- An axiom's answer world extends the trace by accesses only (`GutO`,
    with the call's guards held). -/
theorem axiom_erw {O : Orakel D} (hO : GutO O) (a : D.Ax) (σ : World D)
    (ρ : Env D (D.aparams a)) {Λ : List (Res D)}
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (hh : HeldIn Λ σ.haelt) :
    Erw σ (O.wirkt a σ ρ).1 := by
  obtain ⟨tabs, globs, Λe, -, -, -, -, -, -, hsp⟩ := (hO a σ ρ).2.2
    (fun t hwr L hL => hh L (hd t hwr _ hL)) (fun g hwr L hL => hh L (hgd g hwr _ hL))
  refine ⟨_, hsp, fun e he => ?_⟩
  rcases axiomSpur_mem he with ⟨t, _, _, rfl⟩ | ⟨g, _, _, rfl⟩ <;> rfl

end Gabbro.Grammatik
