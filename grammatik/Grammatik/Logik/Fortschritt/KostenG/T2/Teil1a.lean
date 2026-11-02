module

public import Grammatik.Logik.Fortschritt.KostenG.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **One own step of the head: the potential argument, per rule of G.** A push through a direct call charges
    the callee's cost `c g`; one through an indirect call (signature `n`, admitted by `ZS n`) charges nothing for
    the callee, whose cost the model does not name. -/
theorem schrittArt {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O pa M f M') (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    ((M'.faeden f).stapel = (M.faeden f).stapel ∧
      (rufeR Z ZS EW (M.faeden f).kopf.rest.2.2.2.2 = true →
        rufeR Z ZS EW (M'.faeden f).kopf.rest.2.2.2.2 = true ∧
        potRest c pa (M'.faeden f).kopf.rest.2.2.2.2 + 1 ≤
          potRest c pa (M.faeden f).kopf.rest.2.2.2.2)) ∨
    (∃ (g : D.Fn) (caller' : RufRahmenG D) (rho : Env D (D.params g)) (s0 : World D),
      (M'.faeden f).stapel = caller' :: (M.faeden f).stapel ∧
      (M'.faeden f).kopf = ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
        rho, .ende (P.rumpf g)⟩⟩ ∧
      (rufeR Z ZS EW (M.faeden f).kopf.rest.2.2.2.2 = true →
        rufeR Z ZS EW caller'.rest.2.2.2.2 = true ∧
        ((Z g = true ∧ potRest c pa caller'.rest.2.2.2.2 + 1 + c g ≤
            potRest c pa (M.faeden f).kopf.rest.2.2.2.2) ∨
          (∃ n, ZS n = true ∧ D.passt g n = true ∧
            potRest c pa caller'.rest.2.2.2.2 + 1 ≤ potRest c pa (M.faeden f).kopf.rest.2.2.2.2)))) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst ∧ (M'.faeden f).stapel = rst ∧
      ∀ (c' : D.Fn → Nat) (Z' : D.Fn → Bool) (ZS' : Nat → Bool) (EW' : Bool),
        (rufeR Z' ZS' EW' caller.rest.2.2.2.2 = true →
          rufeR Z' ZS' EW' (M'.faeden f).kopf.rest.2.2.2.2 = true) ∧
        potRest c' pa (M'.faeden f).kopf.rest.2.2.2.2 ≤ potRest c' pa caller.rest.2.2.2.2) := by
  cases hs with
  | g1 hs =>
    cases hs with
    | blatt l Γ Λ Λ' s rest ρ hleaf hhead =>
      kopfA
      · simp_all
      · have := kostenStmt_pos c pa s; omega
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead =>
      kopfA
      · simp_all
      · have := kostenStmt_pos c pa s; omega
    | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
      kopfA
      · simp_all
      · rw [entfZ_wahr hent]; omega
    | endeForm l Γ Λ e ρ hl hent hhead =>
      kopfA
      · cases e <;> try (simp only [EndEntfaltbar, Bool.false_eq_true] at hent; done)
        all_goals simp_all [rufeB_alsBlock, rufeR]
      · cases e <;> try (simp only [EndEntfaltbar, Bool.false_eq_true] at hent; done)
        all_goals (simp only [potRest, kostenBlock_alsBlock, kostenEnd, kostenSonst]; omega)
    | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw =>
      kopfA
      · have h := rufeB_armWahlG Z ZS EW arms (eval σ₁ v σ₁ ρ) hok.1.1
        rw [hw] at h
        have h2 : rufeB Z ZS EW b = true := h
        simp_all
      · have h := kostenBlock_armWahlG c pa arms (eval σ₁ v σ₁ ρ)
        rw [hw] at h
        have h2 : kostenBlock c pa b ≤ kostenArms c pa arms := h
        omega
    | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw =>
      kopfA
      · have h := rufeB_armWahlG Z ZS EW arms (eval σ₁ v σ₁ ρ) hok.1.1
        rw [hw] at h
        have h2 : rufeB Z ZS EW b = true := h
        simp_all
      · have h := kostenBlock_armWahlG c pa arms (eval σ₁ v σ₁ ρ)
        rw [hw] at h
        have h2 : kostenBlock c pa b ≤ kostenArms c pa arms := h
        omega
    | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw =>
      kopfA
      · have h := rufeB_grundWahlG Z ZS EW arms (eval σ₁ r σ₁ ρ) hok.1.1
        rw [hw] at h
        simp_all
      · have h := kostenBlock_grundWahlG c pa arms (eval σ₁ r σ₁ ρ)
        rw [hw] at h
        omega
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      · rw [hhead] at hok ⊢
        dsimp only at hok ⊢
        simp only [potRest, kostenEnd, kostenStmt, rufeR, rufeE, rufeS, Bool.and_eq_true] at hok ⊢
        exact ⟨hok.2, Or.inl ⟨hok.1, by omega⟩⟩
    | rueck caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        fun c' Z' ZS' EW' => ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact ⟨id, Nat.le_refl _⟩
    | _ =>
      kopfA
      · cases EW <;> simp_all
      · omega
  | g2 hs =>
    cases hs with
    | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
      kopfA
      · simp_all
      · have h : @List.length (Wert D (.index (D.count t))) (alleIndizes (D.count t)) *
            (kostenBlock c pa body + kostenExpr inv + 2) ≤
            (D.count t).toNat * (kostenBlock c pa body + kostenExpr inv + 2) :=
          Nat.mul_le_mul_right _ (alleIndizes_length_toNat (D.count t))
        omega
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      · rw [hhead] at hok ⊢
        dsimp only at hok ⊢
        simp only [potRest, kostenBlock, kostenStmt, rufeR, rufeB, rufeS,
          Bool.and_eq_true] at hok ⊢
        exact ⟨⟨hok.1.2, hok.2⟩, Or.inl ⟨hok.1.1, by omega⟩⟩
    | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
      kopfA
      · simp_all
      · have := kostenBlock_pos c pa ueber
        have hm : max 1 (kostenBlock c pa ueber) = kostenBlock c pa ueber := Nat.max_eq_right this
        omega
    | _ =>
      kopfA
      · cases EW <;> simp_all
      · omega
  | g3 hs =>
    cases hs with
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      · rw [hhead] at hok ⊢
        dsimp only at hok ⊢
        simp only [potRest, kostenBlock, rufeR, rufeB, Bool.and_eq_true] at hok ⊢
        exact ⟨⟨hok.1.2, hok.2⟩, Or.inl ⟨hok.1.1, by omega⟩⟩
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      · rw [hhead] at hok ⊢
        dsimp only at hok ⊢
        simp only [potRest, kostenBlock, rufeR, rufeB, Bool.and_eq_true] at hok ⊢
        exact ⟨⟨⟨hok.1.1.2, hok.1.2⟩, hok.2⟩, Or.inl ⟨hok.1.1.1, by omega⟩⟩
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      · rw [hhead] at hok ⊢
        dsimp only at hok ⊢
        simp only [potRest, kostenBlock, kostenStmt, rufeR, rufeB, rufeS, Bool.and_eq_true] at hok ⊢
        exact ⟨⟨hok.1.2, hok.2⟩, Or.inr ⟨n, hok.1.1, hg, by omega⟩⟩
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      · rw [hhead] at hok ⊢
        dsimp only at hok ⊢
        simp only [potRest, kostenEnd, kostenStmt, rufeR, rufeE, rufeS, Bool.and_eq_true] at hok ⊢
        exact ⟨hok.2, Or.inr ⟨n, hok.1, hg, by omega⟩⟩
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      · rw [hhead] at hok ⊢
        dsimp only at hok ⊢
        simp only [potRest, kostenBlock, rufeR, rufeB, Bool.and_eq_true] at hok ⊢
        exact ⟨⟨hok.1.2, hok.2⟩, Or.inr ⟨n, hok.1.1, hg, by omega⟩⟩
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err rest k⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      · rw [hhead] at hok ⊢
        dsimp only at hok ⊢
        simp only [potRest, kostenBlock, rufeR, rufeB, Bool.and_eq_true] at hok ⊢
        exact ⟨⟨⟨hok.1.1.2, hok.1.2⟩, hok.2⟩, Or.inr ⟨n, hok.1.1.1, hg, by omega⟩⟩
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
      refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
        ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err .nil
          (.dann rest k)⟩⟩, rho, s0,
        by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
      · rw [hhead] at hok ⊢
        dsimp only at hok ⊢
        simp only [potRest, kostenBlock, kostenStmt, rufeR, rufeB, rufeS, Bool.and_eq_true] at hok ⊢
        exact ⟨⟨⟨hok.1.1.2, rfl⟩, hok.1.2, hok.2⟩, Or.inr ⟨n, hok.1.1.1, hg, by omega⟩⟩
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        fun c' Z' ZS' EW' => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
        simp only [potRest, rufeR, Bool.and_eq_true] <;> exact ⟨fun h => by simp_all, by omega⟩
    | _ =>
      kopfA
      · cases EW <;> simp_all
      · omega
  | g4 hs =>
    cases hs with
    | rueckCons caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        fun c' Z' ZS' EW' => ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact ⟨id, Nat.le_refl _⟩
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        fun c' Z' ZS' EW' => ?_⟩)
      dsimp only; rw [rufUpdateG_self]
      exact ⟨id, Nat.le_refl _⟩
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        fun c' Z' ZS' EW' => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
        simp only [potRest, rufeR, Bool.and_eq_true] <;> exact ⟨fun h => by simp_all, by omega⟩
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        fun c' Z' ZS' EW' => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
        simp only [potRest, rufeR, Bool.and_eq_true] <;> exact ⟨fun h => by simp_all, by omega⟩
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        fun c' Z' ZS' EW' => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller]; dsimp only
      simp only [potRest, rufeR, kostenBlock_alsBlock, rufeB_alsBlock, Bool.and_eq_true]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, by omega⟩
    | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
      kopfA
      · simp_all
      · have := kostenBlock_pos c pa rest; have := kostenBlock_pos c pa b; omega
    | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
      kopfA
      · simp_all
      · have := kostenBlock_pos c pa rest; have := kostenBlock_pos c pa b; omega
    | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
      kopfA
      · simp_all
      · have := kostenBlock_pos c pa rest; omega
    | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
      kopfA
      · simp_all
      · have := kostenBlock_pos c pa rest; omega
    | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
      kopfA
      · simp_all
      · have := kostenBlock_pos c pa rest; omega
    | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
      kopfA
      · simp_all
      · have := kostenBlock_pos c pa rest; omega
    | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
      kopfA
      · simp_all
      · have := kostenBlock_pos c pa rest; omega
    | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
      kopfA
      · simp_all
      · have := kostenBlock_pos c pa rest; omega
    | _ =>
      kopfA
      · cases EW <;> simp_all
      · omega
  | g5 hs =>
    cases hs with
    | dannBindAxiomOpt _ _ l Γ Λ Λ' e =>
      cases e <;> kopfA
      all_goals first | (solve | simp_all) | omega
    | dannBindAxiomOptElseOk _ _ l Γ Λ Λ' e =>
      cases e <;> kopfA
      all_goals first | (solve | simp_all) | omega
    | rueckConsGrund _ _ r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        fun c' Z' ZS' EW' => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller]; dsimp only
      simp only [potRest, rufeR, kostenBlock_alsBlock, rufeB_alsBlock, Bool.and_eq_true]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, by omega⟩
    | dannRetGrund _ _ r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
      refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
        fun c' Z' ZS' EW' => ?_⟩)
      dsimp only; rw [rufUpdateG_self]; dsimp only
      rw [hcaller]; dsimp only
      simp only [potRest, rufeR, kostenBlock_alsBlock, rufeB_alsBlock, Bool.and_eq_true]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, by omega⟩
    | _ =>
      kopfA
      · cases EW <;> simp_all
      · omega
  | g6 hs =>
    cases hs with
    | _ =>
      kopfA
      · cases EW <;> simp_all
      · omega
/-! ## 6. Counting one thread's steps -/

/- `RufErreichbarG` lives in `Prop`, so no function can count the steps of
    its derivations. `SegLauf` is the `Type`-valued twin: the same steps,
    made explicit, so `segZaehle` can count one thread's firings.
    `segLauf_erreichbar` forgets back, and `erreichbar_segLauf` is the
    converse (as a `Nonempty`): "any reachable run" and "any `SegLauf`"
    are the same runs. -/
inductive SegLauf (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 : RufMaschineG D) : RufMaschineG D → Type where
  | start : SegLauf P O passes M0 M0
  | schritt (M M' : RufMaschineG D) (f : Faden)
      (h : SegLauf P O passes M0 M) (hs : RufSchrittG P O passes M f M') :
      SegLauf P O passes M0 M'


end Gabbro.Grammatik
