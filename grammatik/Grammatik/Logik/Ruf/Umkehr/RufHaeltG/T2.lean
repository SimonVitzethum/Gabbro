/- Part 2 of 3 of `RufHaeltG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufHaeltG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

set_option maxHeartbeats 1000000 in
/-- **Every rule keeps the thread invariant of the acting thread.** -/
theorem rufSchrittG_haeltInv {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (h : HaeltInvG (M.faeden f)) : HaeltInvG (M'.faeden f) := by
  have hk0 := h.2.1 _ List.mem_cons_self
  have hh0 := h.kopf
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have ho : offen σ'.spur = offen (M.faeden f).spur :=
      (Stmt.gut_blatt O passes keinRuf hO s hleaf (M.weltVon f) ρ hΛ σ'
        (by rw [hstep]; rfl)).2.1
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) (nennt_stmt s hk) ?_
    rw [ho]; exact heldIn_stmt s hh
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_push h _ _ _ _ rfl (nach_nennt hk) (by fr_push) (callee_kette P g rho s0) rfl
      (by rw [hs0, offen_lese]; rfl) (nach_held hh) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | rueck caller rst hpop Γ Λ e hperm ρ _ g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
    simp only [rufUpdateG_self]
    exact haeltInvG_pop_gleich h hpop _ _ (by rw [hs1, offen_lese]; rfl)
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk, nennt_stmt s hk⟩ hh
  | endeForm l Γ Λ e ρ hl hent hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac)
      (kette_abbruch _ hk (GRest.leer (Λ := Λ)) hk (fun L hL => hL)) hh
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have ho : offen σ'.spur = offen (M.faeden f).spur :=
      (Stmt.gut_blatt O passes keinRuf hO s hleaf (M.weltVon f) ρ hΛ σ'
        (by rw [hstep]; rfl)).2.1
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨nennt_stmt s hk.1, hk.2⟩ ?_
    rw [ho]; exact heldIn_stmt s hh
  | dannLeer l Γ Λ k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2 hh
  | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block t hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block e hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block p hk.1, nennt_block p hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block a hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block b hk.1, nennt_block b hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block b hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block b hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk ?_
    rw [hs₁, offen_lese]; exact hh
  | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk ?_
    rw [axiom_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]; exact hh
  | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac)
      (kette_abbruch _ hk.1 k hk.2 (fun L hL => (Block.held_iff rest L).mp hL)) ?_
    rw [hs₁, offen_lese]; exact hh
  | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk ?_
    rw [hs₁, offen_lese]; exact hh
  | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac)
      (kette_abbruch _ hk.1 k hk.2 (fun L hL => (Block.held_iff rest L).mp hL)) ?_
    rw [hs₁, offen_lese]; exact hh
  | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, nennt_block body hk.1, hk.2⟩ hh
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have hL : Res.held L ∉ Λ := fun hm => hself (hh L hm)
    refine haeltInvG_kopf h (fun K hK _ => List.mem_cons_of_mem _ hK)
      (fun K hK => by
        rw [freis_von hhead]
        simp only [GRest.freis, List.mem_cons] at hK ⊢
        rcases hK with rfl | hK
        · exact .inr hself
        · exact .inl hK) ⟨fun K hK => List.mem_cons_of_mem _ (hk.1 K hK), hL, hk⟩ ?_
    intro K hK
    rcases List.mem_cons.mp hK with hK | hK
    · cases hK; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hh K hK)
  | freiGib l Γ Λ L k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (fun K hK hnf => (List.mem_erase_of_ne (fun e => hnf (by
        rw [freis_von hhead]; simp [GRest.freis, e]))).mpr hK) (by fr_tac) hk.2 ?_
    intro K hK
    have hKL : K ≠ L := fun e => hk.1 (e ▸ hK)
    exact (List.mem_erase_of_ne hKL).mpr (hh K (List.mem_cons_of_mem _ hK))
  | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2 hh
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, hk.1, hk.2⟩ hh
  | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | travFort l Γ Λ t inv body is k i ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) hk hh
  | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2 ?_
    rw [hs₁, offen_lese]; exact hh
  | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, hk.1, hk.2⟩ hh
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) hk hh
  | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2 ?_
    rw [hs₁, offen_lese]; exact hh
  | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) hk hh
  | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, hk.1, hk.2⟩ hh
  | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, hk.1, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | ewigFort l Γ Λ a n inv body k ρ hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) hk hh
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_push h _ _ _ _ rfl ⟨nach_nennt hk.1, hk.2⟩ (by fr_push) (callee_kette P g rho s0) rfl
      (by rw [hs0, offen_lese]; rfl) (nach_held hh) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    subst hg
    refine haeltInvG_push h _ _ _ _ rfl ⟨nach_nennt hk.1, hk.2⟩ (by fr_push) (callee_kette P g rho s0) rfl
      (by rw [hs0, offen_lese]; rfl) (nach_held hh) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    subst hg
    refine haeltInvG_push h _ _ _ _ rfl (nach_nennt hk) (by fr_push) (callee_kette P g rho s0) rfl
      (by rw [hs0, offen_lese]; rfl) (nach_held hh) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_push h _ _ _ _ rfl ⟨nach_nennt hk.1, hk.2⟩ (by fr_push) (callee_kette P g rho s0) rfl
      (by rw [hs0, offen_lese]; rfl) (nach_held hh) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
      neu hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    subst hg
    refine haeltInvG_push h _ _ _ _ rfl ⟨nach_nennt hk.1, hk.2⟩ (by fr_push) (callee_kette P g rho s0) rfl
      (by rw [hs0, offen_lese]; rfl) (nach_held hh) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
      hneu =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_push h _ _ _ _ rfl ⟨nach_nennt hk.1, hk.2⟩ (by fr_push) (callee_kette P g rho s0) rfl
      (by rw [hs0, offen_lese]; rfl) (nach_held hh) ?_
    rw [hs0, offen_lese]; exact callee_held hp hh
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ _ g hfg rho hrho s0
      hs0 hΛ s1 hs1 v hv he neu hneu =>
    simp only [rufUpdateG_self]
    have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
      h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hck : (GRest.dann restb (.schrumpf k) :
        GRest D (vertragVon D caller.f) l (τ :: Γ) Λ).kette (D.haelt caller.f) := by
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩
      · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
      · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
    refine haeltInvG_pop h hpop _ _ _ rfl ?_ (by fr_pop) hck (by rw [hs1, offen_lese]; rfl)
    intro L hL
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] <;> exact hL
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁
      hw neu₁ hneu₁ hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have e := leave_welt' O passes keinRuf _ _ hleave σ' ρ' hstep
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2.2 ?_
    rw [hs₁, offen_lese, e]; exact heldIn_block rest hh
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have e := next_welt' O passes keinRuf _ _ hnext σ' ρ' hstep
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2 ?_
    rw [e]; exact heldIn_block rest hh
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have e := leave_welt' O passes keinRuf _ _ hleave σ' ρ' hstep
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2.2 ?_
    rw [e]; exact heldIn_block rest hh
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have e := next_welt' O passes keinRuf _ _ hnext σ' ρ' hstep
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2 ?_
    rw [e]; exact heldIn_block rest hh
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have e := leave_welt' O passes keinRuf _ _ hleave σ' ρ' hstep
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2.2 ?_
    rw [e]; exact heldIn_block rest hh
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    have e := next_welt' O passes keinRuf _ _ hnext σ' ρ' hstep
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk.2 ?_
    rw [e]; exact heldIn_block rest hh
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨GRest.kette_top k hk.2.2, hk.2.2⟩
      (heldIn_block b (heldIn_block rest hh))
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨GRest.kette_top k hk.2.2, hk.2.2⟩
      (heldIn_block b (heldIn_block rest hh))
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨GRest.kette_top k hk.2.2, hk.2.2⟩ (heldIn_block rest hh)
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨GRest.kette_top k hk.2.2, hk.2.2⟩ (heldIn_block rest hh)
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (fun K hK hnf => (List.mem_erase_of_ne (fun e => hnf (by
        rw [freis_von hhead]; simp [GRest.freis, e]))).mpr hK) (by fr_tac) ⟨GRest.kette_top k hk.2.2, hk.2.2⟩ ?_
    intro K hK
    have hKL : K ≠ L := fun e => hk.2.1 (e ▸ hK)
    exact (List.mem_erase_of_ne hKL).mpr
      (heldIn_block rest hh K (List.mem_cons_of_mem _ hK))
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (fun K hK hnf => (List.mem_erase_of_ne (fun e => hnf (by
        rw [freis_von hhead]; simp [GRest.freis, e]))).mpr hK) (by fr_tac) ⟨GRest.kette_top k hk.2.2, hk.2.2⟩ ?_
    intro K hK
    have hKL : K ≠ L := fun e => hk.2.1 (e ▸ hK)
    exact (List.mem_erase_of_ne hKL).mpr
      (heldIn_block rest hh K (List.mem_cons_of_mem _ hK))
  | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hl hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨GRest.kette_top k hk.2.2.2, hk.2.2.2⟩ ?_
    exact fun L hL => heldIn_block rest hh L (hk.2.2.1 L hL)
  | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hl hhead =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨GRest.kette_top k hk.2.2.2, hk.2.2.2⟩ ?_
    exact fun L hL => heldIn_block rest hh L (hk.2.2.1 L hL)
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
      neu hneu hnw =>
    simp only [rufUpdateG_self]
    exact haeltInvG_pop_gleich h hpop _ _ (by rw [hs1, offen_lese]; rfl)
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ _ g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu
      hnw =>
    simp only [rufUpdateG_self]
    exact haeltInvG_pop_gleich h hpop _ _ (by rw [hs1, offen_lese]; rfl)
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    simp only [rufUpdateG_self]
    have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
      h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hck : (GRest.dann restb (.schrumpf k) :
        GRest D (vertragVon D caller.f) l (τ :: Γ) Λ).kette (D.haelt caller.f) := by
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩
      · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
      · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
    refine haeltInvG_pop h hpop _ _ _ rfl ?_ (by fr_pop) hck (by rw [hs1, offen_lese]; rfl)
    intro L hL
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] <;> exact hL
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
      s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    simp only [rufUpdateG_self]
    have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
      h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hck : (GRest.dann restb (.schrumpf k) :
        GRest D (vertragVon D caller.f) l (τ :: Γ) Λ).kette (D.haelt caller.f) := by
      rcases hcaller with hcaller | ⟨_, _, hcaller⟩
      · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
      · have := kette_von hcaller hc; exact ⟨this.1, GRest.kette_top k this.2, this.2⟩
    refine haeltInvG_pop h hpop _ _ _ rfl ?_ (by fr_pop) hck (by rw [hs1, offen_lese]; rfl)
    intro L hL
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] <;> exact hL
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho
      hrho s0 hs0 rg hrg hn =>
    simp only [rufUpdateG_self]
    have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
      h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hcw := kette_von hcaller hc
    have hck := kette_abbruch (Endblock.alsBlock err).2 hcw.1 (.schrumpf k)
      ⟨GRest.kette_top k hcw.2, hcw.2⟩ (fun L hL => (Block.held_iff restb L).mp hL)
    refine haeltInvG_pop h hpop _ _ _ rfl ?_ (by fr_pop) hck rfl
    intro L hL
    rw [hcaller]; exact hL
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    simp only [rufUpdateG_self]
    have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
      h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hcw := kette_von hcaller hc
    have hck := kette_abbruch (Endblock.alsBlock err).2 hcw.1 (.schrumpf k)
      ⟨GRest.kette_top k hcw.2, hcw.2⟩ (fun L hL => (Block.held_iff restb L).mp hL)
    refine haeltInvG_pop h hpop _ _ _ rfl ?_ (by fr_pop) hck rfl
    intro L hL
    rw [hcaller]; exact hL
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    simp only [rufUpdateG_self]
    have hc : caller.rest.2.2.2.2.kette (D.haelt caller.f) :=
      h.2.1 caller (by rw [hpop]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hcw := kette_von hcaller hc
    have hck := kette_abbruch (Endblock.alsBlock err).2 hcw.1 (.schrumpf k)
      ⟨GRest.kette_top k hcw.2, hcw.2⟩ (fun L hL => (Block.held_iff restb L).mp hL)
    refine haeltInvG_pop h hpop _ _ _ rfl ?_ (by fr_pop) hck rfl
    intro L hL
    rw [hcaller]; exact hL
  | dannRegLies l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ hh
  | dannRegLiesElseWahr l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac)
      (kette_abbruch _ hk.1 k hk.2 (fun L hL => (Block.held_iff rest L).mp hL)) ?_
    rw [hs₁, offen_lese]; exact hh
  | dannAwaits l Γ Λ Λ' g payload hp hL rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₂, offen_schreibGlob, hs₁, offen_lese]; exact hh
  | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    exact haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ hh
  | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [hs₁, offen_lese]; exact hh
  | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac)
      (kette_abbruch _ hk.1 k hk.2 (fun L hL => (Block.held_iff rest L).mp hL)) ?_
    rw [hs₁, offen_lese]; exact hh
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [axiom_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]; exact hh
  | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu
      hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) ⟨hk.1, GRest.kette_top k hk.2, hk.2⟩ ?_
    rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]; exact hh
  | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax
      neu hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac)
      (kette_abbruch _ hk.1 (.schrumpf k) ⟨GRest.kette_top k hk.2, hk.2⟩
        (fun L hL => (Block.held_iff rest L).mp hL)) ?_
    rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]; exact hh
  | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu
      hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk ?_
    rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]; exact hh
  | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu
      hneu hΛ =>
    simp only [rufUpdateG_self]
    have hk := kette_von hhead hk0
    have hh := heldIn_von hhead hh0
    refine haeltInvG_kopf h (by ho_tac) (by fr_tac) hk ?_
    rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁, offen_lese]; exact hh


end Gabbro.Grammatik
