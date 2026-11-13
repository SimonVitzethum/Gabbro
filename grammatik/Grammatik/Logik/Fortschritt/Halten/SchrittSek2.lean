/-
  File:      Grammatik/Logik/Fortschritt/Halten/SchrittSek2.lean
  Subject:   ONE OWN STEP OF A SECTION'S FRAME, rule groups G4-G7, and `schrittSek` over all of G. A `leave` or
             `next` that peels the release marker of `L` releases `L` (excluded: `L` stays held); one that
             peels another lock's marker is `schrittArt`'s case. A scoped `return` turns the residue into a
             cleanup of all its markers, paid by `potSek`'s count of the markers behind `L`
             (`GRest.scopedWert_budgetSek`).
-/
module
public import Grammatik.Logik.Fortschritt.Halten.SchrittSek1
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Gruppen

variable (L : D.Lock) {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D} {f : Faden}

set_option linter.unusedVariables false

set_option maxHeartbeats 4000000 in
/-- Rule group G4: returns, `leave`/`next` peeling. -/
theorem schrittSek4 (hs : RufSchrittG4 P O pa M f M') (hb : RestScopeBalance (M.faeden f).kopf.rest)
    (hL : L ∈ offen (M.faeden f).spur) (hL' : L ∈ offen (M'.faeden f).spur)
    (hnd : (offen (M.faeden f).spur).Nodup)
    (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    SekArt L P pa M M' f ep c Z ZS EW := by
  unfold SekArt
  cases hs with
  | rueckCons caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun ep c' Z' ZS' EW' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact ⟨id, Nat.le_refl _⟩
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun ep c' Z' ZS' EW' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact ⟨id, Nat.le_refl _⟩
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun ep c' Z' ZS' EW' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [potSek, rufeV, Bool.and_eq_true] <;> exact ⟨fun h => by simp_all, by omega⟩
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun ep c' Z' ZS' EW' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [potSek, rufeV, Bool.and_eq_true] <;> exact ⟨fun h => by simp_all, by omega⟩
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun ep c' Z' ZS' EW' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [potSek, rufeV, kostenBlock_alsBlock, rufeB_alsBlock, Bool.and_eq_true]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, by omega⟩
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
    kopfS
    · simp_all
    · have := kostenBlock_pos ep c pa rest; have := kostenBlock_pos ep c pa b; omega
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
    kopfS
    · simp_all
    · have := kostenBlock_pos ep c pa rest; have := kostenBlock_pos ep c pa b; omega
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
    kopfS
    · simp_all
    · have := kostenBlock_pos ep c pa rest; omega
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
    kopfS
    · simp_all
    · have := kostenBlock_pos ep c pa rest; omega
  | peelFreiLeave l Γ Λ L' rest k ρ hleave hhead =>
    by_cases hne : L' = L
    · exfalso
      simp only [rufUpdateG_self, offen] at hL'
      rw [hne] at hL'
      exact hnd.not_mem_erase hL'
    · kopfSn
      · simp_all
      · have := kostenBlock_pos ep c pa rest; omega
  | peelFreiNext l Γ Λ L' rest k ρ hnext hhead =>
    by_cases hne : L' = L
    · exfalso
      simp only [rufUpdateG_self, offen] at hL'
      rw [hne] at hL'
      exact hnd.not_mem_erase hL'
    · kopfSn
      · simp_all
      · have := kostenBlock_pos ep c pa rest; omega
  | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
    kopfS
    · simp_all
    · have := kostenBlock_pos ep c pa rest; omega
  | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
    kopfS
    · simp_all
    · have := kostenBlock_pos ep c pa rest; omega
  | _ =>
    kopfS
    · cases EW <;> simp_all
    · omega

set_option maxHeartbeats 4000000 in
/-- Rule group G5: foreign calls, registers, floats, reason returns. -/
theorem schrittSek5 (hs : RufSchrittG5 P O pa M f M') (hb : RestScopeBalance (M.faeden f).kopf.rest)
    (hL : L ∈ offen (M.faeden f).spur) (hL' : L ∈ offen (M'.faeden f).spur)
    (hnd : (offen (M.faeden f).spur).Nodup)
    (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    SekArt L P pa M M' f ep c Z ZS EW := by
  unfold SekArt
  cases hs with
  | dannBindAxiomOpt _ _ l Γ Λ Λ' e a args he hp hd hgd rest k ρ hhead
      σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    cases e <;> kopfS
    all_goals (try dsimp only [ErgCtx, GRest.weiterOpt] at *)
    all_goals first | (solve | simp_all) | omega
  | dannBindAxiomOptElseOk _ _ l Γ Λ Λ' e a args he hr hp hd hgd err rest k ρ hhead
      σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    cases e <;> kopfS
    all_goals (try dsimp only [ErgCtx, GRest.weiterOpt] at *)
    all_goals first | (solve | simp_all) | omega
  | rueckConsGrund _ _ r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun ep c' Z' ZS' EW' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [potSek, rufeV, kostenBlock_alsBlock, rufeB_alsBlock, Bool.and_eq_true]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, by omega⟩
  | dannRetGrund _ _ r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun ep c' Z' ZS' EW' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [potSek, rufeV, kostenBlock_alsBlock, rufeB_alsBlock, Bool.and_eq_true]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, by omega⟩
  | _ =>
    kopfS
    · cases EW <;> simp_all
    · omega

set_option maxHeartbeats 4000000 in
/-- Rule group G6: end-position foreign binders and floats. -/
theorem schrittSek6 (hs : RufSchrittG6 P O pa M f M') (hb : RestScopeBalance (M.faeden f).kopf.rest)
    (hL : L ∈ offen (M.faeden f).spur) (hL' : L ∈ offen (M'.faeden f).spur)
    (hnd : (offen (M.faeden f).spur).Nodup)
    (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    SekArt L P pa M M' f ep c Z ZS EW := by
  unfold SekArt
  cases hs with
  | _ =>
    kopfS
    · cases EW <;> simp_all
    · omega

set_option maxHeartbeats 4000000 in
/-- Rule group G7: consuming traversal, scoped returns and the cleanup of their markers. -/
theorem schrittSek7 (hs : RufSchrittG7 P O pa M f M') (hb : RestScopeBalance (M.faeden f).kopf.rest)
    (hL : L ∈ offen (M.faeden f).spur) (hL' : L ∈ offen (M'.faeden f).spur)
    (hnd : (offen (M.faeden f).spur).Nodup)
    (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    SekArt L P pa M M' f ep c Z ZS EW := by
  unfold SekArt
  cases hs with
  | dannVerbrauch l Γ Λ Λ'' t member edge inv bound mass body rest k ρ hhead =>
    kopfS
    · simp_all
    · omega
  | verbrauchWeiter l Γ Λ t member edge inv bound mass body rest k ρ hhead
      σ₁ hs₁ hw σ₂ hs₂ v hv σ₃ hs₃ m hm neu hneu hΛ =>
    kopfS
    · simp_all
    · omega
  | verbrauchLeer l Γ Λ t member edge inv bound mass body rest k ρ hhead
      σ₁ hs₁ hw σ₂ hs₂ hleer hkein neu hneu hΛ =>
    kopfS
    · simp_all
    · omega
  | verbrauchFort l Γ Λ t member edge inv bound mass body rest vor k i ρ hhead
      σ₁ hs₁ m' hm' hfall neu hneu hΛ =>
    kopfS
    · simp_all
    · omega
  | dannLeaveVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ
      hleave hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall
      σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
    kopfS
    · simp_all
    · omega
  | dannNextVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ
      hnext hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall neum hneum hΛ =>
    kopfS
    · simp_all
    · omega
  | rueckScopedWert ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hnonempty =>
    have hbudget := r.scopedWert_budgetSek L ep c pa e R (scopeBalance_von hhead hb) hret
    dsimp only
    generalize hw : rufUpdateG M.faeden f _ f = w
    rw [rufUpdateG_self] at hw
    subst hw
    refine Or.inl ⟨rfl, fun _ => ?_⟩
    refine ⟨rfl, ?_⟩
    rw [hhead]
    change R.scopes.length + 1 ≤ potSek L ep c pa r
    unfold scopedReturnSteps at hbudget
    omega
  | rueckScopedGrund ρ r grund R hhead hret hscope hΛ hnonempty =>
    have hbudget := r.scopedGrund_budgetSek L ep c pa grund R (scopeBalance_von hhead hb) hret
    dsimp only
    generalize hw : rufUpdateG M.faeden f _ f = w
    rw [rufUpdateG_self] at hw
    subst hw
    refine Or.inl ⟨rfl, fun _ => ?_⟩
    refine ⟨rfl, ?_⟩
    rw [hhead]
    change R.scopes.length + 1 ≤ potSek L ep c pa r
    unfold scopedReturnSteps at hbudget
    omega
  | rueckFreigabe ρ a K remaining hhead hnonempty =>
    kopfS
    omega
  | rueckScopedWertDirekt ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hempty z ha =>
    have hbudget := r.scopedWert_budgetSek L ep c pa e R (scopeBalance_von hhead hb) hret
    rcases rufAntwortG_kostenSek L ha pa with ⟨hst, hroot⟩ | hpop
    · dsimp only
      generalize hw : rufUpdateG M.faeden f _ f = w
      rw [rufUpdateG_self] at hw
      subst hw
      refine Or.inl ⟨hst, fun _ => ?_⟩
      obtain ⟨hok, hzero⟩ := hroot ep c Z ZS EW
      refine ⟨hok, ?_⟩
      rw [hhead, hzero]
      simpa only [hempty, scopedReturnSteps, List.length_nil, Nat.add_zero] using hbudget
    · dsimp only
      generalize hw : rufUpdateG M.faeden f _ f = w
      rw [rufUpdateG_self] at hw
      subst hw
      exact Or.inr (Or.inr hpop)
  | rueckScopedGrundDirekt ρ r grund R hhead hret hscope hΛ hempty z ha =>
    have hbudget := r.scopedGrund_budgetSek L ep c pa grund R (scopeBalance_von hhead hb) hret
    rcases rufAntwortG_kostenSek L ha pa with ⟨hst, hroot⟩ | hpop
    · dsimp only
      generalize hw : rufUpdateG M.faeden f _ f = w
      rw [rufUpdateG_self] at hw
      subst hw
      refine Or.inl ⟨hst, fun _ => ?_⟩
      obtain ⟨hok, hzero⟩ := hroot ep c Z ZS EW
      refine ⟨hok, ?_⟩
      rw [hhead, hzero]
      simpa only [hempty, scopedReturnSteps, List.length_nil, Nat.add_zero] using hbudget
    · dsimp only
      generalize hw : rufUpdateG M.faeden f _ f = w
      rw [rufUpdateG_self] at hw
      subst hw
      exact Or.inr (Or.inr hpop)
  | rueckFreigabeLetzte ρ a K hhead z ha =>
    rcases rufAntwortG_kostenSek L ha pa with ⟨hst, hroot⟩ | hpop
    · dsimp only
      generalize hw : rufUpdateG M.faeden f _ f = w
      rw [rufUpdateG_self] at hw
      subst hw
      refine Or.inl ⟨hst, fun _ => ?_⟩
      obtain ⟨hok, hzero⟩ := hroot ep c Z ZS EW
      refine ⟨hok, ?_⟩
      rw [hhead, hzero]
      exact Nat.le_refl 1
    · dsimp only
      generalize hw : rufUpdateG M.faeden f _ f = w
      rw [rufUpdateG_self] at hw
      subst hw
      exact Or.inr (Or.inr hpop)

end Gruppen

/-- **`schrittSek`: one own step of the head, measured by the section potential of `L`**, while `L` is
    held before and after the step. The shape of `schrittArt` with `potSek L` for `potRest` and
    `rufeV L` for `rufeR`. -/
theorem schrittSek (L : D.Lock) {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D}
    {f : Faden} (hs : RufSchrittG P O pa M f M') (hb : RestScopeBalance (M.faeden f).kopf.rest)
    (hL : L ∈ offen (M.faeden f).spur) (hL' : L ∈ offen (M'.faeden f).spur)
    (hnd : (offen (M.faeden f).spur).Nodup)
    (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    SekArt L P pa M M' f ep c Z ZS EW := by
  cases hs with
  | g1 hs => exact schrittSek1 L hs hb hL hL' hnd ep c Z ZS EW
  | g2 hs => exact schrittSek2 L hs hb hL hL' hnd ep c Z ZS EW
  | g3 hs => exact schrittSek3 L hs hb hL hL' hnd ep c Z ZS EW
  | g4 hs => exact schrittSek4 L hs hb hL hL' hnd ep c Z ZS EW
  | g5 hs => exact schrittSek5 L hs hb hL hL' hnd ep c Z ZS EW
  | g6 hs => exact schrittSek6 L hs hb hL hL' hnd ep c Z ZS EW
  | g7 hs => exact schrittSek7 L hs hb hL hL' hnd ep c Z ZS EW

end Gabbro.Grammatik
