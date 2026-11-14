/-
  File:      Grammatik/Logik/Fortschritt/Halten/SchrittSek1.lean
  Subject:   ONE OWN STEP OF A SECTION'S FRAME, rule groups G1-G3: the potential argument of `schrittArt`
             (KostenG/T2/Teil1a.lean) for the section potential `potSek L` and the cut admission `rufeV L`
             (Halten/PotSek.lean). The proof is `schrittArt`'s, rule by rule; the only rules that touch a
             release marker are `dannLocks` (it pushes one for a lock `L' ≠ L`, since `L` is held and
             `L'` is not) and `freiGib` (it pops one; for `L` itself that releases `L`, excluded by the
             premise that `L` is still held after the step).
-/
module
public import Grammatik.Logik.Fortschritt.Halten.PotSek
public import Grammatik.Logik.Fortschritt.KostenG.T2
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **What one own step does to a section's frame** (the shape of `schrittArt`): (A) the head moves,
    the stack stays, `potSek L` drops by one; (B) a push, the caller drops by one plus the callee's
    cost; (C) a pop, the caller resumes with at most its section potential. -/
abbrev SekArt (L : D.Lock) (P : Programm D) (pa : Nat) (M M' : RufMaschineG D) (f : Faden)
    (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) : Prop :=
  ((M'.faeden f).stapel = (M.faeden f).stapel ∧
      (rufeV L Z ZS EW (M.faeden f).kopf.rest.2.2.2.2 = true →
        rufeV L Z ZS EW (M'.faeden f).kopf.rest.2.2.2.2 = true ∧
        potSek L ep c pa (M'.faeden f).kopf.rest.2.2.2.2 + 1 ≤
          potSek L ep c pa (M.faeden f).kopf.rest.2.2.2.2)) ∨
    (∃ (g : D.Fn) (caller' : RufRahmenG D) (rho : Env D (D.params g)) (s0 : World D),
      (M'.faeden f).stapel = caller' :: (M.faeden f).stapel ∧
      (M'.faeden f).kopf = ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
        rho, .ende (P.rumpf g)⟩⟩ ∧
      (rufeV L Z ZS EW (M.faeden f).kopf.rest.2.2.2.2 = true →
        rufeV L Z ZS EW caller'.rest.2.2.2.2 = true ∧
        ((Z g = true ∧ potSek L ep c pa caller'.rest.2.2.2.2 + 1 + c g ≤
            potSek L ep c pa (M.faeden f).kopf.rest.2.2.2.2) ∨
          (∃ n, ZS n = true ∧ D.passt g n = true ∧
            potSek L ep c pa caller'.rest.2.2.2.2 + 1 ≤ potSek L ep c pa (M.faeden f).kopf.rest.2.2.2.2)))) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst ∧ (M'.faeden f).stapel = rst ∧
      ∀ (ep : Nat) (c' : D.Fn → Nat) (Z' : D.Fn → Bool) (ZS' : Nat → Bool) (EW' : Bool),
        (rufeV L Z' ZS' EW' caller.rest.2.2.2.2 = true →
          rufeV L Z' ZS' EW' (M'.faeden f).kopf.rest.2.2.2.2 = true) ∧
        potSek L ep c' pa (M'.faeden f).kopf.rest.2.2.2.2 ≤ potSek L ep c' pa caller.rest.2.2.2.2)

set_option hygiene false in
/-- Case (A) of `SekArt`: rewrite the new head and the old head into their residues and unfold. -/
macro "kopfS" : tactic => `(tactic| (
  refine Or.inl ⟨by dsimp only; rw [rufUpdateG_self], fun hok => ⟨?_, ?_⟩⟩ <;> dsimp only <;>
  rw [rufUpdateG_self] <;>
  rw [‹(M.faeden f).kopf.rest = _›] at hok <;> (try rw [‹(M.faeden f).kopf.rest = _›]) <;>
  dsimp only at hok ⊢ <;>
  simp only [GRest.weiterOpt, potSek, kostenEnd, kostenBlock, kostenStmt, rufeV, rufeE, rufeB, rufeS,
    kostenBlock_alsBlock, rufeB_alsBlock,
    Bool.and_eq_true, List.length_cons, Nat.add_mul, Nat.one_mul] at hok ⊢))

set_option hygiene false in
/-- `kopfS` at a release marker of a lock `L' ≠ L` (`hne : ¬ L' = L`): the marker is not the section's. -/
macro "kopfSn" : tactic => `(tactic| (
  refine Or.inl ⟨by dsimp only; rw [rufUpdateG_self], fun hok => ⟨?_, ?_⟩⟩ <;> dsimp only <;>
  rw [rufUpdateG_self] <;>
  rw [‹(M.faeden f).kopf.rest = _›] at hok <;> (try rw [‹(M.faeden f).kopf.rest = _›]) <;>
  dsimp only at hok ⊢ <;>
  simp only [GRest.weiterOpt, potSek, kostenEnd, kostenBlock, kostenStmt, rufeV, rufeE, rufeB, rufeS,
    kostenBlock_alsBlock, rufeB_alsBlock, hne, ↓reduceIte, ite_false, if_false,
    Bool.and_eq_true, List.length_cons, Nat.add_mul, Nat.one_mul] at hok ⊢))

section Gruppen

variable (L : D.Lock) {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D} {f : Faden}

set_option linter.unusedVariables false

set_option maxHeartbeats 4000000 in
/-- Rule group G1. -/
theorem schrittSek1 (hs : RufSchrittG1 P O pa M f M') (hb : RestScopeBalance (M.faeden f).kopf.rest)
    (hL : L ∈ offen (M.faeden f).spur) (hL' : L ∈ offen (M'.faeden f).spur)
    (hnd : (offen (M.faeden f).spur).Nodup)
    (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    SekArt L P pa M M' f ep c Z ZS EW := by
  unfold SekArt
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead =>
    kopfS
    · simp_all
    · have := kostenStmt_pos ep c pa s; omega
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead =>
    kopfS
    · simp_all
    · have := kostenStmt_pos ep c pa s; omega
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
    kopfS
    · simp_all
    · rw [entfZ_wahr hent]; omega
  | endeForm l Γ Λ e ρ hl hent hhead =>
    kopfS
    · cases e <;> try (simp only [EndEntfaltbar, Bool.false_eq_true] at hent; done)
      all_goals simp_all [rufeB_alsBlock, rufeV]
    · cases e <;> try (simp only [EndEntfaltbar, Bool.false_eq_true] at hent; done)
      all_goals (simp only [potSek, kostenBlock_alsBlock, kostenEnd, kostenSonst]; omega)
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw =>
    kopfS
    · have h := rufeB_armWahlG Z ZS EW arms (eval σ₁ v σ₁ ρ) hok.1.1
      rw [hw] at h
      have h2 : rufeB Z ZS EW b = true := h
      simp_all
    · have h := kostenBlock_armWahlG ep c pa arms (eval σ₁ v σ₁ ρ)
      rw [hw] at h
      have h2 : kostenBlock ep c pa b ≤ kostenArms ep c pa arms := h
      omega
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw =>
    kopfS
    · have h := rufeB_armWahlG Z ZS EW arms (eval σ₁ v σ₁ ρ) hok.1.1
      rw [hw] at h
      have h2 : rufeB Z ZS EW b = true := h
      simp_all
    · have h := kostenBlock_armWahlG ep c pa arms (eval σ₁ v σ₁ ρ)
      rw [hw] at h
      have h2 : kostenBlock ep c pa b ≤ kostenArms ep c pa arms := h
      omega
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw =>
    kopfS
    · have h := rufeB_grundWahlG Z ZS EW arms (eval σ₁ r σ₁ ρ) hok.1.1
      rw [hw] at h
      simp_all
    · have h := kostenBlock_grundWahlG ep c pa arms (eval σ₁ r σ₁ ρ)
      rw [hw] at h
      omega
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potSek, kostenEnd, kostenStmt, rufeV, rufeE, rufeS, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.2, Or.inl ⟨hok.1, by omega⟩⟩
  | rueck caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun ep c' Z' ZS' EW' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact ⟨id, Nat.le_refl _⟩
  | _ =>
    kopfS
    · cases EW <;> simp_all
    · omega

set_option maxHeartbeats 4000000 in
/-- Rule group G2: `dannLocks` takes a lock other than `L`, `freiGib` of `L` itself releases `L`. -/
theorem schrittSek2 (hs : RufSchrittG2 P O pa M f M') (hb : RestScopeBalance (M.faeden f).kopf.rest)
    (hL : L ∈ offen (M.faeden f).spur) (hL' : L ∈ offen (M'.faeden f).spur)
    (hnd : (offen (M.faeden f).spur).Nodup)
    (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    SekArt L P pa M M' f ep c Z ZS EW := by
  unfold SekArt
  cases hs with
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
    kopfS
    · simp_all
    · have h : @List.length (Wert D (.index (D.count t))) (alleIndizes (D.count t)) *
          (kostenBlock ep c pa body + kostenExpr inv + 2) ≤
          (D.count t).toNat * (kostenBlock ep c pa body + kostenExpr inv + 2) :=
        Nat.mul_le_mul_right _ (alleIndizes_length_toNat (D.count t))
      omega
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potSek, kostenBlock, kostenStmt, rufeV, rufeB, rufeS,
        Bool.and_eq_true] at hok ⊢
      exact ⟨⟨hok.1.2, hok.2⟩, Or.inl ⟨hok.1.1, by omega⟩⟩
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
    kopfS
    · simp_all
    · have := kostenBlock_pos ep c pa ueber
      have hm : max 1 (kostenBlock ep c pa ueber) = kostenBlock ep c pa ueber := Nat.max_eq_right this
      omega
  | dannLocks l Γ Λ Λ'' L' hr body rest k ρ hhead hself hrang hfrei =>
    have hne : ¬ L' = L := fun e => hself (by rw [e]; exact hL)
    kopfSn
    · simp_all
    · omega
  | freiGib l Γ Λ L' k ρ hhead =>
    by_cases hne : L' = L
    · exfalso
      simp only [rufUpdateG_self, offen] at hL'
      rw [hne] at hL'
      exact hnd.not_mem_erase hL'
    · kopfSn
      · simp_all
      · omega
  | _ =>
    kopfS
    · cases EW <;> simp_all
    · omega

set_option maxHeartbeats 4000000 in
/-- Rule group G3: the call rules and `rueckBind`, unchanged from `schrittArt`. -/
theorem schrittSek3 (hs : RufSchrittG3 P O pa M f M') (hb : RestScopeBalance (M.faeden f).kopf.rest)
    (hL : L ∈ offen (M.faeden f).spur) (hL' : L ∈ offen (M'.faeden f).spur)
    (hnd : (offen (M.faeden f).spur).Nodup)
    (ep : Nat) (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    SekArt L P pa M M' f ep c Z ZS EW := by
  unfold SekArt
  cases hs with
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potSek, kostenBlock, rufeV, rufeB, Bool.and_eq_true] at hok ⊢
      exact ⟨⟨hok.1.2, hok.2⟩, Or.inl ⟨hok.1.1, by omega⟩⟩
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potSek, kostenBlock, rufeV, rufeB, Bool.and_eq_true] at hok ⊢
      exact ⟨⟨⟨hok.1.1.2, hok.1.2⟩, hok.2⟩, Or.inl ⟨hok.1.1.1, by omega⟩⟩
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potSek, kostenBlock, kostenStmt, rufeV, rufeB, rufeS, Bool.and_eq_true] at hok ⊢
      exact ⟨⟨hok.1.2, hok.2⟩, Or.inr ⟨n, hok.1.1, hg, by omega⟩⟩
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potSek, kostenEnd, kostenStmt, rufeV, rufeE, rufeS, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.2, Or.inr ⟨n, hok.1, hg, by omega⟩⟩
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potSek, kostenBlock, rufeV, rufeB, Bool.and_eq_true] at hok ⊢
      exact ⟨⟨hok.1.2, hok.2⟩, Or.inr ⟨n, hok.1.1, hg, by omega⟩⟩
  | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potSek, kostenBlock, rufeV, rufeB, Bool.and_eq_true] at hok ⊢
      exact ⟨⟨⟨hok.1.1.2, hok.1.2⟩, hok.2⟩, Or.inr ⟨n, hok.1.1.1, hg, by omega⟩⟩
  | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (τ := τ) (D.sigNr n).gruende err .nil
        (.dann rest k)⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potSek, kostenBlock, kostenStmt, rufeV, rufeB, rufeS, Bool.and_eq_true] at hok ⊢
      exact ⟨⟨⟨hok.1.1.2, by trivial⟩, hok.1.2, hok.2⟩, Or.inr ⟨n, hok.1.1.1, hg, by omega⟩⟩
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun ep c' Z' ZS' EW' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [potSek, rufeV, Bool.and_eq_true] <;> exact ⟨fun h => by simp_all, by omega⟩
  | _ =>
    kopfS
    · cases EW <;> simp_all
    · omega

end Gruppen

end Gabbro.Grammatik
