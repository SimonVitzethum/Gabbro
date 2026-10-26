/-
  File:      stage0/Stage0/Schritt/Dann.lean
  Subject:   The executable step, part 2: a head residue `.dann b k` whose block `b` is not a call and not a leaf
             (`dannLeer`, `dannBind`, `dannNarrowOk`/`Else`, `dannPruefWahr`/`Falsch`, and the unfolds of the
             compound statements `ite`, `onOption`, `breaking`).

  Each case returns the successor exactly as its rule of `RufSchrittG` states it, with the rule as the proof.
-/
import Stage0.Schritt.Grund

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} (P : Programm D) (O : Orakel D) (passes : Nat)

/-- No other thread holds `L`: checked on the running threads `aktiv`; a thread outside it holds nothing. -/
def freiB (M : RufMaschineG D) (f : Faden) (aktiv : List Faden) (L : D.Lock) : Bool :=
  aktiv.all fun g => g == f || !decide (L ∈ offen (M.faeden g).spur)

theorem frei_of {M : RufMaschineG D} {f : Faden} {aktiv : List Faden} {L : D.Lock}
    (hruhe : ∀ g, g ∉ aktiv → offen (M.faeden g).spur = []) (h : freiB M f aktiv L = true) : RufFreiG M f L := by
  intro g hg hL
  by_cases ha : g ∈ aktiv
  · simp only [freiB, List.all_eq_true] at h
    have := h g ha
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at this
    rcases this with e | e
    · exact hg e
    · exact e hL
  · rw [hruhe g ha] at hL; simp at hL

/-- The unfold of a compound statement at the head of a `dann` block. -/
def zugDannCons (M : RufMaschineG D) (f : Faden) (aktiv : List Faden)
    (hruhe : ∀ g, g ∉ aktiv → offen (M.faeden g).spur = []) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    (ρ : Env D Γ) (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ'')
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons s rest) k⟩) : Option (Zug P O passes M f) :=
  match s, hk with
  | .ite c t e, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      let σ₁ := (M.weltVon f).lese Λ c.orte
      if hw : wahr? (eval σ₁ c σ₁ ρ) = true then
        some ⟨_, .dannIteWahr M f l Γ Λ Λ' Λ'' c t e rest k ρ hk σ₁ rfl hw _ (lese_neu M f Λ c.orte)
          (heldIn_of hΛ), [], rfl⟩
      else
        some ⟨_, .dannIteFalsch M f l Γ Λ Λ' Λ'' c t e rest k ρ hk σ₁ rfl (by simpa using hw) _
          (lese_neu M f Λ c.orte) (heldIn_of hΛ), [], rfl⟩
    else none
  | .onOption (n := n) o p a, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      let σ₁ := (M.weltVon f).lese Λ o.orte
      match hv : eval σ₁ o σ₁ ρ with
      | Option.some v =>
        some ⟨_, .dannOnOptionSome M f l Γ Λ Λ' Λ'' n o p a rest k ρ hk σ₁ rfl v hv _
          (lese_neu M f Λ o.orte) (heldIn_of hΛ), [], rfl⟩
      | Option.none =>
        some ⟨_, .dannOnOptionNone M f l Γ Λ Λ' Λ'' n o p a rest k ρ hk σ₁ rfl hv _
          (lese_neu M f Λ o.orte) (heldIn_of hΛ), [], rfl⟩
    else none
  | .breaking i body, hk => some ⟨_, .dannBreaking M f l Γ Λ Λ' Λ'' i body rest k ρ hk, [], rfl⟩
  | .onTag (cs := cs) v arms, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      let σ₁ := (M.weltVon f).lese Λ v.orte
      match hw : armWahlG arms (eval σ₁ v σ₁ ρ) with
      | ⟨some (lo, hi), b, nutz⟩ =>
        some ⟨_, .dannOnTagSome M f l Γ Λ Λ' Λ'' cs v arms rest k ρ hk σ₁ rfl lo hi b nutz hw _
          (lese_neu M f Λ v.orte) (heldIn_of hΛ), [], rfl⟩
      | ⟨none, b, nutz⟩ =>
        some ⟨_, .dannOnTagNone M f l Γ Λ Λ' Λ'' cs v arms rest k ρ hk σ₁ rfl b nutz hw _
          (lese_neu M f Λ v.orte) (heldIn_of hΛ), [], rfl⟩
    else none
  | .onWhy (n := n) r arms, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      let σ₁ := (M.weltVon f).lese Λ r.orte
      some ⟨_, .dannOnGrund M f l Γ Λ Λ' Λ'' n r arms rest k ρ hk σ₁ rfl _ rfl _ (lese_neu M f Λ r.orte)
        (heldIn_of hΛ), [], rfl⟩
    else none
  | .locks L hr body, hk =>
    if hself : L ∉ offen (M.faeden f).spur then
      if hrang : ∀ K ∈ offen (M.faeden f).spur, D.rang K < D.rang L then
        if hf : freiB M f aktiv L = true then
          some ⟨_, .dannLocks M f l Γ Λ Λ'' L hr body rest k ρ hk hself hrang (frei_of hruhe hf), [], rfl⟩
        else none
      else none
    else none
  | .traverse t inv body, hk => some ⟨_, .dannTrav M f l Γ Λ Λ'' t inv body rest k ρ hk, [], rfl⟩
  | .retry n bis body ueber, hk => some ⟨_, .dannRetry M f l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hk, [], rfl⟩
  | .forever a inv body, hk => some ⟨_, .dannForever M f l Γ Λ Λ' Λ'' a inv body rest k ρ hk, [], rfl⟩
  | _, _ => none

/-- **A head residue `.dann b k`.** -/
def zugDann (M : RufMaschineG D) (f : Faden) (aktiv : List Faden)
    (hruhe : ∀ g, g ∉ aktiv → offen (M.faeden g).spur = []) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (ρ : Env D Γ)
    (b : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ')
    (hk : (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann b k⟩) : Option (Zug P O passes M f) :=
  match b, hk with
  | .nil, hk => some ⟨_, .dannLeer M f l Γ Λ k ρ hk, [], rfl⟩
  | .bind e rest, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      some ⟨_, .dannBind M f l Γ Λ Λ' Λ' _ e rest k ρ hk _ rfl _ (lese_neu M f Λ e.orte) (heldIn_of hΛ), [], rfl⟩
    else none
  | .narrow (lo := lo) (hi := hi) e lo' hi' sonst rest, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      let σ₁ := (M.weltVon f).lese Λ e.orte
      if h : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi' then
        some ⟨_, .dannNarrowOk M f l Γ Λ Λ' Λ' lo hi lo' hi' e sonst rest k ρ hk σ₁ rfl h _
          (lese_neu M f Λ e.orte) (heldIn_of hΛ), [], rfl⟩
      else
        some ⟨_, .dannNarrowElse M f l Γ Λ Λ' Λ' lo hi lo' hi' e sonst rest k ρ hk σ₁ rfl h _
          (lese_neu M f Λ e.orte) (heldIn_of hΛ), [], rfl⟩
    else none
  | .check c sonst rest, hk =>
    if hΛ : heldInB Λ (offen (M.faeden f).spur) = true then
      let σ₁ := (M.weltVon f).lese Λ c.orte
      if hw : wahr? (eval σ₁ c σ₁ ρ) = true then
        some ⟨_, .dannPruefWahr M f l Γ Λ Λ' Λ' c sonst rest k ρ hk σ₁ rfl hw _ (lese_neu M f Λ c.orte)
          (heldIn_of hΛ), [], rfl⟩
      else
        some ⟨_, .dannPruefFalsch M f l Γ Λ Λ' Λ' c sonst rest k ρ hk σ₁ rfl (by simpa using hw) _
          (lese_neu M f Λ c.orte) (heldIn_of hΛ), [], rfl⟩
    else none
  | .cons s rest, hk => zugDannCons P O passes M f aktiv hruhe ρ s rest k hk
  | _, _ => none

end Gabbro.Stage0
