module

public import Bruecke.Kodierung
public import Bruecke.Pflichten
public import Bruecke.Ausdruck.Teil3

@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

/-- **One clause of a promise**: the Prop the duty file states (`clauseProp`) holds exactly when
    the lowered G predicate is true -- over the entry world `σ₀`, the exit world `σ'` and the
    `ensures` environment `E` (the answer first, where there is one). -/
theorem clause_iff {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {er : Option (Int × Int)}
    (hA : ArtStimmt fn) (hT : TabEindeutig u) (hN : NamenFrei fn)
    {e : UEns} {x : Gabbro.Body.Expr} {A : Acc} (hx : ensExpr u fn {} e = some (x, A))
    {g : Expr (declOf u) Γ Λ .bool} (hg : lowEns u Γ Λ fn er e = .ok g)
    (h9 : A.olds.length ≤ 9)
    (σ₀ σ' : World (declOf u)) (E : Env (declOf u) Γ) (s s' : Gabbro.Body.State)
    (hW₀ : WRel u σ₀ s.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) E s.local')
    (hW : WRel u σ' s'.world) (r : Option Gabbro.Body.Value)
    (her : er.isSome = true → r = some (nthVal E 0)) :
    clauseProp x A s s' r ↔ wahr? (eval σ₀ g σ' E) = true := by
  have hz := ensExpr_zuwachs hA hT σ₀ σ' E s hW₀ hL₀ e hx hg
  have hr : A.result = true → r = some (nthVal E 0) := fun h =>
    match hz.2 h with
    | .inl h' => absurd h' Bool.false_ne_true
    | .inr h' => her h'
  have hev : ∀ o ∈ A.olds, ∃ v, Gabbro.Body.eval s o = some v := fun o ho =>
    match hz.1 o ho with
    | .inl h => absurd h (List.not_mem_nil)
    | .inr h => h
  unfold clauseProp
  rw [clauseAux_iff x A.result s s' r A.olds 0 s.local' hev]
  have hold : ∀ i (hi : i < A.olds.length),
      Gabbro.Body.eval s A.olds[i] = some (oldsBind s A.olds 0 s.local' (oldName i)) := by
    intro i hi
    have := oldsBind_hier s A.olds 0 s.local' i hi (by omega)
    rw [Nat.zero_add] at this
    rw [this]
    obtain ⟨v, hv⟩ := hev _ (List.getElem_mem hi)
    rw [hv]; rfl
  have hpar : LRel fn (if er.isSome then 1 else 0) E (oldsBind s A.olds 0 s.local') :=
    LRel.ueber hN hL₀ (fun p _ hp => oldsBind_fremd s p A.olds 0 _ (fun i _ => by rw [Nat.zero_add]; exact hp i))
  unfold Schluss
  cases hres : A.result with
  | false =>
    have hB : EnsBind fn er E s A (oldsBind s A.olds 0 s.local') :=
      ⟨hpar, fun h => absurd (hres.symm.trans h) Bool.false_ne_true, hold⟩
    have := lowEns_sim hA hT σ₀ σ' E s s'.world _ A hW₀ hL₀ hW hB e hx hg (Vor.refl A)
    simp only [Bool.false_eq_true, ↓reduceIte, this, Option.some.injEq,
      Gabbro.Body.Value.bool.injEq]
  | true =>
    obtain hrv := hr hres
    have hB : EnsBind fn er E s A
        (Gabbro.Body.bindLocal (oldsBind s A.olds 0 s.local') "result" (nthVal E 0)) := by
      refine ⟨LRel.ueber hN hpar (fun p hp _ => Gabbro.Body.bindLocal_elsewhere _ _ _ _ hp),
        fun _ => Gabbro.Body.bindLocal_here _ _ _, fun i hi => ?_⟩
      rw [Gabbro.Body.bindLocal_elsewhere _ _ _ _ (oldName_ne_result i)]
      exact hold i hi
    have := lowEns_sim hA hT σ₀ σ' E s s'.world _ A hW₀ hL₀ hW hB e hx hg (Vor.refl A)
    simp only [↓reduceIte]
    constructor
    · rintro ⟨v, hv, h⟩
      rw [hrv] at hv; cases hv
      rw [this] at h
      simpa using h
    · intro h
      refine ⟨_, hrv, ?_⟩
      rw [this, h]

/-- The `old` reads of every clause fit the nine names the printer has (`oldName`). Checked
    per unit. -/
def OldsKurz (u : UProg) (fn : UFn) : Prop :=
  ∀ e ∈ fn.sichert, match ensExpr u fn {} e with
    | some (_, A) => A.olds.length ≤ 9
    | none => True

theorem andAll_iff : ∀ (p : Prop) (ps : List Prop), andAll p ps ↔ p ∧ ∀ q ∈ ps, q
  | p, [] => by simp [andAll]
  | p, q :: qs => by
      simp only [andAll, List.mem_cons, forall_eq_or_imp]
      rw [andAll_iff q qs]

theorem chain_iff (wf : Prop) : ∀ (ps : List Prop), chain wf ps ↔ wf ∧ ∀ q ∈ ps, q
  | [] => by simp [chain]
  | p :: ps => by
      simp only [chain, List.mem_cons, forall_eq_or_imp]
      rw [andAll_iff]

/-- **All clauses of a promise** against the lowered conjunction. -/
theorem ensList_iff {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {er : Option (Int × Int)}
    (hA : ArtStimmt fn) (hT : TabEindeutig u) (hN : NamenFrei fn)
    (σ₀ σ' : World (declOf u)) (E : Env (declOf u) Γ) (s s' : Gabbro.Body.State)
    (hW₀ : WRel u σ₀ s.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) E s.local')
    (hW : WRel u σ' s'.world) (r : Option Gabbro.Body.Value)
    (her : er.isSome = true → r = some (nthVal E 0)) :
    ∀ (es : List UEns) (cs : List Prop) (g : Expr (declOf u) Γ Λ .bool),
      (∀ e ∈ es, match ensExpr u fn {} e with
        | some (_, A) => A.olds.length ≤ 9
        | none => True) →
      ensList u fn s s' r es = some cs → lowEnsList u Γ Λ fn er es = .ok g →
      ((∀ q ∈ cs, q) ↔ wahr? (eval σ₀ g σ' E) = true)
  | [], cs, g, _, hb, h => by
      simp only [ensList, Option.some.injEq] at hb
      subst hb
      simp only [lowEnsList] at h
      cases h
      simp [Grammatik.eval, wahr?]
  | e :: es, cs, g, h9, hb, h => by
      simp only [ensList] at hb
      split at hb
      · rename_i p ps hp hps
        simp only [Option.some.injEq] at hb
        subst hb
        simp only [ensClause] at hp
        cases hx : ensExpr u fn {} e with
        | none => rw [hx] at hp; cases hp
        | some xa =>
          obtain ⟨x, A⟩ := xa
          rw [hx] at hp
          simp only [Option.map_some, Option.some.injEq] at hp
          subst hp
          have h9e := h9 e (List.mem_cons_self ..)
          rw [hx] at h9e
          simp only [lowEnsList] at h
          split at h
          · cases h
          · rename_i gx hgx
            split at h
            · cases h
            · rename_i gy hgy
              have hc := clause_iff hA hT hN hx hgx h9e σ₀ σ' E s s' hW₀ hL₀ hW r her
              have ih := ensList_iff hA hT hN σ₀ σ' E s s' hW₀ hL₀ hW r her es ps gy
                (fun e' he' => h9 e' (List.mem_cons_of_mem _ he')) hps hgy
              simp only [List.mem_cons, forall_eq_or_imp]
              rw [hc, ih]
              split at h
              · cases h
                simp [Grammatik.eval, wahr?]
              · cases h
                simp only [Grammatik.eval, wahr?]
                exact Iff.of_eq (Bool.and_eq_true _ _).symm
      · cases hb

end Gabbro.Bruecke
