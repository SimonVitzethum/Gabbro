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

/-! ## 5. One `ensures` clause, as the duty file states it -/

theorem oldName_inj : ∀ a < 9, ∀ b < 9, oldName a = oldName b → a = b := by decide

theorem oldName_ne_result : ∀ a, oldName a ≠ "result" := by
  intro a
  match a with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => decide
  | _ + 8 => simp [oldName]

/-- The binding `clauseAux` builds: the `n`th, `n+1`st, … `old` name bound to the value its read
    has in the entry state. -/
def oldsBind (s : Gabbro.Body.State) : List Gabbro.Body.Expr → Nat → Gabbro.Body.Binding →
    Gabbro.Body.Binding
  | [], _, β => β
  | o :: os, n, β =>
      oldsBind s os (n + 1) (Gabbro.Body.bindLocal β (oldName n) ((Gabbro.Body.eval s o).getD .absent))

/-- The end of a clause: evaluated in the exit world under the built binding (with `result`
    bound to the answer, where the clause names it). -/
def Schluss (t : Gabbro.Body.Expr) (uses : Bool) (s' : Gabbro.Body.State)
    (r : Option Gabbro.Body.Value) (β : Gabbro.Body.Binding) : Prop :=
  if uses then ∃ v, r = some v ∧
      Gabbro.Body.eval ⟨s'.world, Gabbro.Body.bindLocal β "result" v⟩ t = some (.bool true)
  else Gabbro.Body.eval ⟨s'.world, β⟩ t = some (.bool true)

/-- Where every `old` read evaluates, the universally bound `old` values of `clauseAux` ARE those
    values. -/
theorem clauseAux_iff (t : Gabbro.Body.Expr) (uses : Bool) (s s' : Gabbro.Body.State)
    (r : Option Gabbro.Body.Value) :
    ∀ (olds : List Gabbro.Body.Expr) (n : Nat) (β : Gabbro.Body.Binding),
      (∀ o ∈ olds, ∃ v, Gabbro.Body.eval s o = some v) →
      (clauseAux t uses s s' r olds n β ↔ Schluss t uses s' r (oldsBind s olds n β))
  | [], n, β, _ => by
      unfold clauseAux Schluss oldsBind
      cases uses <;> simp
  | o :: os, n, β, hev => by
      obtain ⟨v, hv⟩ := hev o (List.mem_cons_self ..)
      have ih := clauseAux_iff t uses s s' r os (n + 1)
        (Gabbro.Body.bindLocal β (oldName n) v) (fun o' h => hev o' (List.mem_cons_of_mem _ h))
      simp only [clauseAux, oldsBind, hv, Option.getD_some]
      constructor
      · intro h; exact ih.mp (h v rfl)
      · intro h ov hov; cases hov; exact ih.mpr h

theorem oldsBind_fremd (s : Gabbro.Body.State) (m : String) :
    ∀ (olds : List Gabbro.Body.Expr) (n : Nat) (β : Gabbro.Body.Binding),
      (∀ i, i < olds.length → m ≠ oldName (n + i)) → oldsBind s olds n β m = β m
  | [], _, _, _ => rfl
  | o :: os, n, β, h => by
      simp only [oldsBind]
      rw [oldsBind_fremd s m os (n + 1) _ (fun i hi => by
        have := h (i + 1) (by simp; omega)
        rwa [show n + (i + 1) = n + 1 + i by omega] at this)]
      exact Gabbro.Body.bindLocal_elsewhere _ _ _ _ (by simpa using h 0 (by simp))

theorem oldsBind_hier (s : Gabbro.Body.State) :
    ∀ (olds : List Gabbro.Body.Expr) (n : Nat) (β : Gabbro.Body.Binding) (i : Nat)
      (hi : i < olds.length), n + olds.length ≤ 9 →
      oldsBind s olds n β (oldName (n + i)) = (Gabbro.Body.eval s olds[i]).getD .absent
  | [], _, _, _, hi, _ => by simp at hi
  | o :: os, n, β, 0, _, hn => by
      simp only [oldsBind, Nat.add_zero]
      rw [oldsBind_fremd s _ os (n + 1) _ (fun i hi h => by
        have := oldName_inj n (by simp at hn; omega) (n + 1 + i) (by simp at hn; omega) h
        omega)]
      simp
  | o :: os, n, β, i + 1, hi, hn => by
      simp only [oldsBind]
      rw [show n + (i + 1) = n + 1 + i by omega]
      exact oldsBind_hier s os (n + 1) _ i (by simpa using hi) (by simp at hn; omega)
      
/-- No parameter is called `result` or `old#…` -- the names a clause binds on top of the entry
    binding. Checked per unit. -/
def NamenFrei (fn : UFn) : Prop :=
  ∀ q ∈ fn.params, q.1 ≠ "result" ∧ ∀ i, q.1 ≠ oldName i

theorem LRel.ueber {D : Deklaration} {Γ : Ctx} {fn : UFn} {sh : Nat} {ρ : Env D Γ}
    {β β' : Gabbro.Body.Binding} (hN : NamenFrei fn) (h : LRel fn sh ρ β)
    (hβ : ∀ p, p ≠ "result" → (∀ i, p ≠ oldName i) → β' p = β p) : LRel fn sh ρ β' := by
  intro p j hj
  obtain ⟨τ, hτ⟩ := paramPos_name _ _ _ hj
  have hm : (p, τ) ∈ fn.params := List.mem_of_getElem? hτ
  obtain ⟨h1, h2⟩ := hN _ hm
  rw [hβ p h1 h2]
  exact h p j hj

/-- **One clause of a promise**: the Prop the duty file states (`clauseProp`) holds exactly when
    the lowered G predicate is true -- over the entry world `σ₀`, the exit world `σ'` and the
    `ensures` environment `E` (the answer first, where there is one). -/
theorem clause_iff {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {er : Option Ty}
    (hA : ArtStimmt fn) (hT : TabEindeutig u) (hN : NamenFrei fn)
    {e : UEns} {x : Gabbro.Body.Expr} {A : Acc} (hx : ensExpr u fn {} e = some (x, A))
    {g : Expr (declOf u) Γ Λ .bool} (hg : lowEns u Γ Λ fn er e = .ok g)
    (h9 : A.olds.length ≤ 9)
    (σ₀ σ' : World (declOf u)) (E : Env (declOf u) Γ) (s s' : Gabbro.Body.State)
    (hW₀ : WGRel u σ₀ s.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) E s.local')
    (hW : WGRel u σ' s'.world) (r : Option Gabbro.Body.Value)
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
  ∀ e ∈ fn.gives, match ensExpr u fn {} e with
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
theorem ensList_iff {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {er : Option Ty}
    (hA : ArtStimmt fn) (hT : TabEindeutig u) (hN : NamenFrei fn)
    (σ₀ σ' : World (declOf u)) (E : Env (declOf u) Γ) (s s' : Gabbro.Body.State)
    (hW₀ : WGRel u σ₀ s.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) E s.local')
    (hW : WGRel u σ' s'.world) (r : Option Gabbro.Body.Value)
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

/-- A runtime bool expression has no entry snapshots or result binder. -/
theorem lowEns_raw_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {v : UEns} {ev : Expr (declOf u) Γ Λ .bool} {e : Gabbro.Body.Expr}
    (h : lowEns u Γ Λ fn none v = .ok ev) (hb : rawCond u fn v = some e)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    Gabbro.Body.eval s e = some (valOf .bool (eval σ₀ ev σ ρ)) := by
  unfold rawCond at hb
  split at hb
  · rename_i raw a hens
    split at hb
    · rename_i hc
      cases hb
      let s0 : Gabbro.Body.State := ⟨encG u σ₀ s.world, s.local'⟩
      have hB : EnsBind fn none ρ s0 a s.local' :=
        ⟨hL, fun hr => (by rw [hc.2] at hr; cases hr),
          fun i hi => (by rw [hc.1] at hi; exact absurd hi (Nat.not_lt_zero _))⟩
      exact lowEns_sim (er := none) hA hT σ₀ σ ρ s0 s.world s.local' a
        (wgrel_enc u σ₀ s.world) hL hW hB v hens h (Vor.refl a)
    · cases hb
  · cases hb

end Gabbro.Bruecke
