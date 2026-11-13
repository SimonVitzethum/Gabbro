module
public import Bruecke.Anweisung.Lokal.Uebersetzung
@[expose] public section

/-!
# C3: the scope of a body with binders -- freshness, the scope invariant, the binding relation

A binder must be fresh where it stands (`BindFrisch`): no name of the scope (no parameter, no
earlier binder), not `result`, not an `old#i`, not the hidden result binder `#erg`. Then the
scope the lowering threads (`fn.mitBindung x ..`) keeps the three name conditions the bridge
rests on (`NamenEindeutig`, `NamenFrei`, `ArtStimmt`), and the binding relation `LRel` moves
along a `let` (`lrel_mitBindung`) and along an assignment (`lrel_set`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. Freshness -/

/-- The name a statement binds in the bridge's fragment. -/
def binderOf : UStmt → Option String
  | .bind x _ _ => some x
  | .bindMut x _ _ _ => some x
  | _ => none

/-- `x` may be bound in a scope with the names `ns`. -/
def NameFrisch (ns : List String) (x : String) : Prop :=
  x ∉ ns ∧ x ≠ "result" ∧ x ≠ "#erg" ∧ ∀ i, x ≠ oldName i

/-- Every binder of the statements is fresh at its point (the names grow by each binder). -/
def BindFrischL : List String → List UStmt → Prop
  | _, [] => True
  | ns, s :: ss =>
      match binderOf s with
      | some x => NameFrisch ns x ∧ BindFrischL (x :: ns) ss
      | none => BindFrischL ns ss

/-- **Freshness instead of shadowing** -- every binder of the body of `fn` is fresh. -/
def BindFrisch (fn : UFn) : Prop := BindFrischL (fn.params.map (·.1)) fn.body

theorem bindFrischL_bind {ns : List String} {x : String} {d : Option (Int × Int)} {v : USide}
    {ss : List UStmt} (h : BindFrischL ns (.bind x d v :: ss)) :
    NameFrisch ns x ∧ BindFrischL (x :: ns) ss := by
  first
    | exact h
    | simpa only [BindFrischL, binderOf] using h

theorem bindFrischL_bindMut {ns : List String} {x : String} {lo hi : Int} {v : USide}
    {ss : List UStmt} (h : BindFrischL ns (.bindMut x lo hi v :: ss)) :
    NameFrisch ns x ∧ BindFrischL (x :: ns) ss := by
  first
    | exact h
    | simpa only [BindFrischL, binderOf] using h

theorem bindFrischL_sonst {ns : List String} {s : UStmt} {ss : List UStmt}
    (hs : binderOf s = none) (h : BindFrischL ns (s :: ss)) : BindFrischL ns ss := by
  simp only [BindFrischL, hs] at h
  exact h

theorem mitBindung_namen (fn : UFn) (x : String) (w : Int × Int) :
    (fn.mitBindung x w).params.map (·.1) = x :: fn.params.map (·.1) := rfl

theorem mitBindung_ctx (fn : UFn) (x : String) (w : Int × Int) :
    (fn.mitBindung x w).params.map (·.2) = .int w.1 w.2 :: fn.params.map (·.2) := rfl

/-! ## 2. The three name conditions survive a fresh binder -/

theorem namenEindeutig_mitBindung {fn : UFn} {x : String} (w : Int × Int)
    (h : NamenEindeutig fn) (hx : x ∉ fn.params.map (·.1)) :
    NamenEindeutig (fn.mitBindung x w) := by
  show ((fn.mitBindung x w).params.map (·.1)).Nodup
  rw [mitBindung_namen]
  exact List.nodup_cons.mpr ⟨hx, h⟩

theorem namenFrei_mitBindung {fn : UFn} {x : String} (w : Int × Int)
    (h : NamenFrei fn) (h1 : x ≠ "result") (h2 : ∀ i, x ≠ oldName i) :
    NamenFrei (fn.mitBindung x w) := by
  intro q hq
  simp only [UFn.mitBindung, List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact ⟨h1, h2⟩
  · exact h q hq

theorem artStimmt_mitBindung {fn : UFn} {x : String} (w : Int × Int)
    (h : ArtStimmt fn) (hx : x ≠ "#erg") : ArtStimmt (fn.mitBindung x w) := by
  refine ⟨fun j num wb hk => ?_, fun k hk => ?_, fun q hq => ?_⟩
  · cases j with
    | zero => simp [UFn.mitBindung] at hk
    | succ j =>
      have hk' : fn.kinds[j]? = some (.ptr (.table num (true, wb))) := by
        simpa [UFn.mitBindung] using hk
      obtain ⟨w', hw'⟩ := h.1 j num wb hk'
      exact ⟨w', by simpa [UFn.mitBindung] using hw'⟩
  · simp only [UFn.mitBindung, List.mem_cons] at hk
    rcases hk with rfl | hk
    · rfl
    · exact h.2.1 k hk
  · simp only [UFn.mitBindung, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp [ParamSchlicht, TySchlicht, hx]
    · exact h.2.2 q hq

/-! ## 3. The scope invariant -/

/-- What the run keeps of a scope: the context is the scope's types, and the scope satisfies the
    name conditions of the statement simulations. -/
structure UmfangB (Γ : Ctx) (fn : UFn) : Prop where
  ctx : Γ = fn.params.map (·.2)
  art : ArtStimmt fn
  namen : NamenEindeutig fn

theorem UmfangB.start (c : Fin u.fns.length) (hA : ArtStimmt (fnAt u c))
    (hN : NamenEindeutig (fnAt u c)) : UmfangB (ctxOf u c) (fnAt u c) :=
  ⟨rfl, hA, hN⟩

/-- **A fresh `let` keeps the invariant**, at every range. -/
theorem UmfangB.bind {Γ : Ctx} {fn : UFn} (h : UmfangB Γ fn) {x : String}
    (hx : NameFrisch (fn.params.map (·.1)) x) (w : Int × Int) :
    UmfangB (.int w.1 w.2 :: Γ) (fn.mitBindung x w) :=
  ⟨by rw [h.ctx, mitBindung_ctx], artStimmt_mitBindung w h.art hx.2.2.1,
    namenEindeutig_mitBindung w h.namen hx.1⟩

/-! ## 4. The binding relation along a `let` and along an assignment -/

/-- **After a `let`**: the new name reads the new first entry, every other name its old entry one
    place further. -/
theorem lrel_mitBindung {D : Deklaration} {Γ : Ctx} {fn : UFn} {ρ : Env D Γ}
    {β : Gabbro.Body.Binding} (hL : LRel fn 0 ρ β) (x : String) (w : Int × Int) {τ : Ty}
    (v : Wert D τ) (bv : Gabbro.Body.Value) (hv : bv = valOf τ v) :
    LRel (fn.mitBindung x w) 0 (Env.cons v ρ) (Gabbro.Body.bindLocal β x bv) := by
  intro p j hj
  simp only [UFn.mitBindung] at hj
  unfold paramPos at hj
  split at hj
  · rename_i hq
    simp only [Except.ok.injEq] at hj
    subst hj
    have : x = p := by simpa using hq
    subst this
    rw [Gabbro.Body.bindLocal_here, hv]
    rfl
  · rename_i hq
    split at hj
    · cases hj
    · rename_i k hk
      simp only [Except.ok.injEq] at hj
      subst hj
      have hpx : p ≠ x := fun e => hq (by simp [e])
      rw [Gabbro.Body.bindLocal_elsewhere _ _ _ _ hpx, hL p k hk]
      simp

/-- Writing the variable the lowering resolves at position `j` changes the `j`th entry only. -/
theorem nthVal_set {D : Deklaration} : ∀ (Γ : Ctx) (j : Nat) (τ : Ty) (x : Var Γ τ)
    (ρ : Env D Γ) (v : Wert D τ) (k : Nat), lowVar Γ j τ = .ok x →
    nthVal (ρ.set x v) k = if k = j then valOf τ v else nthVal ρ k
  | [], _, _, _, _, _, _, h => by simp [lowVar] at h
  | σ :: Γ, 0, τ, x, ρ, v, k, h => by
      unfold lowVar at h
      split at h
      · rename_i hστ
        subst hστ
        have h' : (Except.ok Var.here : Except String (Var (σ :: Γ) σ)) = .ok x := h
        simp only [Except.ok.injEq] at h'
        subst h'
        cases ρ with
        | cons w ρ' =>
          show nthVal (Env.cons v ρ') k = _
          cases k with
          | zero => simp
          | succ k => simp
      · simp at h
  | σ :: Γ, j + 1, τ, x, ρ, v, k, h => by
      unfold lowVar at h
      split at h
      · simp at h
      · rename_i y hy
        simp only [Except.ok.injEq] at h
        subst h
        cases ρ with
        | cons w ρ' =>
          show nthVal (Env.cons w (ρ'.set y v)) k = _
          cases k with
          | zero => simp
          | succ k => simp [nthVal_set Γ j τ y ρ' v k hy]

/-- **After an assignment** to the name at position `j`: that name reads the new value, every
    other name its old entry. -/
theorem lrel_set {D : Deklaration} {Γ : Ctx} {fn : UFn} {ρ : Env D Γ}
    {β : Gabbro.Body.Binding} (hL : LRel fn 0 ρ β) {x : String} {j : Nat}
    (hj : paramPos fn.params x = .ok j) {τ : Ty} (var : Var Γ τ) (hvar : lowVar Γ j τ = .ok var)
    (v : Wert D τ) :
    LRel fn 0 (ρ.set var v) (Gabbro.Body.bindLocal β x (valOf τ v)) := by
  intro p k hk
  rw [Nat.zero_add, nthVal_set Γ j τ var ρ v k hvar]
  by_cases hp : p = x
  · subst hp
    rw [hj] at hk
    cases hk
    rw [Gabbro.Body.bindLocal_here, if_pos rfl]
  · have hkj : k ≠ j := by
      intro e
      subst e
      obtain ⟨τ1, h1⟩ := paramPos_name _ _ _ hk
      obtain ⟨τ2, h2⟩ := paramPos_name _ _ _ hj
      rw [h1] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      exact hp h2.1
    rw [if_neg hkj, Gabbro.Body.bindLocal_elsewhere _ _ _ _ hp]
    have := hL p k hk
    rwa [Nat.zero_add] at this

end Gabbro.Bruecke
