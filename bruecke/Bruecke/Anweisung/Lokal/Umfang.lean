module
public import Bruecke.Anweisung.Lokal.Uebersetzung
@[expose] public section

/-! # Local admission and positional scope invariants -/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- Scalar integers, booleans and checked indices may share source names. Capability
    entries stay protected; positional identifiers preserve shadowed scalar values. -/
def protectedNames : List (String × Ty) → List UParamArt → List String
  | [], _ => []
  | (x, .int ..) :: ps, .int :: ks => protectedNames ps ks
  | (x, .bool) :: ps, .bool :: ks => protectedNames ps ks
  | (_, .int ..) :: ps, .index _ :: ks => protectedNames ps ks
  | (_, .prod ..) :: ps, .wert :: ks => protectedNames ps ks
  | (x, _) :: ps, _ :: ks => x :: protectedNames ps ks
  | (x, _) :: ps, [] => x :: protectedNames ps []

def binderOf : UStmt → Option String
  | .bind x _ _ => some x
  | .bindMut x _ _ _ => some x
  | .bindB x _ => some x
  | .bindCall x _ _ => some x
  | .narrowBeg x _ _ => some x
  | .loopBeg x _ _ => some x
  | .bindW x _ _ => some x
  | .matchBeg _ _ x => some x
  | _ => none

def NameFrisch (ns : List String) (x : String) : Prop :=
  x ∉ ns ∧ x ≠ "result" ∧ x ≠ "#erg" ∧ ∀ i, x ≠ oldName i

/-- Scalar bridge binders do not grow the protected names. -/
def BindFrischL : List String → List UStmt → Prop
  | _, [] => True
  | ns, s :: ss =>
      match binderOf s with
      | some x => NameFrisch ns x ∧ BindFrischL ns ss
      | none => BindFrischL ns ss

def BindFrisch (fn : UFn) : Prop := BindFrischL (protectedNames fn.params fn.kinds) fn.body

theorem bindFrischL_bind {ns : List String} {x : String} {d : Option (Int × Int)} {v : USide}
    {ss : List UStmt} (h : BindFrischL ns (.bind x d v :: ss)) :
    NameFrisch ns x ∧ BindFrischL ns ss := h

theorem bindFrischL_bindMut {ns : List String} {x : String} {lo hi : Int} {v : USide}
    {ss : List UStmt} (h : BindFrischL ns (.bindMut x lo hi v :: ss)) :
    NameFrisch ns x ∧ BindFrischL ns ss := h

theorem bindFrischL_bindB {ns : List String} {x : String} {v : UEns}
    {ss : List UStmt} (h : BindFrischL ns (.bindB x v :: ss)) :
    NameFrisch ns x ∧ BindFrischL ns ss := h

theorem bindFrischL_sonst {ns : List String} {s : UStmt} {ss : List UStmt}
    (hs : binderOf s = none) (h : BindFrischL ns (s :: ss)) : BindFrischL ns ss := by
  simp only [BindFrischL, hs] at h
  exact h

/-- Every pointer entry is among the names that a number binder must avoid. -/
theorem pointer_mem_protected : ∀ (ps : List (String × Ty)) (ks : List UParamArt)
    (j : Nat) (x : String) (cap : DataCapTy), ps[j]? = some (x, .ptr cap) →
    x ∈ protectedNames ps ks
  | [], _, _, _, _, h => by simp only [List.getElem?_nil, reduceCtorEq] at h
  | (y, ty) :: ps, ks, 0, x, cap, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases ks with
      | nil => exact List.mem_cons_self ..
      | cons k ks => cases k <;> exact List.mem_cons_self ..
  | (y, ty) :: ps, ks, j + 1, x, cap, h => by
      have ht : ps[j]? = some (x, .ptr cap) := h
      cases ks with
      | nil =>
        have ih := pointer_mem_protected ps [] j x cap ht
        cases ty
        all_goals first
          | exact List.mem_cons_of_mem _ ih
          | (simp only [protectedNames]; exact List.mem_cons_of_mem _ ih)
      | cons k ks =>
        have ih := pointer_mem_protected ps ks j x cap ht
        cases ty <;> cases k
        all_goals first | exact ih | exact List.mem_cons_of_mem _ ih

theorem mitBindung_ctx (fn : UFn) (x : String) (w : Int × Int) :
    (fn.mitBindung x w).params.map (·.2) = .int w.1 w.2 :: fn.params.map (·.2) := rfl

/-! ## 2. The three name conditions survive a fresh binder -/

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

/-- Pointer entry lookup remains unique while integer entries may be hidden. -/
def PointerVisible (fn : UFn) : Prop :=
  ∀ j x cap, fn.params[j]? = some (x, .ptr cap) → paramPos fn.params x = .ok j

/-- Source typing, unshadowed capability entries, and distinct positional identifiers. -/
structure UmfangB (Γ : Ctx) (fn : UFn) (ns : BodyNames) : Prop where
  ctx : Γ = fn.params.map (·.2)
  art : ArtStimmt fn
  namen : ns.active.Nodup
  length : ns.active.length = fn.params.length
  vorrat : ∀ x ∈ ns.active, x ∈ ns.used
  pointer : PointerVisible fn

theorem UmfangB.valid {Γ : Ctx} {fn : UFn} {ns : BodyNames} (h : UmfangB Γ fn ns) :
    ns.Valid := ⟨h.namen, h.vorrat⟩

theorem UmfangB.start (c : Fin u.fns.length) (hA : ArtStimmt (fnAt u c))
    (hN : NamenEindeutig (fnAt u c)) :
    UmfangB (ctxOf u c) (fnAt u c) (BodyNames.start (fnAt u c)) :=
  ⟨rfl, hA, hN, (by simp only [BodyNames.start, List.length_map]), fun _ hx => hx,
    fun j x cap hj => paramPos_of_nodup _ j x (.ptr cap) hN hj⟩

theorem UmfangB.resume {Γ : Ctx} {fn : UFn} {ns : BodyNames} (h : UmfangB Γ fn ns)
    {used : List String} (hu : ∀ x ∈ ns.used, x ∈ used) : UmfangB Γ fn (ns.resume used) :=
  ⟨h.ctx, h.art, h.namen, h.length, fun x hx => hu x (h.vorrat x hx), h.pointer⟩

theorem UmfangB.bind {Γ : Ctx} {fn : UFn} {ns : BodyNames} (h : UmfangB Γ fn ns) {x : String}
    (hx : NameFrisch (protectedNames fn.params fn.kinds) x) (w : Int × Int) :
    UmfangB (.int w.1 w.2 :: Γ) (fn.mitBindung x w) (ns.push x) := by
  have hn := BodyNames.valid_push h.valid x
  refine ⟨?_, artStimmt_mitBindung w h.art hx.2.2.1, hn.1,
    congrArg Nat.succ h.length, hn.2, ?_⟩
  · rw [h.ctx, mitBindung_ctx]
  · intro j y cap hj
    cases j with
    | zero => cases hj
    | succ j =>
      have ht : fn.params[j]? = some (y, .ptr cap) := hj
      have hxy : x ≠ y := by
        intro he
        apply hx.1
        rw [he]
        exact pointer_mem_protected fn.params fn.kinds j y cap ht
      change paramPos ((x, .int w.1 w.2) :: fn.params) y = .ok (j + 1)
      simp only [paramPos, beq_iff_eq, hxy, ↓reduceIte, h.pointer j y cap ht]

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


end Gabbro.Bruecke
