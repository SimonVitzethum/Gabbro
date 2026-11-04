/- Recursive validity of canonical constant initializers. -/
module
public import Grammatik.GabbroV.Start.GvStartPflicht
public import Stage0.Senke.Ausdruck.Aggregat.Werte.Sum.Model
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze

private theorem mapM_valid {α β : Type} (f : α → Option β) (valid : β → Prop)
    (step : ∀ x y, f x = some y → valid y) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ y ∈ ys, valid y := by
  intro xs
  induction xs with
  | nil => intro ys made; simp at made; subst ys; simp
  | cons x xs ih =>
    intro ys made
    rw [List.mapM_cons] at made
    cases first : f x with
    | none => simp [first] at made
    | some value =>
      cases rest : xs.mapM f with
      | none => simp [first, rest] at made
      | some values =>
        simp [first, rest] at made
        subst ys
        intro y hy
        rcases List.mem_cons.mp hy with same | tail
        · subst y; exact step x value first
        · exact ih values rest y tail

mutual
/-- Every existing canonical constant initializer retains recursive representation validity. -/
theorem initialConstant_valid {D : Deklaration} (L : Lay D) (τ : Ty) :
    ∀ (k : UKonst) (v : Wert D τ), GabbroV.konstWert τ k = some v → ValueValid L τ v := by
  cases τ with
  | ref n => intro k v made; cases k <;> simp [GabbroV.konstWert] at made
  | fl a b => intro k v made; cases k <;> simp [GabbroV.konstWert] at made
  | arr τ n =>
    have ih := initialConstant_valid L τ
    intro k v made
    by_cases zero : k = .null
    · subst k
      have equation : GabbroV.konstWert (F := D.Fn) (P := D.passt) (.arr τ n) .null =
          (GabbroV.konstWert τ .null).map (fun z => fun _ : Fin n => z) := by
        rw [GabbroV.konstWert]
        rfl
      rw [equation] at made
      obtain ⟨z, hz, eq⟩ := Option.map_eq_some_iff.mp made
      rw [← eq]
      intro i; exact ih _ _ hz
    · have equation : GabbroV.konstWert (F := D.Fn) (P := D.passt) (.arr τ n) k =
          (match GabbroV.konstListe k with
          | some ks => match ks.mapM (GabbroV.konstWert τ) with
            | some vs => if h : vs.length = n then
                some (fun i : Fin n => vs.get ⟨i.val, by rw [h]; exact i.isLt⟩)
              else none
            | none => none
          | none => none) := by
          rw [GabbroV.konstWert]
          · rfl
          · exact zero
      rw [equation] at made
      cases items : GabbroV.konstListe k with
      | none => simp [items] at made
      | some ks =>
        cases values : ks.mapM (GabbroV.konstWert (F := D.Fn) (P := D.passt) τ) with
        | none => simp [items, values] at made
        | some vs =>
          by_cases length : vs.length = n
          · simp only [items, values, length, dite_true] at made
            cases made
            intro i
            exact mapM_valid (GabbroV.konstWert τ) (ValueValid L τ) (fun x y h => ih x y h)
              ks vs values _ (List.get_mem _ _)
          · simp [items, values, length] at made
  | sum cs =>
    intro k v made
    cases k <;> simp only [GabbroV.konstWert, reduceCtorEq] at made
    all_goals
      split at made
      · next bound =>
        obtain ⟨payload, payloadMade, equal⟩ := Option.map_eq_some_iff.mp made
        cases equal
        apply (sumValid_selected L cs _ _).mpr
        simpa only [Fall.to_of] using nutzKonst_valid L _ _ payload payloadMade
      · cases made
  | prod name fs =>
    intro k v made
    cases k with
    | product other fields =>
      rw [GabbroV.konstWert_product] at made
      by_cases same : (name == other) = true
      · have collected : GabbroV.prodKonst (F := D.Fn) (P := D.passt)
            GabbroV.konstWert fs fields = some v := by
          dsimp only [Val] at made
          simpa only [same, ite_true] using made
        exact prodKonst_valid L fs fields v collected
      · simp only [same, ite_false, reduceCtorEq] at made
    | null | zahl _ | wahr _ | text _ | nil | cons _ _ | fall _ _ =>
      simp only [GabbroV.konstWert, reduceCtorEq] at made
  | _ => intro _ _ _; trivial
termination_by sizeOf τ
decreasing_by
  all_goals first
    | decreasing_trivial
    | (have hs := List.sizeOf_get cs ⟨_, ‹_ < cs.length›⟩
       simp only [Ty.sum.sizeOf_spec]
       omega)

/-- The selected constant payload keeps the obligations of its declared type. -/
theorem nutzKonst_valid {D : Deklaration} (L : Lay D) (c : Option Ty) :
    ∀ (k : UKonst) (v : Nutzlast D.Fn D.passt c),
      GabbroV.nutzKonst c k = some v → PayloadValid L c v := by
  cases c with
  | none => intro _ _ _; trivial
  | some τ =>
    intro k v made
    dsimp only [Nutzlast] at made
    have valueMade : GabbroV.konstWert (F := D.Fn) (P := D.passt) τ k = some v := by
      simpa only [GabbroV.nutzKonst] using made
    exact initialConstant_valid L τ k v valueMade
termination_by sizeOf c

/-- Successful product initialization
 preserves every field's representation obligations. -/
theorem prodKonst_valid {D : Deklaration} (L : Lay D) (fs : List Ty) :
    ∀ (ks : List UKonst) (v : ProdVal D.Fn D.passt fs),
      GabbroV.prodKonst GabbroV.konstWert fs ks = some v → ProdValid L fs v := by
  cases fs with
  | nil => intro ks v made; trivial
  | cons τ fs =>
    intro ks v made
    cases ks with
    | nil => simp only [GabbroV.prodKonst_cons_nil, reduceCtorEq] at made
    | cons k ks =>
      rw [GabbroV.prodKonst_cons_cons] at made
      cases first : GabbroV.konstWert (F := D.Fn) (P := D.passt) τ k with
      | none => simp only [first, bind, Option.bind, reduceCtorEq] at made
      | some x =>
        cases rest : GabbroV.prodKonst (F := D.Fn) (P := D.passt) GabbroV.konstWert fs ks with
        | none => simp only [first, rest, bind, Option.bind, reduceCtorEq] at made
        | some xs =>
          have returned : ProdVal.pcons x xs = v := by
            simpa only [first, rest, bind, Option.bind, pure, Option.pure_def,
              Option.some.injEq] using made
          subst v
          exact ⟨initialConstant_valid L τ k x first, prodKonst_valid L fs ks xs rest⟩
termination_by sizeOf fs
end

end Gabbro.Stage0.Senke
