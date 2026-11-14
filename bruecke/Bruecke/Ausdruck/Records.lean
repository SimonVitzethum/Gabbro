module
public import Bruecke.Ausdruck.RecordFit
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

mutual
/-- The actual source value lowerer agrees with the record reader, including its exact
    nominal type information. The scalar fallback uses the existing scalar simulation. -/
theorem lowWertE_recordRead_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option Ty} {sd : USide} {wv : LowWert u Γ Λ}
    {tag : Option Ty} {eB : Gabbro.Body.Expr}
    (h : lowWertE u Γ Λ fn er sd = .ok wv)
    (hb : recordRead u fn (numericSideExprG u fn) sd = some (tag, eB))
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ w)
    (hL : LRel fn (if er.isSome then 1 else 0) ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf wv.ty (eval σ₀ wv.term σ ρ)) ∧
      (∀ ty, tag = some ty → wv.ty = ty) := by
  have scalarCase {sd' : USide} {wv' : LowWert u Γ Λ} {tag' : Option Ty}
      {e' : Gabbro.Body.Expr} (h' : lowWertE u Γ Λ fn er sd' = .ok wv')
      (hb' : recordRead u fn (numericSideExprG u fn) sd' = some (tag', e'))
      (read : recordRead u fn (numericSideExprG u fn) sd' =
        (numericSideExprG u fn sd').map (none, ·)) :
      Gabbro.Body.eval ⟨w, β⟩ e' = some (valOf wv'.ty (eval σ₀ wv'.term σ ρ)) ∧
        (∀ ty, tag' = some ty → wv'.ty = ty) := by
    rw [read] at hb'
    cases hs : numericSideExprG u fn sd' with
    | none => simp [hs] at hb'
    | some e =>
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb'
        obtain ⟨rfl, rfl⟩ := hb'
        obtain ⟨ls, rfl, hv⟩ := lowWertE_sim h' hs hA hT σ₀ σ ρ w β hW hL
        exact ⟨hv, fun _ he => by cases he⟩
  -- Retain constructor size relationships across the mutual simulation proofs.
  match sd, h, hb with
  | .param p, h, hb =>
      cases ht : valueParamTy fn p with
      | none =>
          cases hs : numericSideExprG u fn (.param p) with
          | none => simp [recordRead, ht, hs] at hb
          | some e =>
              simp only [recordRead, ht, hs, Option.map_some, Option.some.injEq,
                Prod.mk.injEq] at hb
              obtain ⟨rfl, rfl⟩ := hb
              obtain ⟨ls, rfl, hv⟩ := lowWertE_sim h hs hA hT σ₀ σ ρ w β hW hL
              exact ⟨hv, fun _ he => by cases he⟩
      | some ty =>
          simp only [recordRead, ht, Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          obtain ⟨hv, hty⟩ := lowParam_record_sim ht h σ₀ σ ρ β hL
          exact ⟨congrArg some hv, fun t he => (Option.some.inj he) ▸ hty⟩
  | .truth b, h, hb =>
      simp only [recordRead, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      simp only [lowWertE, Except.ok.injEq] at h
      subst wv
      cases b <;> exact ⟨rfl, fun _ he => Option.some.inj he⟩
  | .product identity reordered fields, h, hb =>
      cases hs : uRecordOf u.records (.prod identity (fields.map (·.1))) with
      | error err => simp [recordRead, hs, Except.toOption, bind, Option.bind] at hb
      | ok schema =>
          cases hr : recordReads u fn (numericSideExprG u fn) fields with
          | none => simp [recordRead, hs, hr, Except.toOption, bind, Option.bind] at hb
          | some es =>
              simp only [recordRead, hs, Except.toOption, hr, Option.unattach, Option.map_some,
                bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at hb
              obtain ⟨rfl, rfl⟩ := hb
              cases hg : u.exportGate with
              | error err => simp [lowWertE, hg, bind, Except.bind] at h
              | ok gate =>
                  cases ha : lowProductArgs u Γ Λ fn er fields with
                  | error err => simp [lowWertE, hg, ha, bind, Except.bind] at h
                  | ok args =>
                      simp only [lowWertE, hg, ha, hs, bind, Except.bind,
                        Except.ok.injEq] at h
                      cases h
                      have hv := lowProductArgs_record_sim ha hr hA hT σ₀ σ ρ w β hW hL
                      refine ⟨?_, fun _ he => Option.some.inj he⟩
                      rw [Gabbro.Body.eval_recOf, hv]
                      rfl
  | .field base name, h, hb =>
      cases hr : recordRead u fn (numericSideExprG u fn) base with
      | none => simp [recordRead, hr] at hb
      | some out =>
          rcases out with ⟨bt, be⟩
          cases bt with
          | none => simp [recordRead, hr] at hb
          | some ty =>
              cases hg : u.exportGate with
              | error err => simp [lowWertE, hg, bind, Except.bind] at h
              | ok gate =>
                  cases hw : lowWertE u Γ Λ fn er base with
                  | error err => simp [lowWertE, hg, hw, bind, Except.bind] at h
                  | ok baseW =>
                      obtain ⟨hv, hty⟩ := lowWertE_recordRead_sim hw hr hA hT σ₀ σ ρ w β hW hL
                      have same := hty ty rfl
                      rcases baseW with ⟨actual, term⟩
                      dsimp only at same
                      subst actual
                      cases hs : uRecordOf u.records ty with
                      | error err => simp [recordRead, hr, hs, Except.toOption, bind, Option.bind] at hb
                      | ok schema =>
                          cases hp : uRecordPosition schema.val.fields name with
                          | error err => simp [recordRead, hr, hs, hp, Except.toOption, bind, Option.bind] at hb
                          | ok pos =>
                              rcases pos with ⟨fieldTy, pos⟩
                              simp only [recordRead, hr, hs, hp, Except.toOption,
                                Option.unattach, Option.map_some, bind, Option.bind, pure,
                                Option.some.injEq, Prod.mk.injEq] at hb
                              obtain ⟨rfl, rfl⟩ := hb
                              simp only [lowWertE, hg, hw, hs, hp, bind, Except.bind,
                                pure, Except.pure, Except.ok.injEq] at h
                              cases h
                              let baseE := cast (congrArg (Expr (declOf u) Γ Λ) schema.property.symm) term
                              have he : Gabbro.Body.eval ⟨w, β⟩ be =
                                  some (.record (valOfProd _ (eval σ₀ baseE σ ρ))) := by
                                rw [hv, ← valOf_cast_eval schema.property.symm term σ₀ σ ρ]
                                rfl
                              refine ⟨?_, fun _ heq => Option.some.inj heq⟩
                              rw [Gabbro.Body.eval_recGet _ _ _ _ he]
                              exact valOfProd_get (D := declOf u) pos (eval σ₀ baseE σ ρ)
  | .replace base name value, h, hb =>
      cases hr : recordRead u fn (numericSideExprG u fn) base with
      | none => simp [recordRead, hr] at hb
      | some out =>
          rcases out with ⟨bt, be⟩
          cases bt with
          | none => simp [recordRead, hr] at hb
          | some ty =>
              cases hg : u.exportGate with
              | error err => simp [lowWertE, hg, bind, Except.bind] at h
              | ok gate =>
                  cases hw : lowWertE u Γ Λ fn er base with
                  | error err => simp [lowWertE, hg, hw, bind, Except.bind] at h
                  | ok baseW =>
                      obtain ⟨hv, hty⟩ := lowWertE_recordRead_sim hw hr hA hT σ₀ σ ρ w β hW hL
                      have same := hty ty rfl
                      rcases baseW with ⟨actual, term⟩
                      dsimp only at same
                      subst actual
                      cases hs : uRecordOf u.records ty with
                      | error err => simp [recordRead, hr, hs, Except.toOption, bind, Option.bind] at hb
                      | ok schema =>
                          cases hp : uRecordPosition schema.val.fields name with
                          | error err => simp [recordRead, hr, hs, hp, Except.toOption, bind, Option.bind] at hb
                          | ok pos =>
                              rcases pos with ⟨fieldTy, pos⟩
                              cases hrV : recordRead u fn (numericSideExprG u fn) value with
                              | none => simp [recordRead, hr, hs, hp, hrV, Except.toOption, bind, Option.bind] at hb
                              | some outV =>
                                  rcases outV with ⟨vt, ve⟩
                                  simp only [recordRead, hr, hs, hp, hrV, Except.toOption,
                                    Option.unattach, Option.map_some, bind, Option.bind, pure,
                                    Option.some.injEq, Prod.mk.injEq] at hb
                                  obtain ⟨rfl, rfl⟩ := hb
                                  cases hf : lowWertAtE u Γ Λ fn er fieldTy value with
                                  | error err => simp [lowWertE, hg, hw, hs, hp, hf,
                                      bind, Except.bind] at h
                                  | ok val =>
                                      simp only [lowWertE, hg, hw, hs, hp, hf, bind, Except.bind,
                                        pure, Except.pure, Except.ok.injEq] at h
                                      cases h
                                      have hev := lowWertAtE_recordRead_sim hf hrV hA hT σ₀ σ ρ w β hW hL
                                      let baseE := cast (congrArg (Expr (declOf u) Γ Λ)
                                        schema.property.symm) term
                                      have he : Gabbro.Body.eval ⟨w, β⟩ be =
                                          some (.record (valOfProd _ (eval σ₀ baseE σ ρ))) := by
                                        rw [hv, ← valOf_cast_eval schema.property.symm term σ₀ σ ρ]
                                        rfl
                                      refine ⟨?_, fun _ heq => Option.some.inj heq⟩
                                      rw [Gabbro.Body.eval_recSet _ _ _ _ _ _ he hev
                                        (by
                                          rw [valOfProd_length (D := declOf u) _ (eval σ₀ baseE σ ρ)]
                                          exact recordIndex_lt pos)]
                                      rw [← valOfProd_set (D := declOf u) pos
                                        (eval σ₀ baseE σ ρ) (eval σ₀ val σ ρ)]
                                      rfl
  | .lit _, h, hb | .slot _ _ _, h, hb | .tab _ _ _, h, hb | .old _ _ _, h, hb
  | .glob _, h, hb | .erg, h, hb | .add _ _, h, hb | .sub _ _, h, hb | .mul _ _, h, hb
  | .conv _ _ _, h, hb | .band _ _, h, hb | .bor _ _, h, hb | .bxor _ _, h, hb
  | .div _ _, h, hb | .rem _ _, h, hb | .shl _ _, h, hb | .shr _ _, h, hb
  | .neg _, h, hb | .refSlot _ _, h, hb | .idx _ _, h, hb | .len _, h, hb
  | .text _, h, hb | .arrNil, h, hb | .arrCons _ _, h, hb | .upd _ _ _, h, hb
  | .typed _ _, h, hb | .eng _ _ _, h, hb | .ib1 _ _ _, h, hb | .ib2 _ _ _ _, h, hb
  | .zaehle _ _ _, h, hb | .zaehleBaum _ _ _ _ _ _, h, hb | .zaehleFeld _ _ _, h, hb
  | .taggedEmpty _ _, h, hb | .taggedValue _ _ _, h, hb | .predicate _, h, hb
  | .option _ _, h, hb | .absent _, h, hb | .present _ _, h, hb | .reason _ _, h, hb
  | .function _ _, h, hb => exact scalarCase h hb (by rw [recordRead] <;> simp)
termination_by 5 * sizeOf sd + 1
decreasing_by all_goals (simp_wf <;> omega)

theorem lowWertAtE_recordRead_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option Ty} {ty : Ty} {sd : USide} {e : Expr (declOf u) Γ Λ ty}
    {tag : Option Ty} {eB : Gabbro.Body.Expr}
    (h : lowWertAtE u Γ Λ fn er ty sd = .ok e)
    (hb : recordRead u fn (numericSideExprG u fn) sd = some (tag, eB))
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ w)
    (hL : LRel fn (if er.isSome then 1 else 0) ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf ty (eval σ₀ e σ ρ)) := by
  unfold lowWertAtE at h
  split at h
  · simp [recordRead, numericSideExprG] at hb
  · simp [recordRead, numericSideExprG] at hb
  · cases hw : lowWertE u Γ Λ fn er sd with
    | error err => simp [hw] at h
    | ok wv =>
        rw [hw] at h
        have hv := (lowWertE_recordRead_sim hw hb hA hT σ₀ σ ρ w β hW hL).1
        rw [hv, fitW_val wv h σ₀ σ ρ]
termination_by 5 * sizeOf sd + 2
decreasing_by all_goals (simp_wf <;> omega)

theorem lowProductArgs_record_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option Ty} {fields : List (Ty × USide)}
    {args : Args (declOf u) Γ Λ (fields.map (·.1))} {es : List Gabbro.Body.Expr}
    (h : lowProductArgs u Γ Λ fn er fields = .ok args)
    (hb : recordReads u fn (numericSideExprG u fn) fields = some es)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ w)
    (hL : LRel fn (if er.isSome then 1 else 0) ρ β) :
    Gabbro.Body.evalAll ⟨w, β⟩ es = some (valOfProd _ (evalProd σ₀ args σ ρ)) := by
  match fields, args, h, hb with
  | [], args, h, hb =>
      simp only [lowProductArgs, Except.ok.injEq] at h
      cases h
      simp only [recordReads, Option.some.injEq] at hb
      cases hb
      rfl
  | (ty, sd) :: rest, args, h, hb =>
      cases hr : recordRead u fn (numericSideExprG u fn) sd with
      | none => simp [recordReads, hr] at hb
      | some out =>
          rcases out with ⟨tag, be⟩
          cases hrs : recordReads u fn (numericSideExprG u fn) rest with
          | none => simp [recordReads, hr, hrs] at hb
          | some bes =>
              simp only [recordReads, hr, hrs, bind, Option.bind, pure, Option.some.injEq] at hb
              cases hb
              cases hh : lowWertAtE u Γ Λ fn er ty sd with
              | error err => simp [lowProductArgs, hh, bind, Except.bind] at h
              | ok head =>
                  cases ht : lowProductArgs u Γ Λ fn er rest with
                  | error err => simp [lowProductArgs, hh, ht, bind, Except.bind] at h
                  | ok tail =>
                      simp only [lowProductArgs, hh, ht, bind, Except.bind,
                        pure, Except.pure, Except.ok.injEq] at h
                      cases h
                      have hv := lowWertAtE_recordRead_sim hh hr hA hT σ₀ σ ρ w β hW hL
                      have hvs := lowProductArgs_record_sim ht hrs hA hT σ₀ σ ρ w β hW hL
                      simp only [Gabbro.Body.evalAll, hv, hvs]
                      rfl
termination_by 5 * sizeOf fields + 3
decreasing_by all_goals (simp_wf <;> omega)
end

/-- Generic source-to-Body simulation for records and scalar leaves in the actual lowerer. -/
theorem lowWertE_rec_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {er : Option Ty}
    {sd : USide} {wv : LowWert u Γ Λ} {eB : Gabbro.Body.Expr}
    (h : lowWertE u Γ Λ fn er sd = .ok wv) (hb : sideExprG u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ w)
    (hL : LRel fn (if er.isSome then 1 else 0) ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf wv.ty (eval σ₀ wv.term σ ρ)) := by
  unfold sideExprG at hb
  cases hr : recordRead u fn (numericSideExprG u fn) sd with
  | none => simp [hr] at hb
  | some out =>
      rcases out with ⟨tag, e⟩
      simp only [hr, Option.map_some, Option.some.injEq] at hb
      cases hb
      exact (lowWertE_recordRead_sim h hr hA hT σ₀ σ ρ w β hW hL).1

/-- Checking-mode simulation is shared by record returns, replacements and call arguments. -/
theorem lowWertAtE_rec_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {er : Option Ty}
    {ty : Ty} {sd : USide} {e : Expr (declOf u) Γ Λ ty} {eB : Gabbro.Body.Expr}
    (h : lowWertAtE u Γ Λ fn er ty sd = .ok e) (hb : sideExprG u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ w)
    (hL : LRel fn (if er.isSome then 1 else 0) ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf ty (eval σ₀ e σ ρ)) := by
  unfold sideExprG at hb
  cases hr : recordRead u fn (numericSideExprG u fn) sd with
  | none => simp [hr] at hb
  | some out =>
      rcases out with ⟨tag, be⟩
      simp only [hr, Option.map_some, Option.some.injEq] at hb
      cases hb
      exact lowWertAtE_recordRead_sim h hr hA hT σ₀ σ ρ w β hW hL

end Gabbro.Bruecke
