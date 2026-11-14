module
public import Bruecke.Ausdruck.Records
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

/-- Exact tags agree with canonical value inference independently of runtime inhabitation. -/
theorem lowWertE_recordRead_type {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option Ty} {sd : USide} {wv : LowWert u Γ Λ} {ty : Ty} {e : Gabbro.Body.Expr}
    (h : lowWertE u Γ Λ fn er sd = .ok wv)
    (hb : recordRead u fn sd = some (some ty, e)) : wv.ty = ty := by
  have untagged {oe : Option Gabbro.Body.Expr}
      (hh : oe.map (fun e => ((none : Option Ty), e)) = some (some ty, e)) : False := by
    cases oe <;> simp at hh
  cases sd
  case param p =>
    cases ht : valueParamTy fn p with
    | none =>
      cases hn : numericSideExprG u fn (.param p) <;> simp [recordRead, ht, hn] at hb
    | some actual =>
      simp only [recordRead, ht, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      cases hj : paramPos fn.params p with
      | error err =>
        unfold valueParamTy at ht
        rw [paramPos_find_none _ _ _ hj] at ht
        cases ht
      | ok j =>
        unfold valueParamTy at ht
        rw [paramPos_find _ _ _ hj] at ht
        cases hq : fn.params[j]? with
        | none => simp [hq] at ht
        | some q =>
          rcases q with ⟨name, actual⟩
          cases actual <;> simp only [hq] at ht <;> try { cases ht; done }
          all_goals
            cases ht
            cases hk : fn.kinds[j]? with
            | none =>
              simp only [lowWertE, lowParamWert, hj, hk, hq] at h
              split at h
              · cases h
              · cases h; rfl
            | some kind =>
              cases kind <;> simp only [lowWertE, lowParamWert, hj, hk, hq] at h
              all_goals split at h
              all_goals first | (cases h; rfl) | (cases h; done)
  case truth b =>
    simp only [recordRead, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simp only [lowWertE, Except.ok.injEq] at h
    cases h
    rfl
  case product identity reordered fields =>
    cases hs : uRecordOf u.records (.prod identity (fields.map (·.1))) with
    | error err => simp [recordRead, hs, Except.toOption, bind, Option.bind] at hb
    | ok schema =>
      cases hr : recordReads u fn fields with
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
            simp only [lowWertE, hg, ha, hs, bind, Except.bind, Except.ok.injEq] at h
            cases h
            rfl
  case field base name | replace base name value =>
    all_goals
      cases hr : recordRead u fn base with
      | none => simp [recordRead, recordProject, hr] at hb
      | some out =>
        rcases out with ⟨tag, be⟩
        cases tag with
        | none => simp [recordRead, recordProject, hr] at hb
        | some baseTy =>
          cases hg : u.exportGate with
          | error err => simp [lowWertE, hg, bind, Except.bind] at h
          | ok gate =>
            cases hw : lowWertE u Γ Λ fn er base with
            | error err => simp [lowWertE, hg, hw, bind, Except.bind] at h
            | ok baseW =>
              have same := lowWertE_recordRead_type hw hr
              rcases baseW with ⟨actual, term⟩
              dsimp only at same
              subst actual
              cases hs : uRecordOf u.records baseTy with
              | error err => simp [recordRead, recordProject, hr, hs, Except.toOption,
                  bind, Option.bind] at hb
              | ok schema =>
                cases hp : uRecordPosition schema.val.fields name with
                | error err => simp [recordRead, recordProject, hr, hs, hp, Except.toOption,
                    bind, Option.bind] at hb
                | ok pos =>
                  rcases pos with ⟨fieldTy, pos⟩
                  first
                  | (simp only [recordRead, recordProject, hr, hs, hp, Except.toOption,
                      Option.unattach, Option.map_some, bind, Option.bind, pure,
                      Option.some.injEq, Prod.mk.injEq] at hb
                     obtain ⟨rfl, rfl⟩ := hb
                     simp only [lowWertE, hg, hw, hs, hp, bind, Except.bind,
                       pure, Except.pure, Except.ok.injEq] at h
                     cases h
                     rfl)
                  | (cases hrV : recordRead u fn value with
                     | none => simp [recordRead, hr, hs, hp, hrV, Except.toOption,
                         bind, Option.bind] at hb
                     | some outV =>
                       rcases outV with ⟨vt, ve⟩
                       simp only [recordRead, hr, hs, hp, hrV, Except.toOption,
                         Option.unattach, Option.map_some, bind, Option.bind, pure,
                         Option.some.injEq, Prod.mk.injEq] at hb
                       obtain ⟨rfl, rfl⟩ := hb
                       cases hf : lowWertAtE u Γ Λ fn er fieldTy value with
                       | error err => simp [lowWertE, hg, hw, hs, hp, hf, bind, Except.bind] at h
                       | ok val =>
                         simp only [lowWertE, hg, hw, hs, hp, hf, bind, Except.bind,
                           pure, Except.pure, Except.ok.injEq] at h
                         cases h
                         rfl)
  all_goals
    simp only [recordRead] at hb
    exact (untagged hb).elim
termination_by sizeOf sd
decreasing_by all_goals (simp_wf <;> omega)

def recordBinderType (u : UProg) (fn : UFn) (d : Option Ty) (v : USide) : Option Ty :=
  match d with
  | some ty@(.prod ..) => some ty
  | some _ => none
  | none => do
    let (some ty@(.prod ..), _) ← recordRead u fn v | none
    pure ty

theorem recordBinderType_prod {fn : UFn} {d : Option Ty} {v : USide} {ty : Ty}
    (h : recordBinderType u fn d v = some ty) : ∃ id fs, ty = .prod id fs := by
  cases d with
  | some declared =>
    cases declared <;> simp only [recordBinderType] at h <;> try { cases h; done }
    case prod id fs => cases h; exact ⟨id, fs, rfl⟩
  | none =>
    cases hr : recordRead u fn v with
    | none => simp [recordBinderType, hr] at h
    | some p =>
      rcases p with ⟨tag, e⟩
      cases tag with
      | none => simp [recordBinderType, hr] at h
      | some actual =>
        cases actual <;> simp only [recordBinderType, hr, bind, Option.bind, pure] at h <;>
          try { cases h; done }
        case prod id fs => cases h; exact ⟨id, fs, rfl⟩

/-- An inferred binder can be fitted at its exact inferred nominal type. -/
theorem lowBindW_record {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {d : Option Ty} {v : USide} {id : Nat} {fs : List Ty} {w : LowWert u Γ Λ}
    (ht : recordBinderType u fn d v = some (.prod id fs))
    (h : lowBindW u Γ Λ fn d v = .ok w) :
    ∃ ev : Expr (declOf u) Γ Λ (.prod id fs),
      lowWertAtE u Γ Λ fn none (.prod id fs) v = .ok ev ∧ w = ⟨.prod id fs, ev⟩ := by
  cases d with
  | some ty =>
    cases ty <;> simp only [recordBinderType, Option.some.injEq] at ht <;> try { cases ht; done }
    case prod identity fields =>
      injection ht with hid hfs
      subst identity
      subst fields
      simp only [lowBindW] at h
      cases hv : lowWertAtE u Γ Λ fn none (.prod id fs) v with
      | error err => simp [hv] at h
      | ok ev => simp only [hv, Except.ok.injEq] at h; exact ⟨ev, rfl, h.symm⟩
  | none =>
    cases hr : recordRead u fn v with
    | none => simp [recordBinderType, hr] at ht
    | some out =>
      rcases out with ⟨tag, e⟩
      cases tag with
      | none => simp [recordBinderType, hr] at ht
      | some ty =>
        cases ty <;> simp only [recordBinderType, hr, bind, Option.bind, pure] at ht <;>
          try { cases ht; done }
        case prod identity fields =>
          injection ht with heq
          injection heq with hid hfs
          subst identity
          subst fields
          have hw : lowWertE u Γ Λ fn none v = .ok w := h
          have same := lowWertE_recordRead_type hw hr
          rcases w with ⟨actual, term⟩
          dsimp only at same
          subst actual
          refine ⟨term, ?_, rfl⟩
          simp only [lowWertAtE, hw, Except.bind, fitW, ↓reduceDIte]

end Gabbro.Bruecke
