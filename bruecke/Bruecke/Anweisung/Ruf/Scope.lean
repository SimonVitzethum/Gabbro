module
public import Bruecke.Anweisung.Ruf.Kopf
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

/-- All typed value binders add one parameter, irrespective of its representation. -/
theorem mitTy_params (fn : UFn) (x : String) (ty : Ty) :
    (fn.mitTy x ty).params = (x, ty) :: fn.params := by
  cases ty <;> rfl

theorem mitRuf_length (fn : UFn) (x : String) (d : Fin u.fns.length) (ty : Ty) :
    (mitRuf u fn x d ty).params.length = fn.params.length + 1 := by
  unfold mitRuf
  split
  · rfl
  · rw [mitTy_params]
    rfl

/-- The canonical option scope retains the callee's table number and exact extent. -/
theorem mitRuf_params (fn : UFn) (x : String) (d : Fin u.fns.length) {ty : Ty}
    (hb : resultTypeB (fnAt u d) = true) (he : (declOf u).erg d = some ty) :
    (mitRuf u fn x d ty).params = (fn.mitTy x ty).params := by
  have hty : (fnAt u d).ergTy = some ty := (erg_eq u d).symm.trans he
  cases ty
  case opt n =>
    cases ho : (fnAt u d).resOpt with
    | none => simp only [mitRuf, ho]
    | some entry =>
      obtain ⟨num, cnt⟩ := entry
      have same := resultTypeB_option hb hty ho
      subst cnt
      simp only [mitRuf, ho]
      rfl
  all_goals rfl

/-- Every Body scope lookup depends on parameters alone, not on source kind metadata. -/
theorem Sicht.same_params {ft fn : UFn} (h : ft.params = fn.params) : Sicht u ft fn := by
  refine ⟨fun p => ?_, fun p => ?_, fun t => ?_, fun p => ?_, fun p => ?_⟩
  · simp only [numericParam, h]
  · simp only [ptrTab, h]
  · simp only [ptrParam, h]
  · rw [h]
  · simp only [valueParamTy, h]

theorem Sicht.trans {ft fn fg : UFn} (h : Sicht u ft fn) (h' : Sicht u fn fg) :
    Sicht u ft fg :=
  ⟨fun p => (h.1 p).trans (h'.1 p), fun p => (h.2.1 p).trans (h'.2.1 p),
    fun t => (h.2.2.1 t).trans (h'.2.2.1 t),
    fun p => (h.2.2.2.1 p).trans (h'.2.2.2.1 p),
    fun p => (h.2.2.2.2 p).trans (h'.2.2.2.2 p)⟩

theorem Sicht.bindRuf {ft fn : UFn} (h : Sicht u ft fn) (x : String)
    (d : Fin u.fns.length) {ty : Ty} {sh : Gabbro.Body.Shape}
    (ht : shapeOfTy ty = some sh) (hb : resultTypeB (fnAt u d) = true)
    (he : (declOf u).erg d = some ty) :
    Sicht u (ft.mitTy x ty) (mitRuf u fn x d ty) :=
  (h.bindTy x ht).trans (Sicht.same_params (mitRuf_params fn x d hb he).symm)

theorem UmfangB.bindRuf {Γ : Ctx} {fn : UFn} {ns : BodyNames} (h : UmfangB Γ fn ns)
    {x : String} (hx : NameFrisch (protectedNames fn.params fn.kinds) x)
    (d : Fin u.fns.length) {ty : Ty} {sh : Gabbro.Body.Shape}
    (ht : shapeOfTy ty = some sh) (hb : resultTypeB (fnAt u d) = true)
    (he : (declOf u).erg d = some ty) :
    UmfangB (ty :: Γ) (mitRuf u fn x d ty) (ns.push x) := by
  have hty : (fnAt u d).ergTy = some ty := (erg_eq u d).symm.trans he
  cases ty
  case opt n =>
    cases ho : (fnAt u d).resOpt with
    | none => simpa only [mitRuf, ho] using h.bindTy hx ht
    | some entry =>
      obtain ⟨num, cnt⟩ := entry
      have same := resultTypeB_option hb hty ho
      subst cnt
      simpa only [mitRuf, ho] using h.bindOpt num n hx
  all_goals simpa only [mitRuf] using h.bindTy hx ht

theorem protectedNames_mitRuf (fn : UFn) (x : String) (d : Fin u.fns.length)
    {ty : Ty} {sh : Gabbro.Body.Shape} (ht : shapeOfTy ty = some sh) :
    protectedNames (mitRuf u fn x d ty).params (mitRuf u fn x d ty).kinds =
      protectedNames fn.params fn.kinds := by
  unfold mitRuf
  split
  · rfl
  · exact protectedNames_mitTy fn x ht

/-- Runtime bindings are positional; preserving table metadata changes no stored value. -/
theorem PositionalLRel.pushRuf {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {ρ : Env D Γ} {β : Gabbro.Body.Binding} (h : PositionalLRel fn ids 0 ρ β)
    (x id : String) (d : Fin u.fns.length) (hfresh : id ∉ ids) {ty : Ty}
    {sh : Gabbro.Body.Shape} (ht : shapeOfTy ty = some sh) (v : Wert D ty) :
    PositionalLRel (mitRuf u fn x d ty) (id :: ids) 0 (Env.cons v ρ)
      (Gabbro.Body.bindLocal β id (valOf ty v)) := by
  have hp := h.pushTy x id hfresh ht v
  refine ⟨?_, hp.distinct, hp.values⟩
  simpa only [mitRuf_length, mitTy_params, List.length_cons] using hp.length

theorem PositionalLRel.tailRuf {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {id x : String} {d : Fin u.fns.length} {ty : Ty} {ρ : Env D (ty :: Γ)}
    {β : Gabbro.Body.Binding}
    (h : PositionalLRel (mitRuf u fn x d ty) (id :: ids) 0 ρ β) :
    PositionalLRel fn ids 0 ρ.tail β := by
  have hp : PositionalLRel (fn.mitBindung x (0, 0)) (id :: ids) 0 ρ β := by
    refine ⟨?_, h.distinct, h.values⟩
    simpa only [mitRuf_length, UFn.mitBindung, List.length_cons] using h.length
  exact hp.tail

end Gabbro.Bruecke
