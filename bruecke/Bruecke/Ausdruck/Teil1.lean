module

public import Bruecke.Kodierung
public import Bruecke.Pflichten

@[expose] public section



/-!
# S3, part 2: the expressions -- a lowered G term and its Body term have the same value

For every expression form of the parser's fragment: an index (`lowIdx` / `idxExpr`), a value side
(`lowSideVal` / `sideExpr`), an `ensures` side (`lowSideEns` / `ensSide`) and an `ensures`
predicate (`lowEns` / `ensExpr`), the Body term `Pflichten.lean` computes evaluates, in a Body
state related to the G state (`WRel`, `LRel`), to the G value read as a Body value.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- **The binding relation**: every parameter name reads, in the Body binding, the entry of the
    G environment at its position (shifted by `sh`: `1` in an `ensures` context with a result,
    where the result rides first) -- the lookup is `paramPos`, as in the lowering. -/
def LRel {D : Deklaration} {Γ : Ctx} (fn : UFn) (sh : Nat) (ρ : Env D Γ)
    (β : Gabbro.Body.Binding) : Prop :=
  ∀ p j, paramPos fn.params p = .ok j → β p = nthVal ρ (sh + j)

/-- The consistency of a function's two parameter lists (kinds and types, as the elaborator
    writes both): a pointer kind is a pointer type to the same table. Checked per unit. -/
def ArtStimmtPtr (fn : UFn) : Prop :=
  ∀ (j num : Nat) (w : Bool), fn.kinds[j]? = some (.ptr (.table num (true, w))) →
    ∃ w', (fn.params[j]?).map (·.2) = some (.ptr (.table num (true, w')))

/-- The parameter kinds the bridge speaks about: pointers, indices and numbers. -/
def ArtSchlicht : UParamArt → Bool
  | .ptr .. | .index _ | .int => true
  | _ => false

/-- The parameter types the bridge speaks about: numbers (an index is one) and pointers. -/
def TySchlicht : Ty → Bool
  | .int .. | .ptr .. => true
  | _ => false

/-- A parameter the bridge speaks about: a number or a pointer, and not the hidden result binder
    `#erg` (the lowering reads `result` from it where a body has no result type). -/
def ParamSchlicht (q : String × Ty) : Bool := TySchlicht q.2 && q.1 != "#erg"

/-- The parameter conditions: the kinds agree with the types at pointers, and every parameter is
    a pointer, an index or a number (no aggregate, reference, option, reason or `never`: the typed
    value lowering `lowWertE` then answers the number lowering, `lowParamWert_none`). -/
def ArtStimmt (fn : UFn) : Prop :=
  ArtStimmtPtr fn ∧ (∀ k ∈ fn.kinds, ArtSchlicht k = true) ∧ (∀ q ∈ fn.params, ParamSchlicht q = true)

/-- Table names are unique: the lookup by name finds every table at its own index; and no table has
    an aggregate field (`lowDurchWert`/`lowTabWert` then answer `none`). -/
def TabEindeutig (u : UProg) : Prop :=
  (∀ t : Fin u.tabs.length, tabIdx u.tabs (tabAt u t).name = .ok t) ∧
    ∀ t : Fin u.tabs.length, (tabAt u t).werte = []

variable {u : UProg}

/-! ## 1. Indices -/

theorem lowIdx_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {sh : Nat}
    {t : Fin u.tabs.length} {ix : UIdx} {e : Expr (declOf u) Γ Λ (.index ((declOf u).count t))}
    (h : lowIdx u Γ Λ fn sh t ix = .ok e) (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ)
    (w : Gabbro.Body.World) (β : Gabbro.Body.Binding) (hL : LRel fn sh ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ (idxExpr ix) = some (.int (eval σ₀ e σ ρ).n) := by
  cases ix with
  | lit n =>
    simp only [lowIdx] at h
    split at h
    · split at h
      · cases h
        rfl
      · cases h
    · cases h
  | param p =>
    simp only [lowIdx] at h
    split at h
    · cases h
    · rename_i j hj
      split at h
      · split at h
        · cases h
        · rename_i v hv
          cases h
          simp only [idxExpr, Gabbro.Body.eval]
          rw [hL p j hj, nthVal_lowVar Γ (sh + j) _ v ρ hv]
          rfl
      · split at h
        · split at h
          · split at h
            · split at h
              · cases h
              · rename_i v hv
                cases h
                simp only [idxExpr, Gabbro.Body.eval]
                rw [hL p j hj, nthVal_lowVar Γ (sh + j) _ v ρ hv]
                rfl
            · cases h
          · cases h
        · cases h
      · cases h

/-! ## 2. Slot terms: the casts of the lowering are the constructors -/

theorem durchTerm_heq {space : Nat} (Γ : Ctx) (Λ : List (Res (declOf u)))
    (num : Nat) (w : Bool) (h : num < u.tabs.length)
    (fh : FieldHit u ⟨num, h⟩) (v : Var Γ (.ptr ⟨space, ⟨true, w, none⟩, .table num⟩))
    (hc : (declOf u).capTab space num = some (⟨num, h⟩ : Fin u.tabs.length))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ) :
    HEq (durchTerm u Γ Λ num w h fh v hc i hL)
      (Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩ hc fh.idx i hL) := by
  unfold durchTerm; exact mpr_heq _ _

theorem durchOwnTerm_heq {space : Nat} (Γ : Ctx) (Λ : List (Res (declOf u)))
    (num : Nat) (w : Bool) (h : num < u.tabs.length) (fh : FieldHit u ⟨num, h⟩)
    (owner : Nat) (m : Fin u.marken.length)
    (v : Var Γ (.ptr ⟨space, ⟨true, w, some owner⟩, .table num⟩))
    (hc : (declOf u).capTab space num = some (⟨num, h⟩ : Fin u.tabs.length))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hm : eignerMarke u owner = some m) (he : m ∈ eignerAt u ⟨num, h⟩)
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ) :
    let guards := ownGuard_holds u Λ ⟨num, h⟩ owner m hm he hL
    HEq (durchOwnTerm u Γ Λ num w h fh owner m v hc i hm he hL)
      (Expr.thruOwn (D := declOf u) (Expr.var v) ⟨num, h⟩ hc fh.idx i m 0
        guards.1 guards.2.1 guards.2.2 hL) := by
  unfold durchOwnTerm
  exact mpr_heq _ _

theorem slotTerm_heq (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    HEq (slotTerm u Γ Λ t fh i hL) (Expr.slot (D := declOf u) t fh.idx i hL) := by
  unfold slotTerm; exact mpr_heq _ _

theorem altTerm_heq (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    HEq (altTerm u Γ Λ t fh i hL) (Expr.oldS (D := declOf u) t fh.idx i hL) := by
  unfold altTerm; exact mpr_heq _ _

/-- The Body place of a declared slot holds the G slot. -/
theorem wrel_lies {σ : World (declOf u)} {w : Gabbro.Body.World} (hW : WRel u σ w)
    (c : String) (t : Fin u.tabs.length) (ht : tabIdx u.tabs c = .ok t)
    (fld : String) (fh : FieldHit u t) (hf : fieldHit u t fld = .ok fh) (k : Int) :
    w (.slot c k fld) = valOf ((declOf u).typ t fh.idx) (σ.slots t k fh.idx) := by
  apply hW
  simp only [slotWert, ht, hf]

/-- The pointer parameter the lowering resolves names, in `Pflichten.ptrTab`, its table. -/
theorem ptrTab_of (fn : UFn) (hA : ArtStimmt fn) (b : String) (j num : Nat) (w : Bool)
    (hj : paramPos fn.params b = .ok j) (hp : fn.kinds[j]? = some (.ptr (.table num (true, w))))
    (h : num < u.tabs.length) :
    ptrTab u fn b = some (tabAt u ⟨num, h⟩).name := by
  obtain ⟨w', hw'⟩ := hA.1 j num w hp
  obtain ⟨τ, hτ⟩ := paramPos_name _ _ _ hj
  rw [hτ] at hw'
  simp only [Option.map_some, Option.some.injEq] at hw'
  subst hw'
  unfold ptrTab
  rw [paramPos_find _ _ _ hj, hτ]
  simp [tabAt, List.getElem?_eq_getElem h]

/-- Typed parameter lookup also identifies a write-only capability's table. -/
theorem ptrTab_of_type {space : Nat} {owner : Option Nat}
    (fn : UFn) (b : String) (j num : Nat) (read write : Bool)
    (hj : paramPos fn.params b = .ok j)
    (hp : (fn.params[j]?).map (·.2) =
      some (.ptr ⟨space, ⟨read, write, owner⟩, .table num⟩))
    (h : num < u.tabs.length) : ptrTab u fn b = some (tabAt u ⟨num, h⟩).name := by
  obtain ⟨τ, hτ⟩ := paramPos_name _ _ _ hj
  rw [hτ] at hp
  simp only [Option.map_some, Option.some.injEq] at hp
  subst hp
  unfold ptrTab
  rw [paramPos_find _ _ _ hj, hτ]
  simp [tabAt, List.getElem?_eq_getElem h]

/-! ## 3. Value sides -/

theorem lowParamSide_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {sh : Nat}
    {p : String} {ls : LowSide u Γ Λ} (h : lowParamSide u Γ Λ fn sh p = .ok ls)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (β : Gabbro.Body.Binding)
    (hL : LRel fn sh ρ β) :
    β p = valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ) := by
  unfold lowParamSide at h
  split at h
  · cases h
  · rename_i j hj
    split at h
    · cases h
    · split at h
      · rename_i a b _
        split at h
        · cases h
        · rename_i v hv
          cases h
          rw [hL p j hj, nthVal_lowVar Γ (sh + j) _ v ρ hv]
          rfl
      · cases h
    · cases h

theorem lowDurch_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {sh : Nat}
    {b fname : String} {ix : UIdx} {ls : LowSide u Γ Λ}
    (h : lowDurch u Γ Λ fn sh b fname ix = .ok ls) (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WRel u σ w) (hL : LRel fn sh ρ β) :
    ∃ c, ptrTab u fn b = some c ∧
      Gabbro.Body.eval ⟨w, β⟩ (.place c (idxExpr ix) fname) =
        some (valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ)) := by
  unfold lowDurch at h
  split at h
  · cases h
  · rename_i j hj
    split at h
    · rename_i space wr num hp
      split at h
      · rename_i hlt
        split at h
        · cases h
        · rename_i fh hfh
          split at h
          · cases h
          · rename_i v hv
            split at h
            · cases h
            · rename_i i hi
              split at h
              · rename_i hG
                cases hcap : checkedTableCap u space num hlt with
                | error error => simp [hcap] at h
                | ok cap =>
                  cases hparam : checkedPointerParam fn j ⟨space, ⟨true, wr, none⟩, .table num⟩ with
                  | error error => simp [hcap, hparam] at h
                  | ok parameter =>
                    simp only [hcap, hparam, bind, Except.bind] at h
                    cases h
                    refine ⟨_, ptrTab_of_type fn b j num true wr hj parameter.down.2 hlt, ?_⟩
                    simp only [Gabbro.Body.eval]
                    rw [lowIdx_sim hi σ₀ σ ρ w β hL]
                    simp only
                    rw [wrel_lies hW _ ⟨num, hlt⟩ (hT.1 _) fname fh hfh]
                    rw [valOf_eval_heq fh.hint.symm _ _
                      (durchTerm_heq Γ Λ num wr hlt fh v cap.down i hG) σ₀ σ ρ]
                    rfl
              · cases h
      · cases h
    · rename_i space wr owner num hp
      split at h
      · rename_i hlt
        split at h
        · cases h
        · rename_i fh hfh
          split at h
          · cases h
          · rename_i m hm
            split at h
            · cases h
            · rename_i v hv
              split at h
              · cases h
              · rename_i i hi
                split at h
                · rename_i hG
                  split at h
                  · rename_i he
                    cases hcap : checkedTableCap u space num hlt with
                    | error error => simp [hcap] at h
                    | ok cap =>
                      cases hparam : checkedPointerParam fn j
                          ⟨space, ⟨true, wr, some owner⟩, .table num⟩ with
                      | error error => simp [hcap, hparam] at h
                      | ok parameter =>
                        simp only [hcap, hparam, bind, Except.bind] at h
                        cases h
                        refine ⟨_, ptrTab_of_type fn b j num true wr hj parameter.down.2 hlt, ?_⟩
                        simp only [Gabbro.Body.eval]
                        rw [lowIdx_sim hi σ₀ σ ρ w β hL]
                        simp only
                        rw [wrel_lies hW _ ⟨num, hlt⟩ (hT.1 _) fname fh hfh]
                        rw [valOf_eval_heq fh.hint.symm _ _
                          (durchOwnTerm_heq Γ Λ num wr hlt fh owner m v cap.down i hm he hG) σ₀ σ ρ]
                        rfl
                  · cases h
                · cases h
      · cases h
    · cases h

theorem lowTabRead_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {sh : Nat}
    {b fname : String} {ix : UIdx} {ls : LowSide u Γ Λ}
    (h : lowTabRead u Γ Λ fn sh b fname ix = .ok ls)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WRel u σ w) (hL : LRel fn sh ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ (.place b (idxExpr ix) fname) =
      some (valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ)) := by
  unfold lowTabRead at h
  split at h
  · cases h
  · rename_i t ht
    split at h
    · cases h
    · rename_i fh hfh
      split at h
      · cases h
      · rename_i i hi
        split at h
        · rename_i hG
          cases h
          simp only [Gabbro.Body.eval]
          rw [lowIdx_sim hi σ₀ σ ρ w β hL]
          simp only
          rw [wrel_lies hW _ t ht fname fh hfh]
          rw [valOf_eval_heq fh.hint.symm _ _
            (slotTerm_heq Γ Λ t fh i hG) σ₀ σ ρ]
          rfl
        · cases h

/-- An entry read: the G term reads the ENTRY world `σ₀`; the Body place is read in the entry
    state `s₀` (whose binding holds the parameters as well). -/
theorem lowAltRead_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {sh : Nat}
    {b fname : String} {ix : UIdx} {ls : LowSide u Γ Λ}
    (h : lowAltRead u Γ Λ fn sh b fname ix = .ok ls) (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (c : String) (hc : ptrTab u fn b = some c)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w₀ : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WRel u σ₀ w₀) (hL : LRel fn sh ρ β) :
    Gabbro.Body.eval ⟨w₀, β⟩ (.place c (idxExpr ix) fname) =
      some (valOf (.int ls.range.1 ls.range.2) (eval σ₀ ls.term σ ρ)) := by
  unfold lowAltRead at h
  split at h
  · cases h
  · rename_i t ht
    split at h
    · cases h
    · rename_i fh hfh
      split at h
      · cases h
      · rename_i i hi
        split at h
        · rename_i hG
          cases h
          -- the basis is a pointer parameter (`ptrTab` answered)
          unfold lowBasisTab at ht
          have hct : tabIdx u.tabs c = .ok t := by
            split at ht
            · rename_i j hj
              split at ht
              · rename_i space wr owner num hp
                split at ht
                · rename_i hlt
                  cases hcap : checkedTableCap u space num hlt with
                  | error error => simp [hcap] at ht
                  | ok cap =>
                    cases hparam : checkedPointerParam fn j
                        ⟨space, ⟨true, wr, owner⟩, .table num⟩ with
                    | error error => simp [hcap, hparam] at ht
                    | ok parameter =>
                      simp only [hcap, hparam, bind, Except.bind] at ht
                      cases ht
                      rw [ptrTab_of_type fn b j num true wr hj parameter.down.2 hlt] at hc
                      cases hc
                      exact hT.1 _
                · cases ht
              · cases ht
            · rename_i e he
              unfold ptrTab at hc
              rw [paramPos_find_none _ _ _ he] at hc
              cases hc
          simp only [Gabbro.Body.eval]
          rw [lowIdx_sim hi σ₀ σ ρ w₀ β hL]
          simp only
          rw [wrel_lies hW _ t hct fname fh hfh]
          rw [valOf_eval_heq fh.hint.symm _ _
            (altTerm_heq Γ Λ t fh i hG) σ₀ σ ρ]
          rfl
        · cases h

/-! ## The typed value lookups in the bridge's fragment -/

theorem fieldHitW_none {t : Fin u.tabs.length} (hw : (tabAt u t).werte = []) (fname : String) :
    fieldHitW u t fname = none := by
  unfold fieldHitW
  split
  · rfl
  · have hn : ∀ f, wertFeldAt u t f = none := by
      intro f; unfold wertFeldAt; rw [hw]; split <;> rfl
    simp [hn]

/-- A numeric parameter in the scalar fragment bypasses the general value lookup. -/
theorem lowParamWert_none {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {sh : Nat} {p : String}
    (hA : ArtStimmt fn) (hN : numericParam fn p = true) : lowParamWert u Γ Λ fn sh p = none := by
  unfold lowParamWert
  split
  · rfl
  · rename_i j hj
    unfold numericParam at hN
    rw [paramPos_find _ _ _ hj] at hN
    cases hpj : fn.params[j]? with
    | none => simp [hpj] at hN
    | some q =>
      rw [hpj] at hN
      obtain ⟨name, τ⟩ := q
      cases τ <;> try { simp at hN }
      case int lo hi =>
        cases hkj : fn.kinds[j]? with
        | none => rfl
        | some k =>
          have hk := hA.2.1 k (List.mem_of_getElem? hkj)
          cases k <;> first | rfl | (simp [ArtSchlicht] at hk; done)

/-- No aggregate field: the value lookup of a slot read through a pointer answers nothing. -/
theorem lowDurchWert_none {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {sh : Nat}
    {b fname : String} {ix : UIdx} (hT : TabEindeutig u) :
    lowDurchWert u Γ Λ fn sh b fname ix = none := by
  unfold lowDurchWert
  split
  · rfl
  · split
    · rename_i space wr num hp
      split
      · rename_i hlt
        rw [fieldHitW_none (hT.2 ⟨num, hlt⟩)]
        rfl
      · rfl
    · rfl

/-- No aggregate field: the value lookup of a slot read at a table answers nothing. -/
theorem lowTabWert_none {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {sh : Nat}
    {b fname : String} {ix : UIdx} (hT : TabEindeutig u) :
    lowTabWert u Γ Λ fn sh b fname ix = none := by
  unfold lowTabWert
  split
  · rfl
  · rename_i t _
    rw [fieldHitW_none (hT.2 t)]
    rfl

end Gabbro.Bruecke
