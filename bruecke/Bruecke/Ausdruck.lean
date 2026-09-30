import Bruecke.Kodierung
import Bruecke.Pflichten

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
def ArtStimmt (fn : UFn) : Prop :=
  ∀ (j num : Nat) (w : Bool), fn.parten[j]? = some (UParamArt.ptr num w) →
    ∃ w', (fn.params[j]?).map (·.2) = some (Ty.ptr num w')

/-- Table names are unique: the lookup by name finds every table at its own index. -/
def TabEindeutig (u : UProg) : Prop :=
  ∀ t : Fin u.tabellen.length, tabIdx u.tabellen (tabAt u t).name = .ok t

variable {u : UProg}

/-! ## 1. Indices -/

theorem lowIdx_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {sh : Nat}
    {t : Fin u.tabellen.length} {ix : UIdx} {e : Expr (declOf u) Γ Λ (.index ((declOf u).count t))}
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
      · rename_i m hm
        split at h
        · split at h
          · cases h
          · rename_i v hv
            cases h
            simp only [idxExpr, Gabbro.Body.eval]
            rw [hL p j hj, nthVal_lowVar Γ (sh + j) _ v ρ hv]
            rfl
        · cases h
      · cases h

/-! ## 2. Slot terms: the casts of the lowering are the constructors -/

theorem durchTerm_heq (Γ : Ctx) (Λ : List (Res (declOf u)))
    (num : Nat) (w : Bool) (h : num < u.tabellen.length)
    (fh : FieldHit u ⟨num, h⟩) (v : Var Γ (.ptr num w))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ) :
    HEq (durchTerm u Γ Λ num w h fh v i hL)
      (Expr.durch (D := declOf u) (Expr.var v) ⟨num, h⟩ (tabNr_some u num h) fh.idx i hL) := by
  unfold durchTerm; exact mpr_heq _ _

theorem slotTerm_heq (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabellen.length) (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    HEq (slotTerm u Γ Λ t fh i hL) (Expr.slot (D := declOf u) t fh.idx i hL) := by
  unfold slotTerm; exact mpr_heq _ _

theorem altTerm_heq (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabellen.length) (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    HEq (altTerm u Γ Λ t fh i hL) (Expr.altSlot (D := declOf u) t fh.idx i hL) := by
  unfold altTerm; exact mpr_heq _ _

/-- The Body place of a declared slot holds the G slot. -/
theorem wrel_lies {σ : World (declOf u)} {w : Gabbro.Body.World} (hW : WRel u σ w)
    (c : String) (t : Fin u.tabellen.length) (ht : tabIdx u.tabellen c = .ok t)
    (fld : String) (fh : FieldHit u t) (hf : fieldHit u t fld = .ok fh) (k : Int) :
    w (.slot c k fld) = valOf ((declOf u).typ t fh.idx) (σ.slots t k fh.idx) := by
  apply hW
  simp only [slotWert, ht, hf]

/-- The pointer parameter the lowering resolves names, in `Pflichten.ptrTab`, its table. -/
theorem ptrTab_of (fn : UFn) (hA : ArtStimmt fn) (b : String) (j num : Nat) (w : Bool)
    (hj : paramPos fn.params b = .ok j) (hp : fn.parten[j]? = some (.ptr num w))
    (h : num < u.tabellen.length) :
    ptrTab u fn b = some (tabAt u ⟨num, h⟩).name := by
  obtain ⟨w', hw'⟩ := hA j num w hp
  obtain ⟨τ, hτ⟩ := paramPos_name _ _ _ hj
  rw [hτ] at hw'
  simp only [Option.map_some, Option.some.injEq] at hw'
  subst hw'
  unfold ptrTab
  rw [paramPos_find _ _ _ hj, hτ]
  simp [tabAt, List.getElem?_eq_getElem h]

/-! ## 3. Value sides -/

theorem lowParamSide_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {sh : Nat}
    {p : String} {ls : LowSide u Γ Λ} (h : lowParamSide u Γ Λ fn sh p = .ok ls)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (β : Gabbro.Body.Binding)
    (hL : LRel fn sh ρ β) :
    β p = valOf (.int ls.weit.1 ls.weit.2) (eval σ₀ ls.term σ ρ) := by
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
        some (valOf (.int ls.weit.1 ls.weit.2) (eval σ₀ ls.term σ ρ)) := by
  unfold lowDurch at h
  split at h
  · cases h
  · rename_i j hj
    split at h
    · rename_i num wr hp
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
                cases h
                refine ⟨_, ptrTab_of fn hA b j num wr hj hp hlt, ?_⟩
                simp only [Gabbro.Body.eval]
                rw [lowIdx_sim hi σ₀ σ ρ w β hL]
                simp only
                rw [wrel_lies hW _ ⟨num, hlt⟩ (hT _) fname fh hfh]
                rw [valOf_eval_heq (typAt_of u ⟨num, hlt⟩ fh.idx fh.weit fh.hit).symm _ _
                  (durchTerm_heq Γ Λ num wr hlt fh v i hG) σ₀ σ ρ]
                rfl
              · cases h
      · cases h
    · cases h

theorem lowTabRead_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {sh : Nat}
    {b fname : String} {ix : UIdx} {ls : LowSide u Γ Λ}
    (h : lowTabRead u Γ Λ fn sh b fname ix = .ok ls)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WRel u σ w) (hL : LRel fn sh ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ (.place b (idxExpr ix) fname) =
      some (valOf (.int ls.weit.1 ls.weit.2) (eval σ₀ ls.term σ ρ)) := by
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
          rw [valOf_eval_heq (typAt_of u t fh.idx fh.weit fh.hit).symm _ _
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
      some (valOf (.int ls.weit.1 ls.weit.2) (eval σ₀ ls.term σ ρ)) := by
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
          have hct : tabIdx u.tabellen c = .ok t := by
            split at ht
            · rename_i j hj
              split at ht
              · rename_i num wr hp
                split at ht
                · rename_i hlt
                  cases ht
                  rw [ptrTab_of fn hA b j num wr hj hp hlt] at hc
                  cases hc
                  exact hT _
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
          rw [valOf_eval_heq (typAt_of u t fh.idx fh.weit fh.hit).symm _ _
            (altTerm_heq Γ Λ t fh i hG) σ₀ σ ρ]
          rfl
        · cases h

theorem lowSideVal_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {sd : USide} {ls : LowSide u Γ Λ} {eB : Gabbro.Body.Expr}
    (h : lowSideVal u Γ Λ fn sd = .ok ls) (hb : sideExpr u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WRel u σ w) (hL : LRel fn 0 ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf (.int ls.weit.1 ls.weit.2) (eval σ₀ ls.term σ ρ)) := by
  cases sd with
  | add _ _ | sub _ _ | mul _ _ | conv _ _ _ | band _ _ | bor _ _ | bxor _ _ => simp [ensSide, sideExpr] at hb
  | lit n =>
    simp only [lowSideVal] at h; cases h
    simp only [sideExpr] at hb; cases hb
    rfl
  | param p =>
    simp only [lowSideVal] at h
    simp only [sideExpr] at hb; cases hb
    simp only [Gabbro.Body.eval]
    rw [lowParamSide_sim h σ₀ σ ρ β hL]
  | slot b f ix =>
    simp only [lowSideVal] at h
    obtain ⟨c, hc, hv⟩ := lowDurch_sim h hA hT σ₀ σ ρ w β hW hL
    simp only [sideExpr, slotPlace, hc, Option.map_some] at hb
    cases hb
    exact hv
  | tab b f ix =>
    simp only [lowSideVal] at h
    simp only [sideExpr, slotPlace] at hb
    cases hb
    exact lowTabRead_sim h σ₀ σ ρ w β hW hL
  | alt b f ix => simp only [lowSideVal] at h; cases h
  | erg => simp only [lowSideVal] at h; cases h

/-- A value fitted into a target range (`lowWertAt`) keeps its number. -/
theorem lowWertAt_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {lo hi : Int}
    {sd : USide} {e : Expr (declOf u) Γ Λ (.int lo hi)} {eB : Gabbro.Body.Expr}
    (h : lowWertAt u Γ Λ fn lo hi sd = .ok e) (hb : sideExpr u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WRel u σ w) (hL : LRel fn 0 ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ eB = some (valOf (.int lo hi) (eval σ₀ e σ ρ)) := by
  unfold lowWertAt at h
  split at h
  · cases h
  · rename_i ls hls
    split at h
    · split at h
      · cases h
        rw [lowSideVal_sim hls hb hA hT σ₀ σ ρ w β hW hL]
        rfl
      · cases h
    · cases h

/-! ## 4. `ensures` -/

/-- The accumulator only grows: `old` reads are appended, and `result` once met stays met. -/
def Vor (a b : Acc) : Prop := (∃ l, b.olds = a.olds ++ l) ∧ (a.result = true → b.result = true)

theorem Vor.refl (a : Acc) : Vor a a := ⟨⟨[], by simp⟩, id⟩

theorem Vor.trans {a b c : Acc} (h1 : Vor a b) (h2 : Vor b c) : Vor a c := by
  obtain ⟨⟨l1, h1⟩, r1⟩ := h1
  obtain ⟨⟨l2, h2⟩, r2⟩ := h2
  exact ⟨⟨l1 ++ l2, by rw [h2, h1, List.append_assoc]⟩, fun h => r2 (r1 h)⟩

theorem ensSide_vor {fn : UFn} {a a' : Acc} {sd : USide} {x : Gabbro.Body.Expr}
    (h : ensSide u fn a sd = some (x, a')) : Vor a a' := by
  cases sd with
  | add _ _ | sub _ _ | mul _ _ | conv _ _ _ | band _ _ | bor _ _ | bxor _ _ => simp [ensSide, sideExpr] at h
  | alt b f ix =>
    simp only [ensSide] at h
    cases hp : slotPlace u fn (.alt b f ix) with
    | none => rw [hp] at h; cases h
    | some pl =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨⟨[pl], rfl⟩, id⟩
  | erg =>
    simp only [ensSide, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨⟨[], by simp⟩, fun _ => rfl⟩
  | lit n =>
    simp only [ensSide, sideExpr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact Vor.refl _
  | param p =>
    simp only [ensSide, sideExpr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; exact Vor.refl _
  | slot b f ix =>
    simp only [ensSide, sideExpr] at h
    cases hp : slotPlace u fn (.slot b f ix) with
    | none => rw [hp] at h; cases h
    | some pl =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact Vor.refl _
  | tab b f ix =>
    simp only [ensSide, sideExpr] at h
    cases hp : slotPlace u fn (.tab b f ix) with
    | none => rw [hp] at h; cases h
    | some pl =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact Vor.refl _

theorem ensExpr_vor {fn : UFn} : ∀ (e : UEns) {a a' : Acc} {x : Gabbro.Body.Expr},
    ensExpr u fn a e = some (x, a') → Vor a a'
  | .wahr, a, a', x, h => by
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact Vor.refl _
  | .falsch, a, a', x, h => by
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact Vor.refl _
  | .cmp op l r, a, a', x, h => by
      simp only [ensExpr] at h
      split at h
      · rename_i o le a1 _ hl
        split at h
        · rename_i re a2 hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact (ensSide_vor hl).trans (ensSide_vor hr)
        · cases h
      · cases h
  | .und x y, a, a', z, h => by
      simp only [ensExpr] at h
      split at h
      · rename_i xe a1 hx
        split at h
        · rename_i ye a2 hy
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact (ensExpr_vor x hx).trans (ensExpr_vor y hy)
        · cases h
      · cases h
  | .oder x y, a, a', z, h => by
      simp only [ensExpr] at h
      split at h
      · rename_i xe a1 hx
        split at h
        · rename_i ye a2 hy
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact (ensExpr_vor x hx).trans (ensExpr_vor y hy)
        · cases h
      · cases h
  | .nicht x, a, a', z, h => by
      simp only [ensExpr] at h
      split at h
      · rename_i xe a1 hx
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ensExpr_vor x hx
      · cases h

/-- **The binding an `ensures` clause is evaluated under** (`clauseAux` builds it): the
    parameters as in the entry state, `result` as the answer (the G context's first entry when
    there is a result), and the `i`th `old` name as the value the `i`th entry read has in the
    entry state `s₀`. -/
structure EnsBind {D : Deklaration} {Γ : Ctx} (fn : UFn) (er : Option (Int × Int))
    (ρ : Env D Γ) (s₀ : Gabbro.Body.State) (A : Acc) (β : Gabbro.Body.Binding) : Prop where
  par : LRel fn (if er.isSome then 1 else 0) ρ β
  res : A.result = true → β "result" = nthVal ρ 0
  old : ∀ i (hi : i < A.olds.length), Gabbro.Body.eval s₀ (A.olds[i]) = some (β (oldName i))

theorem lowSideEns_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option (Int × Int)} {sd : USide} {ls : LowSide u Γ Λ} {a a' A : Acc}
    {x : Gabbro.Body.Expr}
    (h : lowSideEns u Γ Λ fn er sd = .ok ls) (hb : ensSide u fn a sd = some (x, a'))
    (hpre : Vor a' A) (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s₀ : Gabbro.Body.State)
    (w : Gabbro.Body.World) (β : Gabbro.Body.Binding)
    (hW₀ : WRel u σ₀ s₀.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local')
    (hW : WRel u σ w) (hB : EnsBind fn er ρ s₀ A β) :
    Gabbro.Body.eval ⟨w, β⟩ x = some (valOf (.int ls.weit.1 ls.weit.2) (eval σ₀ ls.term σ ρ)) := by
  cases sd with
  | add _ _ | sub _ _ | mul _ _ | conv _ _ _ | band _ _ | bor _ _ | bxor _ _ => simp [ensSide, sideExpr] at hb
  | lit n =>
    simp only [lowSideEns] at h; cases h
    simp only [ensSide, sideExpr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, _⟩ := hb
    rfl
  | param p =>
    simp only [lowSideEns] at h
    simp only [ensSide, sideExpr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, _⟩ := hb
    simp only [Gabbro.Body.eval]
    rw [lowParamSide_sim h σ₀ σ ρ β hB.par]
  | slot b f ix =>
    simp only [lowSideEns] at h
    obtain ⟨c, hc, hv⟩ := lowDurch_sim h hA hT σ₀ σ ρ w β hW hB.par
    simp only [ensSide, sideExpr, slotPlace, hc, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, _⟩ := hb
    exact hv
  | tab b f ix =>
    simp only [lowSideEns] at h
    simp only [ensSide, sideExpr, slotPlace, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, _⟩ := hb
    exact lowTabRead_sim h σ₀ σ ρ w β hW hB.par
  | alt b f ix =>
    simp only [lowSideEns] at h
    simp only [ensSide] at hb
    cases hc : ptrTab u fn b with
    | none => simp [slotPlace, hc] at hb
    | some c =>
      simp only [slotPlace, hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      obtain ⟨⟨l, hl⟩, _⟩ := hpre
      have hlen : a.olds.length < A.olds.length := by
        rw [hl]; simp
      have hget : A.olds[a.olds.length] = .place c (idxExpr ix) f := by
        simp only [hl, List.append_assoc]
        simp
      have ho := hB.old a.olds.length hlen
      rw [hget] at ho
      have hv := lowAltRead_sim h hA hT c hc σ₀ σ ρ s₀.world s₀.local' hW₀ hL₀
      simp only [Gabbro.Body.eval]
      cases s₀ with
      | mk w₀ β₀ =>
        rw [hv] at ho
        exact ho.symm
  | erg =>
    simp only [lowSideEns] at h
    split at h
    · rename_i _ lo hi
      split at h
      · cases h
      · rename_i v hv
        cases h
        simp only [ensSide, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        simp only [Gabbro.Body.eval]
        rw [hB.res (hpre.2 rfl), nthVal_lowVar Γ 0 _ v ρ hv]
        rfl
    · cases h

theorem opOf_some {op : String} {o : Gabbro.Body.BinOp} (h : opOf op = some o) :
    (op = "==" ∧ o = .eq) ∨ (op = "<" ∧ o = .lt) ∨ (op = "<=" ∧ o = .le) := by
  unfold opOf at h
  split at h <;> simp_all

/-- **An `ensures` predicate**: its Body term, under the clause binding, is the G truth value. -/
theorem lowEns_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option (Int × Int)} (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s₀ : Gabbro.Body.State)
    (w : Gabbro.Body.World) (β : Gabbro.Body.Binding) (A : Acc)
    (hW₀ : WRel u σ₀ s₀.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local')
    (hW : WRel u σ w) (hB : EnsBind fn er ρ s₀ A β) :
    ∀ (e : UEns) {a a' : Acc} {x : Gabbro.Body.Expr} {g : Expr (declOf u) Γ Λ .bool},
      ensExpr u fn a e = some (x, a') → lowEns u Γ Λ fn er e = .ok g →
      Vor a' A →
      Gabbro.Body.eval ⟨w, β⟩ x = some (.bool (wahr? (eval σ₀ g σ ρ)))
  | .wahr, a, a', x, g, hb, h, _ => by
      simp only [lowEns] at h; cases h
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, _⟩ := hb; rfl
  | .falsch, a, a', x, g, hb, h, _ => by
      simp only [lowEns] at h; cases h
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, _⟩ := hb; rfl
  | .cmp op l r, a, a', x, g, hb, h, hpre => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i o le a1 hop hl
        split at hb
        · rename_i re a2 hr
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [lowEns, lowCmp] at h
          split at h
          · cases h
          · rename_i s1 hs1
            split at h
            · cases h
            · rename_i s2 hs2
              have p1 := (ensSide_vor hr).trans hpre
              have e1 := lowSideEns_sim hs1 hl p1 hA hT σ₀ σ ρ s₀ w β hW₀ hL₀ hW hB
              have e2 := lowSideEns_sim hs2 hr hpre hA hT σ₀ σ ρ s₀ w β hW₀ hL₀ hW hB
              rcases opOf_some hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · cases h
                simp only [Gabbro.Body.eval, e1, e2, valOf_int, Gabbro.Body.binop]
                simp [Grammatik.eval, wahr?]
              · cases h
                simp only [Gabbro.Body.eval, e1, e2, valOf_int, Gabbro.Body.binop]
                simp [Grammatik.eval, wahr?]
              · cases h
                simp only [Gabbro.Body.eval, e1, e2, valOf_int, Gabbro.Body.binop]
                simp [Grammatik.eval, wahr?]
        · cases hb
      · cases hb
  | .und x y, a, a', z, g, hb, h, hpre => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i xe a1 hx
        split at hb
        · rename_i ye a2 hy
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [lowEns] at h
          split at h
          · cases h
          · rename_i gx hgx
            split at h
            · cases h
            · rename_i gy hgy
              cases h
              have p1 := (ensExpr_vor y hy).trans hpre
              have e1 := lowEns_sim hA hT σ₀ σ ρ s₀ w β A hW₀ hL₀ hW hB x hx hgx p1
              have e2 := lowEns_sim hA hT σ₀ σ ρ s₀ w β A hW₀ hL₀ hW hB y hy hgy hpre
              simp only [Gabbro.Body.eval, e1, e2, Gabbro.Body.andBool_some]
              rfl
        · cases hb
      · cases hb
  | .oder x y, a, a', z, g, hb, h, hpre => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i xe a1 hx
        split at hb
        · rename_i ye a2 hy
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [lowEns] at h
          split at h
          · cases h
          · rename_i gx hgx
            split at h
            · cases h
            · rename_i gy hgy
              cases h
              have p1 := (ensExpr_vor y hy).trans hpre
              have e1 := lowEns_sim hA hT σ₀ σ ρ s₀ w β A hW₀ hL₀ hW hB x hx hgx p1
              have e2 := lowEns_sim hA hT σ₀ σ ρ s₀ w β A hW₀ hL₀ hW hB y hy hgy hpre
              simp only [Gabbro.Body.eval, e1, e2, Gabbro.Body.orBool_some]
              rfl
        · cases hb
      · cases hb
  | .nicht x, a, a', z, g, hb, h, hpre => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i xe a1 hx
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        simp only [lowEns] at h
        split at h
        · cases h
        · rename_i gx hgx
          cases h
          have e1 := lowEns_sim hA hT σ₀ σ ρ s₀ w β A hW₀ hL₀ hW hB x hx hgx hpre
          simp only [Gabbro.Body.eval, e1, Gabbro.Body.unop]
          rfl
      · cases hb

/-- What a lowered side adds to the accumulator: `old` reads that evaluate in the entry state,
    and `result` only where the function has one. -/
def Zuwachs (s₀ : Gabbro.Body.State) (er : Option (Int × Int)) (a a' : Acc) : Prop :=
  (∀ o ∈ a'.olds, o ∈ a.olds ∨ ∃ v, Gabbro.Body.eval s₀ o = some v) ∧
  (a'.result = true → a.result = true ∨ er.isSome = true)

theorem Zuwachs.refl (s₀ : Gabbro.Body.State) (er : Option (Int × Int)) (a : Acc) :
    Zuwachs s₀ er a a := ⟨fun _ h => .inl h, .inl⟩

theorem Zuwachs.trans {s₀ : Gabbro.Body.State} {er : Option (Int × Int)} {a b c : Acc}
    (_hv : Vor a b) (h1 : Zuwachs s₀ er a b) (h2 : Zuwachs s₀ er b c) : Zuwachs s₀ er a c := by
  refine ⟨fun o ho => ?_, fun h => ?_⟩
  · rcases h2.1 o ho with hb | hv'
    · exact h1.1 o hb
    · exact .inr hv'
  · rcases h2.2 h with hb | he
    · exact h1.2 hb
    · exact .inr he

theorem ensSide_zuwachs {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option (Int × Int)} {sd : USide} {ls : LowSide u Γ Λ} {a a' : Acc}
    {x : Gabbro.Body.Expr}
    (h : lowSideEns u Γ Λ fn er sd = .ok ls) (hb : ensSide u fn a sd = some (x, a'))
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s₀ : Gabbro.Body.State)
    (hW₀ : WRel u σ₀ s₀.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local') :
    Zuwachs s₀ er a a' := by
  cases sd with
  | add _ _ | sub _ _ | mul _ _ | conv _ _ _ | band _ _ | bor _ _ | bxor _ _ => simp [ensSide, sideExpr] at hb
  | alt b f ix =>
    simp only [lowSideEns] at h
    simp only [ensSide] at hb
    cases hc : ptrTab u fn b with
    | none => simp [slotPlace, hc] at hb
    | some c =>
      simp only [slotPlace, hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨fun o ho => ?_, fun hr => .inl hr⟩
      simp only [List.mem_append, List.mem_singleton] at ho
      rcases ho with ho | rfl
      · exact .inl ho
      · have hv := lowAltRead_sim h hA hT c hc σ₀ σ ρ s₀.world s₀.local' hW₀ hL₀
        cases s₀
        exact .inr ⟨_, hv⟩
  | erg =>
    simp only [lowSideEns] at h
    split at h
    · rename_i _ lo hi
      simp only [ensSide, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨fun o ho => .inl ho, fun _ => .inr rfl⟩
    · cases h
  | lit n =>
    simp only [ensSide, sideExpr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨_, rfl⟩ := hb; exact Zuwachs.refl _ _ _
  | param p =>
    simp only [ensSide, sideExpr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨_, rfl⟩ := hb; exact Zuwachs.refl _ _ _
  | slot b f ix =>
    simp only [ensSide, sideExpr] at hb
    cases hp : slotPlace u fn (.slot b f ix) with
    | none => rw [hp] at hb; cases hb
    | some pl =>
      rw [hp] at hb
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨_, rfl⟩ := hb; exact Zuwachs.refl _ _ _
  | tab b f ix =>
    simp only [ensSide, sideExpr] at hb
    cases hp : slotPlace u fn (.tab b f ix) with
    | none => rw [hp] at hb; cases hb
    | some pl =>
      rw [hp] at hb
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨_, rfl⟩ := hb; exact Zuwachs.refl _ _ _

theorem ensExpr_zuwachs {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option (Int × Int)} (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s₀ : Gabbro.Body.State)
    (hW₀ : WRel u σ₀ s₀.world) (hL₀ : LRel fn (if er.isSome then 1 else 0) ρ s₀.local') :
    ∀ (e : UEns) {a a' : Acc} {x : Gabbro.Body.Expr} {g : Expr (declOf u) Γ Λ .bool},
      ensExpr u fn a e = some (x, a') → lowEns u Γ Λ fn er e = .ok g → Zuwachs s₀ er a a'
  | .wahr, a, a', x, g, hb, h => by
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨_, rfl⟩ := hb; exact Zuwachs.refl _ _ _
  | .falsch, a, a', x, g, hb, h => by
      simp only [ensExpr, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨_, rfl⟩ := hb; exact Zuwachs.refl _ _ _
  | .cmp op l r, a, a', x, g, hb, h => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i o le a1 hop hl
        split at hb
        · rename_i re a2 hr
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [lowEns, lowCmp] at h
          split at h
          · cases h
          · rename_i s1 hs1
            split at h
            · cases h
            · rename_i s2 hs2
              exact Zuwachs.trans (ensSide_vor hl)
                (ensSide_zuwachs hs1 hl hA hT σ₀ σ ρ s₀ hW₀ hL₀)
                (ensSide_zuwachs hs2 hr hA hT σ₀ σ ρ s₀ hW₀ hL₀)
        · cases hb
      · cases hb
  | .und x y, a, a', z, g, hb, h => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i xe a1 hx
        split at hb
        · rename_i ye a2 hy
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [lowEns] at h
          split at h
          · cases h
          · rename_i gx hgx
            split at h
            · cases h
            · rename_i gy hgy
              exact Zuwachs.trans (ensExpr_vor x hx)
                (ensExpr_zuwachs hA hT σ₀ σ ρ s₀ hW₀ hL₀ x hx hgx)
                (ensExpr_zuwachs hA hT σ₀ σ ρ s₀ hW₀ hL₀ y hy hgy)
        · cases hb
      · cases hb
  | .oder x y, a, a', z, g, hb, h => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i xe a1 hx
        split at hb
        · rename_i ye a2 hy
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          simp only [lowEns] at h
          split at h
          · cases h
          · rename_i gx hgx
            split at h
            · cases h
            · rename_i gy hgy
              exact Zuwachs.trans (ensExpr_vor x hx)
                (ensExpr_zuwachs hA hT σ₀ σ ρ s₀ hW₀ hL₀ x hx hgx)
                (ensExpr_zuwachs hA hT σ₀ σ ρ s₀ hW₀ hL₀ y hy hgy)
        · cases hb
      · cases hb
  | .nicht x, a, a', z, g, hb, h => by
      simp only [ensExpr] at hb
      split at hb
      · rename_i xe a1 hx
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        simp only [lowEns] at h
        split at h
        · cases h
        · rename_i gx hgx
          exact ensExpr_zuwachs hA hT σ₀ σ ρ s₀ hW₀ hL₀ x hx hgx
      · cases hb

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
