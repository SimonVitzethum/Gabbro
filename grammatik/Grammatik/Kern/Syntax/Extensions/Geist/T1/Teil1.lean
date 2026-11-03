module

public import Grammatik.Kern.Syntax.Extensions.Geist.T1.Teil1Basis

@[expose] public section

namespace Gabbro.Grammatik.Geist
variable {D : Deklaration} {V : Vertrag D}

set_option linter.unusedSectionVars false in
/-! ## Soundness: an accepted body reads no ghost.

    The bridge between the `Bool` decision and the `Prop` footprint claim.
    The decision and the `Extraktion` footprint projections are defined by
    the same per-constructor lists, so each `g001* = true` case discharges
    through `orteOk_korrekt` (via `nge_of_eq_false`) on expression positions
    and the matching sibling theorem on sub-bodies. The five soundness
    theorems form one `mutual` block: each calls its siblings directly, so
    no hypothesis threading is needed.

    Proof shape (measured in this file): splitting `cases` on the body while
    the goal still mentions the `Bool` decision applied to the outer body
    fails, so each proof first does `revert h ho`, then `cases`, then
    `intro`s per arm: the arms take `h` as the same-shape equation by
    definitional unfolding (`have h0 := h`, never `simpa`) and transport
    `ho` with `simpa [Extraktion.*Orte]` into a disjunction. Conjunctions
    split with `Bool.and_eq_true_iff.mp` (never `simp only
    [Bool.and_eq_true]`, which leaves `decide (_ = true)` wrappers this
    toolchain does not strip). -/

theorem g001Stmt_korrekt_assignSlot {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t)
    (f)
    (i)
    (e)
    (hw)
    (hL)
    (zr_h : g001Stmt (.assignSlot t f i e hw hL : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.assignSlot t f i e hw hL : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h' : orteOk (D := D) (i.orte ++ e.orte) = true := by simpa [g001Stmt] using h
  have ho' : o ∈ i.orte ++ e.orte := by simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h' o ho')

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_ite {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (c)
    (t)
    (e)
    (zr_h : g001Stmt (.ite c t e : Stmt D V l Γ Λ Λ') = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.ite c t e : Stmt D V l Γ Λ Λ'))
    (ih_g001_korrekt_t : ∀ (h : g001 t = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte t), ¬ istGeist (D := D) o)
    (ih_g001_korrekt_e : ∀ (h : g001 e = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.blockOrte e), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) c.orte && g001 t && g001 e) = true := h
  have ho' : o ∈ c.orte ∨ o ∈ Extraktion.blockOrte t ∨ o ∈ Extraktion.blockOrte e := by
    simpa [Extraktion.stmtOrte] using ho
  have h1 : ((orteOk (D := D) c.orte && g001 t) = true) ∧ ((g001 e) = true) :=
    Bool.and_eq_true_iff.mp h0
  have h2 : ((orteOk (D := D) c.orte) = true) ∧ ((g001 t) = true) :=
    Bool.and_eq_true_iff.mp h1.1
  rcases ho' with ho' | ho' | ho'
  · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
  · exact ih_g001_korrekt_t h2.2 o ho'
  · exact ih_g001_korrekt_e h1.2 o ho'

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_assignThruOwn {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_n}
    (p)
    (t)
    (ht)
    (f)
    (i)
    (e)
    (m)
    (s)
    (ho)
    (he)
    (hg)
    (hw)
    (hL)
    (zr_h : g001Stmt (.assignThruOwn (n := zi_n) (read := zi_read) (space := zi_space) (o := zi_eig) p t ht f i e m s ho he hg hw hL : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.assignThruOwn (n := zi_n) (read := zi_read) (space := zi_space) (o := zi_eig) p t ht f i e m s ho he hg hw hL : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) (p.orte ++ i.orte ++ e.orte)) = true := h
  have ho' : o ∈ p.orte ++ i.orte ++ e.orte := by
    simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_assignSlotRef {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_n}
    (r)
    (t)
    (ht)
    (ho)
    (f)
    (e)
    (hw)
    (hL)
    (zr_h : g001Stmt (.assignSlotRef (n := zi_n) r t ht ho f e hw hL : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.assignSlotRef (n := zi_n) r t ht ho f e hw hL : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) (r.orte ++ e.orte)) = true := h
  have ho' : o ∈ r.orte ++ e.orte := by
    simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_assignGlob {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g)
    (e)
    (hw)
    (hL)
    (zr_h : g001Stmt (.assignGlob g e hw hL : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.assignGlob g e hw hL : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte) = true := h
  have ho' : o ∈ e.orte := by
    simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_putBytes {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (t)
    (f)
    (hf)
    (n)
    (i)
    (hlo)
    (hhi)
    (e)
    (hw)
    (hL)
    (zr_h : g001Stmt (.putBytes (lo := zi_lo) (hi := zi_hi) t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.putBytes (lo := zi_lo) (hi := zi_hi) t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) (i.orte ++ e.orte)) = true := h
  have ho' : o ∈ i.orte ++ e.orte := by
    simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_assignVar {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_τ}
    (x)
    (e)
    (zr_h : g001Stmt (.assignVar (τ := zi_τ) x e : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.assignVar (τ := zi_τ) x e : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte) = true := h
  have ho' : o ∈ e.orte := by
    simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_shift {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (t)
    (f)
    (hτ)
    (i)
    (von)
    (nach)
    (hn)
    (he)
    (hw)
    (hL)
    (zr_h : g001Stmt (.shift (lo := zi_lo) (hi := zi_hi) t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.shift (lo := zi_lo) (hi := zi_hi) t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) i.orte) = true := h
  have ho' : o ∈ i.orte := by
    simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_call {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (f)
    (args)
    (hp)
    (hr)
    (zr_h : g001Stmt (.call f args hp hr : Stmt D V l Γ Λ (Gabbro.Grammatik.nach D f Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.call f args hp hr : Stmt D V l Γ Λ (Gabbro.Grammatik.nach D f Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) args.orte) = true := h
  have ho' : o ∈ args.orte := by
    simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_callInd {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (p)
    (args)
    (hp)
    (hr)
    (zr_h : g001Stmt (.callInd p args hp hr : Stmt D V l Γ Λ (Gabbro.Grammatik.nachSig D (D.sigNr n) Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.callInd p args hp hr : Stmt D V l Γ Λ (Gabbro.Grammatik.nachSig D (D.sigNr n) Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) (p.orte ++ args.orte)) = true := h
  have ho' : o ∈ p.orte ++ args.orte := by
    simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_callIndElse {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p)
    (args)
    (he : (D.sigNr n).erg = some τ)
    (hp)
    (hr)
    (err)
    (zr_h : g001Stmt (.callIndElse p args he hp hr err : Stmt D V l Γ Λ (Gabbro.Grammatik.nachSig D (D.sigNr n) Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.callIndElse p args he hp hr err : Stmt D V l Γ Λ (Gabbro.Grammatik.nachSig D (D.sigNr n) Λ)))
    (ih_g001End_korrekt_err : ∀ (h : g001End err = true), ∀ (o : D.Tab ⊕ D.Glob), ∀ (ho : o ∈ Extraktion.endblockOrte err), ¬ istGeist (D := D) o)
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) (p.orte ++ args.orte) && g001End err) = true := h
  have ho' : o ∈ p.orte ∨ o ∈ args.orte ∨ o ∈ Extraktion.endblockOrte err := by
    simpa [Extraktion.stmtOrte] using ho
  have h1 : ((orteOk (D := D) (p.orte ++ args.orte)) = true) ∧ ((g001End err) = true) :=
    Bool.and_eq_true_iff.mp h0
  have ho2 : (o ∈ p.orte ∨ o ∈ args.orte) ∨ o ∈ Extraktion.endblockOrte err := by
    rcases ho' with ho' | ho' | ho'
    · exact Or.inl (Or.inl ho')
    · exact Or.inl (Or.inr ho')
    · exact Or.inr ho'
  rcases ho2 with ho2 | ho2
  · have ho3 : o ∈ p.orte ++ args.orte := by
      simpa [List.mem_append] using ho2
    exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho3)
  · exact ih_g001End_korrekt_err h1.2 o ho2

set_option linter.unusedSectionVars false in
theorem g001Stmt_korrekt_regWrite {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (hk)
    (e)
    (zr_h : g001Stmt (.regWrite r hk e : Stmt D V l Γ Λ (Λ)) = true)
    (o : D.Tab ⊕ D.Glob)
    (zr_ho : o ∈ Extraktion.stmtOrte (.regWrite r hk e : Stmt D V l Γ Λ (Λ)))
    : ¬ istGeist (D := D) o :=
  by
  revert zr_h zr_ho
  intro h ho
  have h0 : (orteOk (D := D) e.orte) = true := h
  have ho' : o ∈ e.orte := by
    simpa [Extraktion.stmtOrte] using ho
  exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')

end Gabbro.Grammatik.Geist
