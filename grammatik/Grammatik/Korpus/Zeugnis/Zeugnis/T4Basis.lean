/- Part 4 of 4 of `Zeugnis` (split by instrumente/teile/lean-teilen.py; the umbrella `Zeugnis.lean` imports all parts). -/
module
public import Grammatik.Korpus.Zeugnis.Zeugnis.T3
@[expose] public section


namespace Gabbro.Grammatik

/-- Float-read soundness: a float table hit elaborates to a `.fl` expression
    (mirror of the `var`/`glob`/`slot` cases of `zeugnis_sound`). -/
theorem certFl_sound {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (a : CertFl D) (lo hi : Int × Int) (h : certFlTyp D Γ Λ a = some (lo, hi)) :
    ∃ _ : Expr D Γ Λ (.fl lo hi), True := by
  cases a with
  | varFl k =>
    simp only [certFlTyp] at h
    obtain ⟨x, _⟩ := ctxFlTyp_var Γ k _ _ h
    exact ⟨Expr.var x, trivial⟩
  | globFl g =>
    simp only [certFlTyp] at h
    cases ht : flVonTyp (D.gtyp g) with
    | none => simp only [ht, reduceCtorEq] at h
    | some q =>
      obtain ⟨lo', hi'⟩ := q
      simp only [ht] at h
      by_cases hc : gdarf D g Λ
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have heq := flVonTyp_eq ht
        exact ⟨heq ▸ Expr.glob g hc, trivial⟩
      · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  | slotFl t f i =>
    simp only [certFlTyp] at h
    cases ha : certRange D Γ Λ i with
    | none =>
      cases ht : flVonTyp (D.typ t f) with
      | none => simp only [ha, ht, reduceCtorEq] at h
      | some _ => simp only [ha, ht, reduceCtorEq] at h
    | some p =>
      obtain ⟨l, h'⟩ := p
      cases ht : flVonTyp (D.typ t f) with
      | none => simp only [ha, ht, reduceCtorEq] at h
      | some q =>
        obtain ⟨lo', hi'⟩ := q
        simp only [ha, ht] at h
        by_cases hc : l = 0 ∧ h' = D.count t - 1 ∧ darf D t Λ
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ei, _⟩ := zeugnis_sound i _ _ ha
          have heq := flVonTyp_eq ht
          obtain ⟨hc1, hc2, hc3⟩ := hc
          subst hc1
          subst hc2
          exact ⟨heq ▸ Expr.slot t f ei hc3, trivial⟩
        · simp only [hc, ↓reduceIte, reduceCtorEq] at h

/-- The booked remainder of CUT-3, named as data: the quantifier body. The
    certificate carries the guard only (`darf` -- the bound variable is the
    generated index, named by the table, not the print), so the body, an
    `Expr` over the extended context, has no print to elaborate from. Every
    other arm needs nothing (`Unit`). -/
def Cut3Body (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) : CertCut3 D → Type
  | .forallSlots t => Expr D (.index (D.count t) :: Γ) Λ .bool
  | .existsSlots t => Expr D (.index (D.count t) :: Γ) Λ .bool
  | _ => Unit

/-- CUT-3 soundness: a valid CUT-3 print elaborates to the corresponding
    `Expr` -- float comparisons to `fllt`/`flle` (via `certFl_sound`),
    option prints to `none`/`some`/`istSome`, sum prints to `fall`, grounds
    to `grund`, `reaches` to `reaches` (via `zeugnis_sound` for the endpoint
    indices), and quantifiers to `forallSlots`/`existsSlots` behind the
    supplied body. The `istSome` scrutinee must INTRODUCE the option
    (`certCut3IsOpt` says so); any other scrutinee shape contradicts
    validity, it is not elaborated. -/
theorem cut3_sound {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (c : CertCut3 D) (body : Cut3Body D Γ Λ c) (h : certCut3Ok D Γ Λ c) :
    ∃ τ, ∃ _ : Expr D Γ Λ τ, True := by
  cases c with
  | fllt a b =>
    simp only [certCut3Ok] at h
    cases ha : certFlTyp D Γ Λ a with
    | none => exact absurd ha h.1
    | some _ =>
      cases hb : certFlTyp D Γ Λ b with
      | none => exact absurd hb h.2
      | some _ =>
        obtain ⟨ea, _⟩ := certFl_sound a _ _ ha
        obtain ⟨eb, _⟩ := certFl_sound b _ _ hb
        exact ⟨.bool, Expr.fllt ea eb, trivial⟩
  | flle a b =>
    simp only [certCut3Ok] at h
    cases ha : certFlTyp D Γ Λ a with
    | none => exact absurd ha h.1
    | some _ =>
      cases hb : certFlTyp D Γ Λ b with
      | none => exact absurd hb h.2
      | some _ =>
        obtain ⟨ea, _⟩ := certFl_sound a _ _ ha
        obtain ⟨eb, _⟩ := certFl_sound b _ _ hb
        exact ⟨.bool, Expr.flle ea eb, trivial⟩
  | none n =>
    exact ⟨.opt n, Expr.none n, trivial⟩
  | some e n =>
    simp only [certCut3Ok] at h
    obtain ⟨ee, _⟩ := zeugnis_sound e 0 (n - 1) h
    exact ⟨.opt n, Expr.some ee, trivial⟩
  | istSome o n =>
    simp only [certCut3Ok] at h
    obtain ⟨ho, hi⟩ := h
    cases o with
    | none m =>
      simp only [certCut3IsOpt] at hi
      have hrfl : m = n := of_decide_eq_true hi
      subst hrfl
      exact ⟨.bool, Expr.istSome (Expr.none m), trivial⟩
    | some e m =>
      simp only [certCut3IsOpt] at hi
      have hrfl : m = n := of_decide_eq_true hi
      subst hrfl
      obtain ⟨ee, _⟩ := zeugnis_sound e 0 (m - 1) ho
      exact ⟨.bool, Expr.istSome (Expr.some ee), trivial⟩
    | fllt _ _ => simp only [certCut3IsOpt, Bool.false_eq_true] at hi
    | flle _ _ => simp only [certCut3IsOpt, Bool.false_eq_true] at hi
    | istSome _ _ => simp only [certCut3IsOpt, Bool.false_eq_true] at hi
    | case _ _ _ => simp only [certCut3IsOpt, Bool.false_eq_true] at hi
    | why _ _ => simp only [certCut3IsOpt, Bool.false_eq_true] at hi
    | forallSlots _ => simp only [certCut3IsOpt, Bool.false_eq_true] at hi
    | existsSlots _ => simp only [certCut3IsOpt, Bool.false_eq_true] at hi
    | reaches _ _ _ _ => simp only [certCut3IsOpt, Bool.false_eq_true] at hi
  | case cs i p =>
    simp only [certCut3Ok] at h
    obtain ⟨hi, hp⟩ := h
    cases hq : cs[i]? with
    | none =>
      have hle : cs.length ≤ i := (List.getElem?_eq_none_iff).mp hq
      omega
    | some slot =>
      rw [hq] at hp
      obtain ⟨h', hget⟩ := (List.getElem?_eq_some_iff).mp hq
      have hget' : cs.get ⟨i, hi⟩ = slot := by
        rw [List.get_eq_getElem]
        exact hget
      cases slot with
      | none =>
        cases p with
        | none =>
          simp only [certCut3PayloadOk] at hp
          exact ⟨.sum cs, Expr.case cs ⟨i, hi⟩ (hget'.symm ▸ NutzlastExpr.empty),
            trivial⟩
        | some _ =>
          simp only [certCut3PayloadOk, Bool.false_eq_true] at hp
      | some q =>
        cases q with
        | int lo hi2 =>
          cases p with
          | none =>
            simp only [certCut3PayloadOk, Bool.false_eq_true] at hp
          | some e =>
            simp only [certCut3PayloadOk] at hp
            have he : certRange D Γ Λ e = some (lo, hi2) := of_decide_eq_true hp
            obtain ⟨ee, _⟩ := zeugnis_sound e lo hi2 he
            exact ⟨.sum cs, Expr.case cs ⟨i, hi⟩ (hget'.symm ▸ NutzlastExpr.val ee),
              trivial⟩
        | bool | opt _ | sum _ | why _ | never | fl _ _ | fnptr _ | ptr _ | ref _ | arr _ _ | str _ | prod _ _ =>
          cases p <;> simp only [certCut3PayloadOk, Bool.false_eq_true] at hp
  | why n r =>
    simp only [certCut3Ok] at h
    exact ⟨.why n, Expr.why n ⟨r, h⟩, trivial⟩
  | forallSlots t =>
    simp only [certCut3Ok] at h
    exact ⟨.bool, Expr.forallSlots t body h, trivial⟩
  | existsSlots t =>
    simp only [certCut3Ok] at h
    exact ⟨.bool, Expr.existsSlots t body h, trivial⟩
  | reaches t f a b =>
    simp only [certCut3Ok] at h
    obtain ⟨hf, har, hbr, hL⟩ := h
    obtain ⟨ea, _⟩ := zeugnis_sound a 0 (D.count t - 1) har
    obtain ⟨eb, _⟩ := zeugnis_sound b 0 (D.count t - 1) hbr
    exact ⟨.bool, Expr.reaches t f hf ea eb hL, trivial⟩

/-! ### CUT-3 soundness probes: options, sums, grounds, quantifier guards -/

/-- The float helpers compute on closed types (no world needed for the
    lookup itself). -/
example : flVonTyp (.fl (0, 1) (2, 3)) = some ((0, 1), (2, 3)) := by rfl

/-- The float context lookup hits at index `0`. -/
example : ctxFlTyp [.fl (0, 1) (2, 3)] 0 = some ((0, 1), (2, 3)) := by rfl

/-- `none 5` elaborates to `Expr.none`. -/
example : ∃ τ, ∃ _ : Expr TestD [] [] τ, True :=
  cut3_sound (.none 5) () trivial

/-- `some 0` at bound `1`: the index shape `0 .. 0` recomputes. -/
example : ∃ τ, ∃ _ : Expr TestD [] [] τ, True :=
  cut3_sound (.some (.lit 0) 1) () (by decide)

/-- `istSome` over an introduced option at the same bound. -/
example : ∃ τ, ∃ _ : Expr TestD [] [] τ, True :=
  cut3_sound (.istSome (.some (.lit 0) 1) 1) () (by decide)

/-- FORGED bound: `istSome` over `some 0 @ 1`, claimed at `2` -- the bound
    check fails, so the print is provably not valid. -/
example : ¬ certCut3Ok TestD [] [] (.istSome (.some (.lit 0) 1) 2) := by decide

/-- NESTED `istSome` under `istSome` is correctly rejected -- the scrutinee
    must introduce the option, and `Bool` has no bound. -/
example : ¬ certCut3Ok TestD [] []
    (.istSome (.istSome (.some (.lit 0) 1) 1) 1) := by decide

/-- The `zahl` case: `fall` at index `0` with a payload that recomputes the
    cased range. -/
example : ∃ τ, ∃ _ : Expr TestD [] [] τ, True :=
  cut3_sound (.case [some (.int 0 0)] 0 (some (.lit 0))) () (by decide)

/-- The caseless arm: `fall` at index `0` with no payload. -/
example : ∃ τ, ∃ _ : Expr TestD [] [] τ, True :=
  cut3_sound (.case [none] 0 none) () (by decide)

/-- FORGED payload: the `zahl` arm carries `1`, cased at `(0, 0)`. -/
example : ¬ certCut3Ok TestD [] []
    (.case [some (.int 0 0)] 0 (some (.lit 1))) := by decide

/-- `grund 1 of 2` elaborates to `Expr.grund`. -/
example : ∃ τ, ∃ _ : Expr TestD [] [] τ, True :=
  cut3_sound (.why 2 1) () (by decide)

/-- The quantifier guard, then `return`: `forallSlots` over the guarded
    table elaborates behind the supplied body. -/
example : ∃ τ, ∃ _ : Expr TestD [] [Res.held ()] τ, True :=
  cut3_sound (.forallSlots ()) Expr.tru (by decide)

/-- Same guard, existential half. -/
example : ∃ τ, ∃ _ : Expr TestD [] [Res.held ()] τ, True :=
  cut3_sound (.existsSlots ()) Expr.tru (by decide)

/-- FORGED payload: `some 1` at bound `1` claims the index shape `0 .. 0`,
    but the payload recomputes `(1, 1)` -- provably not valid. -/
example : ¬ certCut3Ok TestD [] [] (.some (.lit 1) 1) := by decide

/-- FORGED ground: case `2` of `2` reasons is out of range (`r < n` fails). -/
example : ¬ certCut3Ok TestD [] [] (.why 2 2) := by decide

/-- FORGED `reaches`: both endpoint indices recompute `(0, 10)`, but the
    field carries `.int 0 10`, not an option into self -- no certificate. -/
example : ¬ certCut3Ok TestD [] []
    (.reaches () () (.wide 0 10 (.lit 3)) (.wide 0 10 (.lit 4))) := by decide +kernel


end Gabbro.Grammatik
