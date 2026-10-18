/- Part 4 of 4 of `Zeugnis` (split by instrumente/teile/lean-teilen.py; the umbrella `Zeugnis.lean` imports all parts). -/
import Grammatik.Korpus.Zeugnis.Zeugnis.T3

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
    | none => simp [ht] at h
    | some q =>
      obtain ⟨lo', hi'⟩ := q
      simp only [ht] at h
      by_cases hc : gdarf D g Λ
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have heq := flVonTyp_eq ht
        exact ⟨heq ▸ Expr.glob g hc, trivial⟩
      · simp [hc] at h
  | slotFl t f i =>
    simp only [certFlTyp] at h
    cases ha : certRange D Γ Λ i with
    | none =>
      cases ht : flVonTyp (D.typ t f) with
      | none => simp [ha, ht] at h
      | some _ => simp [ha, ht] at h
    | some p =>
      obtain ⟨l, h'⟩ := p
      cases ht : flVonTyp (D.typ t f) with
      | none => simp [ha, ht] at h
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
        · simp [hc] at h

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
    | fllt _ _ => simp [certCut3IsOpt] at hi
    | flle _ _ => simp [certCut3IsOpt] at hi
    | istSome _ _ => simp [certCut3IsOpt] at hi
    | case _ _ _ => simp [certCut3IsOpt] at hi
    | why _ _ => simp [certCut3IsOpt] at hi
    | forallSlots _ => simp [certCut3IsOpt] at hi
    | existsSlots _ => simp [certCut3IsOpt] at hi
    | reaches _ _ _ _ => simp [certCut3IsOpt] at hi
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
          simp [certCut3PayloadOk] at hp
      | some q =>
        obtain ⟨lo, hi2⟩ := q
        cases p with
        | none =>
          simp [certCut3PayloadOk] at hp
        | some e =>
          simp only [certCut3PayloadOk] at hp
          have he : certRange D Γ Λ e = some (lo, hi2) := of_decide_eq_true hp
          obtain ⟨ee, _⟩ := zeugnis_sound e lo hi2 he
          exact ⟨.sum cs, Expr.case cs ⟨i, hi⟩ (hget'.symm ▸ NutzlastExpr.num ee),
            trivial⟩
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
example : flVonTyp (.fl (0, 1) (2, 3)) = some ((0, 1), (2, 3)) := rfl

/-- The float context lookup hits at index `0`. -/
example : ctxFlTyp [.fl (0, 1) (2, 3)] 0 = some ((0, 1), (2, 3)) := rfl

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
  cut3_sound (.case [some (0, 0)] 0 (some (.lit 0))) () (by decide)

/-- The caseless arm: `fall` at index `0` with no payload. -/
example : ∃ τ, ∃ _ : Expr TestD [] [] τ, True :=
  cut3_sound (.case [none] 0 none) () (by decide)

/-- FORGED payload: the `zahl` arm carries `1`, cased at `(0, 0)`. -/
example : ¬ certCut3Ok TestD [] []
    (.case [some (0, 0)] 0 (some (.lit 1))) := by decide

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
    (.reaches () () (.wide 0 10 (.lit 3)) (.wide 0 10 (.lit 4))) := by decide

/-! ## CUT-4 remainder soundness: `durch`, `ptrOf`, `fnref`

    Proved as `cut4_sound` below. `ptrOf`/`fnref` elaborate directly from
    the recomputed equations; `durch` takes the pointer it names as an
    explicit hypothesis (`Cut4Ptr`) -- the pointer TERM has no print in
    `CertCut4`, so its elaboration is the remaining booked piece, named
    here as data. -/

/-- The booked remainder of CUT-4, named as data: the pointer behind
    `durch`. The arm checks the capability the pointer NAMES (table number,
    index shape, guard); the pointer itself travels as proof. Every other
    arm needs nothing (`Unit`). -/
def Cut4Ptr (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) : CertCut4 D → Type
  | .thru _ _ n _ => Σ rw : Bool, Expr D Γ Λ (.ptr n rw)
  | _ => Unit

/-- CUT-4 remainder soundness: a valid remainder print elaborates to the
    corresponding `Expr` -- `ptrOf`/`fnref` from the recomputed equations,
    `durch` from the named pointer plus the recomputed index shape and
    guard (via `zeugnis_sound`). -/
theorem cut4_sound {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (c : CertCut4 D) (s : Cut4Ptr D Γ Λ c) (h : certCut4Ok D Γ Λ c) :
    ∃ τ, ∃ _ : Expr D Γ Λ τ, True := by
  cases c with
  | ptrOf t n rw =>
    simp only [certCut4Ok] at h
    exact ⟨.ptr n rw, Expr.ptrOf t n h rw, trivial⟩
  | fnref f n =>
    simp only [certCut4Ok] at h
    exact ⟨.fnptr n, Expr.fnref f n h, trivial⟩
  | thru t f n i =>
    simp only [certCut4Ok] at h
    obtain ⟨ht, hrng, hL⟩ := h
    obtain ⟨rw, p⟩ := s
    obtain ⟨ei, _⟩ := zeugnis_sound i 0 (D.count t - 1) hrng
    exact ⟨D.typ t f, Expr.thru p t ht f ei hL, trivial⟩

/-! ### CUT-4 remainder soundness probes -/

/-- `ptrOf` the table at number `0` elaborates to the pointer capability. -/
example : ∃ τ, ∃ _ : Expr TestD [] [] τ, True :=
  cut4_sound (.ptrOf () 0 true) () (by decide)

/-- `fnref` the nullary function at signature `0`. -/
example : ∃ τ, ∃ _ : Expr TestD [] [] τ, True :=
  cut4_sound (.fnref false 0) () (by decide)

/-- `durch` the named pointer: table number, generated index shape, and
    guard recompute; the pointer travels as proof. -/
example : ∃ τ, ∃ _ : Expr TestD [] [Res.held ()] τ, True :=
  cut4_sound (.thru () () 0 (.wide 0 10 (.lit 3)))
    ⟨true, Expr.ptrOf () 0 rfl true⟩ (by decide)

/-- FORGED signature: the nullary function claimed at signature `1` -- the
    signature equation fails, so the print is provably not valid. -/
example : ¬ certCut4Ok TestD [] [] (.fnref false 1) := by decide

/-- FORGED index: a bare `3` is not of index type `0 .. 10` -- without the
    widening the `durch` has no validity. -/
example : ¬ certCut4Ok TestD [] [Res.held ()]
    (.thru () () 0 (.lit 3)) := by decide

/-- FORGED guard: the widened index is right, but the hands are empty. -/
example : ¬ certCut4Ok TestD [] []
    (.thru () () 0 (.wide 0 10 (.lit 3))) := by decide

/-! ## CUT-5 remainder soundness: calls WITH arguments, carrying `RufPasst`

    Proved as `block5_sound` below. The argument COUNT shape and
    `gruende = 0` recompute (as in `certBlockGueltig`); the carried
    `RufPasst` is forwarded, never recomputed. Each call's argument list
    travels as an explicit hypothesis (`Block5Args`): `CertBlock5` carries
    the count only, and each argument's elaboration at arbitrary param `Ty`
    is the remaining booked piece -- named here as data. The
    `bindCallElse` error branch has no arm at all and stays booked. -/

/-- The booked remainder of CUT-5, named as data: the argument list each
    call site needs. `CertBlock5` carries the COUNT (`nargs`, checked
    against the callee); the elaboration of each argument -- an `Expr` at
    arbitrary param `Ty`, which `CertExpr` cannot print -- is supplied here,
    with the pointer behind `callInd`. -/
inductive Block5Args (D : Deklaration) (V : Vertrag D) :
    (Γ : Ctx) → (Λ Λ' : List (Res D)) → CertBlock5 D V Γ Λ Λ' → Type where
  | nil : Block5Args D V Γ Λ Λ .nil
  | callArgs (f : D.Fn) (nargs : Nat) (hp : RufPasst D V (D.signatur f) Λ)
      (args : Args D Γ Λ (D.params f))
      {r : CertBlock5 D V Γ (nach D f Λ) Λ'} (rest : Block5Args D V Γ (nach D f Λ) Λ' r) :
      Block5Args D V Γ Λ Λ' (CertBlock5.callArgs f nargs hp r)
  | callInd (n nargs : Nat) (hp : RufPasst D V (D.sigNr n) Λ)
      (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      {r : CertBlock5 D V Γ (nachSig D (D.sigNr n) Λ) Λ'}
      (rest : Block5Args D V Γ (nachSig D (D.sigNr n) Λ) Λ' r) :
      Block5Args D V Γ Λ Λ' (CertBlock5.callInd n nargs hp r)
  | bindCall (f : D.Fn) (nargs : Nat) (τ : Ty) (hp : RufPasst D V (D.signatur f) Λ)
      (args : Args D Γ Λ (D.params f))
      {r : CertBlock5 D V (τ :: Γ) (nach D f Λ) Λ'}
      (rest : Block5Args D V (τ :: Γ) (nach D f Λ) Λ' r) :
      Block5Args D V Γ Λ Λ' (CertBlock5.bindCall f nargs τ hp r)

/-- CUT-5 remainder soundness: a valid remainder block IMPLIES the judgment
    behind the supplied argument lists -- there EXISTS an accepted `Block`.
    `callArgs`/`callInd` forward the carried `RufPasst` with the recomputed
    count shape and `gruende = 0`; `bindCall` additionally extends the
    context by the checked result type. (The count itself is checked but not
    load-bearing for the elaboration: the supplied `Args` carry their own
    length -- the honest shrink is the supply, not the count.) -/
theorem block5_sound {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (b : CertBlock5 D V Γ Λ Λ')
    (s : Block5Args D V Γ Λ Λ' b) :
    certBlock5Ok D V Γ Λ Λ' b → ∃ _ : Block D V l Γ Λ Λ', True := by
  induction s with
  | nil => intro _; exact ⟨Block.nil, trivial⟩
  | callArgs f nargs hp args rest ih =>
    intro h
    simp only [certBlock5Ok] at h
    obtain ⟨_, hgr, hr⟩ := h
    obtain ⟨blk, _⟩ := ih hr
    exact ⟨Block.cons (Stmt.call f args hp hgr) blk, trivial⟩
  | callInd n nargs hp p args rest ih =>
    intro h
    simp only [certBlock5Ok] at h
    obtain ⟨_, hgr, hr⟩ := h
    obtain ⟨blk, _⟩ := ih hr
    exact ⟨Block.cons (Stmt.callInd p args hp hgr) blk, trivial⟩
  | bindCall f nargs τ hp args rest ih =>
    intro h
    simp only [certBlock5Ok] at h
    obtain ⟨_, he, hgr, hr⟩ := h
    obtain ⟨blk, _⟩ := ih hr
    exact ⟨Block.bindCall f args he hp hgr blk, trivial⟩

/-! ### CUT-5 remainder soundness probes -/

/-- The nullary call with an (empty) argument list, then the empty tail:
    params empty and no reasons, so the table accepts. (The implicits are
    named so that `f` elaborates against a concrete `Fn` type.) -/
example : ∃ _ : Block TestD TestV false [] [] [], True :=
  block5_sound (.callArgs false 0 TestHp .nil)
    (Block5Args.callArgs (D := TestD) (V := TestV) (Γ := []) (Λ := []) (Λ' := [])
      false 0 TestHp Args.nil .nil) (by decide)

/-- The indirect nullary call through signature `0`: the pointer and the
    (empty) argument list travel as proof. -/
example : ∃ _ : Block TestD TestV false [] [] [], True :=
  block5_sound (.callInd 0 0 TestHp .nil)
    (Block5Args.callInd (D := TestD) (V := TestV) (Γ := []) (Λ := []) (Λ' := [])
      0 0 TestHp (Expr.fnref false 0 rfl) Args.nil .nil) (by decide)

/-- A call WITH a param is no nullary call: `RufPasst` goes through, but the
    count shape fails -- the certificate is honestly rejected. -/
example : ¬ certBlock5Ok TestD TestV [] [] []
    (.callArgs true 0 TestHp1 .nil) := by decide

/-- An indirect call WITH a param is no nullary indirect call: same count
    shape failure through signature `1`. -/
example : ¬ certBlock5Ok TestD TestV [] [] []
    (.callInd 1 0 TestHp1 .nil) := by decide

/-- A binding call with a result is no nullary call: the callee returns
    nothing, so the result shape fails -- honestly rejected. -/
example : ¬ certBlock5Ok TestD TestV [] [] []
    (.bindCall false 0 (.int 1 1) TestHp .nil) := by decide

#print axioms cut3_sound
#print axioms cut4_sound
#print axioms block5_sound


end Gabbro.Grammatik
