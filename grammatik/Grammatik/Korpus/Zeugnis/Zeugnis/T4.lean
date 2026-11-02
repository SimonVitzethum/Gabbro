/- Part 4 of 4 of `Zeugnis` (split by instrumente/teile/lean-teilen.py; the umbrella `Zeugnis.lean` imports all parts). -/
module
public import Grammatik.Korpus.Zeugnis.Zeugnis.T3
public import Grammatik.Korpus.Zeugnis.Zeugnis.T4Basis
@[expose] public section

namespace Gabbro.Grammatik
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
  | .thru t _ n _ => Σ rw : Bool, Expr D Γ Λ (.ptr (.table n (true, rw) (D.tableSpace t)))
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
    exact ⟨.ptr (.table n (true, rw) (D.tableSpace t)), Expr.ptrOf t n h (true, rw), trivial⟩
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
    ⟨true, Expr.ptrOf () 0 rfl (true, true)⟩ (by decide)

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
