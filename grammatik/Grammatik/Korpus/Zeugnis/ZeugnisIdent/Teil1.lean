module

public import Grammatik.Korpus.Zeugnis.Zeugnis
public import Grammatik.Korpus.Referenz.ReferenzB

@[expose] public section



namespace Gabbro.Grammatik

/-- De Bruijn index of a variable: the position `CertExpr.var` names. -/
def varIdx : Var Γ τ → Nat
  | .here => 0
  | .there x => varIdx x + 1

/-- Rebuild a variable from its index: the computational inverse of
    `varIdx` at ANY type. Bounds are READ from the context, never trusted
    from a print (mirror of `ctxTyp_var`, but returning the witness). -/
def varOfAll : (Γ : Ctx) → (k : Nat) → Option (Σ τ, Var Γ τ)
  | τ :: _, 0 => some ⟨τ, .here⟩
  | _ :: Γ, k + 1 =>
    match varOfAll Γ k with
    | some ⟨τ, x⟩ => some ⟨τ, .there x⟩
    | none => none
  | [], _ => none

/-- The int-typed projection of `varOfAll` (the shape `elabInt` uses). -/
def varOf (Γ : Ctx) (k : Nat) : Option (Σ lo hi : Int, Var Γ (.int lo hi)) :=
  match varOfAll Γ k with
  | some ⟨.int lo hi, x⟩ => some ⟨lo, hi, x⟩
  | _ => none

/-- Roundtrip for variables: the rebuilt variable IS the checked one.
    Every premise is used: `x` by induction, `ih` by rewriting. -/
theorem varOfAll_varIdx {Γ : Ctx} {τ : Ty} (x : Var Γ τ) :
    varOfAll Γ (varIdx x) = some ⟨τ, x⟩ := by
  induction x with
  | here => rfl
  | there x ih => simp only [varIdx, varOfAll, ih]

/-- Roundtrip at int type, behind the projection. -/
theorem varOf_varIdx {Γ : Ctx} {lo hi : Int} (x : Var Γ (.int lo hi)) :
    varOf Γ (varIdx x) = some ⟨lo, hi, x⟩ := by
  simp only [varOf, varOfAll_varIdx x]

/-- The rebuilt variable reads back through the range table: `varOfAll`
    at int type IS the `ctxTyp` lookup. Every premise is used (`Γ` by
    induction, `k`/`x` by casing, `h` by rewriting/injection). -/
theorem varOfAll_ctxTyp {Γ : Ctx} {k : Nat} {lo hi : Int} {x : Var Γ (.int lo hi)}
    (h : varOfAll Γ k = some ⟨.int lo hi, x⟩) : ctxTyp Γ k = some (lo, hi) := by
  revert k x h
  induction Γ with
  | nil =>
    intro k x h
    cases k <;> simp only [varOfAll, reduceCtorEq] at h
  | cons τ Γ ih =>
    intro k x h
    cases k with
    | zero =>
      simp only [varOfAll, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨hτ, -⟩ := h
      subst hτ
      rfl
    | succ k =>
      simp only [varOfAll] at h
      cases hsub : varOfAll Γ k with
      | none => simp only [hsub, reduceCtorEq] at h
      | some w =>
        obtain ⟨τw, xw⟩ := w
        simp only [hsub, Option.some.injEq, Sigma.mk.injEq] at h
        obtain ⟨hτw, -⟩ := h
        cases hτw
        have hsub' : varOfAll Γ k = some ⟨.int lo hi, xw⟩ := hsub
        have ihr := ih hsub'
        simp only [ctxTyp]
        exact ihr

/- Term identity at int type is stated after `print_elab_all` below
   (Lean processes top to bottom), as `print_elab`. -/

/-- The Lean-side printer: from a CHECKED (typed) term to its certificate.
    Proof fields are forgotten (they are recomputed by `elabInt`); shapes
    with no `CertExpr` print (`durch`, `altGlob`, `altSlot`, `leseBytes`,
    and every non-`int` constructor) answer `none` -- booked, not faked. -/
def printInt {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} :
    Expr D Γ Λ τ → Option (CertExpr D)
  | .lit n => some (.lit n)
  | .var x => some (.var (varIdx x))
  | .glob g _ => some (.glob g)
  | .slot t f i _ => (printInt i).map (CertExpr.slot t f)
  | .widen _ _ e =>
    match τ with
    | .int lo' hi' => (printInt e).map (CertExpr.wide lo' hi')
    | _ => none
  | .add a b => (printInt a).bind fun ca => (printInt b).bind fun cb => some (.add ca cb)
  | .sub a b => (printInt a).bind fun ca => (printInt b).bind fun cb => some (.sub ca cb)
  | .neg a => (printInt a).map CertExpr.neg
  | .mul a b => (printInt a).bind fun ca => (printInt b).bind fun cb => some (.mul ca cb)
  | .div _ _ a b => (printInt a).bind fun ca => (printInt b).bind fun cb => some (.div ca cb)
  | .rem _ _ a b => (printInt a).bind fun ca => (printInt b).bind fun cb => some (.rem ca cb)
  | .sdiv _ a b => (printInt a).bind fun ca => (printInt b).bind fun cb => some (.sdiv ca cb)
  | .srem _ a b => (printInt a).bind fun ca => (printInt b).bind fun cb => some (.srem ca cb)
  | .band _ _ a b => (printInt a).bind fun ca => (printInt b).bind fun cb => some (.band ca cb)
  | .bor w _ _ _ _ a b =>
    (printInt a).bind fun ca => (printInt b).bind fun cb => some (.bor w ca cb)
  | .bxor w _ _ _ _ a b =>
    (printInt a).bind fun ca => (printInt b).bind fun cb => some (.bxor w ca cb)
  | .shl w _ _ _ _ a b =>
    (printInt a).bind fun ca => (printInt b).bind fun cb => some (.shl w ca cb)
  | .shr w _ _ _ _ a b =>
    (printInt a).bind fun ca => (printInt b).bind fun cb => some (.shr w ca cb)
  -- Every remaining shape has no `CertExpr` print (booked, not faked):
  -- reads through pointers or post-entry values, byte reads, and every
  -- non-`int` constructor. One arm each, so every arm owns an equation
  -- lemma the roundtrip proof rewrites with.
  | .tru => none
  | .fls => none
  | .thru _ _ _ _ _ _ => none
  | .ptrOf _ _ _ _ => none
  | .refEq _ _ => none
  | .slotRef _ _ _ _ _ _ => none
  | .fnref _ _ _ => none
  | .oldG _ _ => none
  | .oldS _ _ _ _ => none
  | .getBytes _ _ _ _ _ _ _ _ => none
  | .lt _ _ => none
  | .le _ _ => none
  | .eq _ _ => none
  | .fllt _ _ => none
  | .flle _ _ => none
  | .and _ _ => none
  | .or _ _ => none
  | .not _ => none
  | .none _ => none
  | .some _ => none
  | .istSome _ => none
  | .case _ _ _ => none
  | .why _ _ => none
  | .forallSlots _ _ _ => none
  | .existsSlots _ _ _ => none
  | .reaches _ _ _ _ _ _ => none
  | .arrNil | .arrCons .. | .arrSet .. | .strLit .. | .strCat .. => none
  | .arrGet .. | .strLen .. => none
  | .strGet .. | .strEq .. | .strLt .. | .strWeit .. | .wenn .. | .eng .. => none
  | .intBuiltin1 .. | .intBuiltin2 .. | .count .. => none
  | .prod .. | .prodGet .. | .prodSet .. => none

/-- The computational elaborator: from a printed certificate back to a
    CHECKED term. Every side condition `certRange` recomputes is rechecked
    here with `if` (never trusted from the print); proofs are rebuilt by
    the `Decidable` instances (`darf`/`gdarf` from `Zeugnis.lean`, integer
    order/equations from the core). `none` means the print has no
    elaboration at all -- the forged-print half of the witness pair.
    The result type is read off the certificate, never supplied. -/
def elabInt {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} :
    CertExpr D → Option (Σ τ, Expr D Γ Λ τ)
  | .lit n => some ⟨_, .lit n⟩
  | .add a b =>
    match elabInt a, elabInt b with
    | some ⟨.int l1 h1, ea⟩, some ⟨.int l2 h2, eb⟩ => some ⟨_, .add ea eb⟩
    | _, _ => none
  | .sub a b =>
    match elabInt a, elabInt b with
    | some ⟨.int l1 h1, ea⟩, some ⟨.int l2 h2, eb⟩ => some ⟨_, .sub ea eb⟩
    | _, _ => none
  | .neg a =>
    match elabInt a with
    | some ⟨.int _ _, ea⟩ => some ⟨_, .neg ea⟩
    | _ => none
  | .mul a b =>
    match elabInt a, elabInt b with
    | some ⟨.int l1 h1, ea⟩, some ⟨.int l2 h2, eb⟩ => some ⟨_, .mul ea eb⟩
    | _, _ => none
  | .div a b =>
    match elabInt a, elabInt b with
    | some ⟨.int l1 h1, ea⟩, some ⟨.int l2 h2, eb⟩ =>
      if h : 0 ≤ l1 ∧ 1 ≤ l2 then some ⟨_, .div h.1 h.2 ea eb⟩ else none
    | _, _ => none
  | .rem a b =>
    match elabInt a, elabInt b with
    | some ⟨.int l1 h1, ea⟩, some ⟨.int l2 h2, eb⟩ =>
      if h : 0 ≤ l1 ∧ 1 ≤ l2 then some ⟨_, .rem h.1 h.2 ea eb⟩ else none
    | _, _ => none
  | .sdiv a b =>
    match elabInt a, elabInt b with
    | some ⟨.int l1 h1, ea⟩, some ⟨.int l2 h2, eb⟩ =>
      if h : 1 ≤ l2 ∨ h2 ≤ -1 then some ⟨_, .sdiv h ea eb⟩ else none
    | _, _ => none
  | .srem a b =>
    match elabInt a, elabInt b with
    | some ⟨.int l1 h1, ea⟩, some ⟨.int l2 h2, eb⟩ =>
      if h : 1 ≤ l2 ∨ h2 ≤ -1 then some ⟨_, .srem h ea eb⟩ else none
    | _, _ => none
  | .band a b =>
    match elabInt a, elabInt b with
    | some ⟨.int l1 h1, ea⟩, some ⟨.int l2 h2, eb⟩ =>
      if h : 0 ≤ l1 ∧ 0 ≤ l2 then some ⟨_, .band h.1 h.2 ea eb⟩ else none
    | _, _ => none
  | .bor w a b =>
    match elabInt a, elabInt b with
    | some ⟨.int l1 h1, ea⟩, some ⟨.int l2 h2, eb⟩ =>
      if h : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w then
        some ⟨_, .bor w h.1 h.2.1 h.2.2.1 h.2.2.2 ea eb⟩
      else none
    | _, _ => none
  | .bxor w a b =>
    match elabInt a, elabInt b with
    | some ⟨.int l1 h1, ea⟩, some ⟨.int l2 h2, eb⟩ =>
      if h : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w then
        some ⟨_, .bxor w h.1 h.2.1 h.2.2.1 h.2.2.2 ea eb⟩
      else none
    | _, _ => none
  | .shl w a b =>
    match elabInt a, elabInt b with
    | some ⟨.int l1 h1, ea⟩, some ⟨.int l2 h2, eb⟩ =>
      if h : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < (w : Int) then
        some ⟨_, .shl w h.2.2.1 h.2.2.2 h.1 h.2.1 ea eb⟩
      else none
    | _, _ => none
  | .shr w a b =>
    match elabInt a, elabInt b with
    | some ⟨.int l1 h1, ea⟩, some ⟨.int l2 h2, eb⟩ =>
      if h : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < (w : Int) then
        some ⟨_, .shr w h.2.2.1 h.2.2.2 h.1 h.2.1 ea eb⟩
      else none
    | _, _ => none
  | .wide lo' hi' a =>
    match elabInt a with
    | some ⟨.int l1 h1, ea⟩ =>
      if h : lo' ≤ l1 ∧ h1 ≤ hi' then some ⟨_, .widen h.1 h.2 ea⟩ else none
    | _ => none
  | .var k =>
    match varOfAll Γ k with
    | some ⟨τ, x⟩ => some ⟨τ, .var x⟩
    | none => none
  | .glob g =>
    if hc : gdarf D g Λ then some ⟨_, .glob g hc⟩ else none
  | .slot t f i =>
    match (elabInt (D := D) (Γ := Γ) (Λ := Λ) i) with
    | some ⟨.int l h, ei⟩ =>
      if hc : l = 0 ∧ h = D.count t - 1 ∧ darf D t Λ then
        have hty : (Ty.int l h) = (Ty.index (D.count t)) := by rw [hc.1, hc.2.1]
        some ⟨_, .slot t f (Eq.mp (congrArg (Expr D Γ Λ) hty) ei) hc.2.2⟩
      else none
    | _ => none

end Gabbro.Grammatik
