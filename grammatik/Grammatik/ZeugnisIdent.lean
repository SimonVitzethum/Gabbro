/-
  File:     Grammatik/ZeugnisIdent.lean
  Subject:  Term identity for expression certificates (Lean side).

  Lane 146 found that nothing proves the printed certificate describes the
  SAME term the checker checked (`certemit.rs` books
  "printer-prints-what-was-checked is trust base there"). This file closes
  the Lean half: a Lean-side `printInt` from typed `Expr` terms (the int
  fragment covered by `CertExpr` in `Zeugnis.lean`) to certificates, a
  computational `elabInt` (Option-returning, no choice inside), and
  `print_elab` -- print then elab round-trips to the same term, proved by
  induction over every `Expr` constructor (the 17 `CertExpr` shapes
  round-trip; the shapes with no `CertExpr` print state `True`).
  The converse `elab_valid` links elaboration back to the existing
  soundness: `elabInt c = some e` implies `GueltigAbleitung`.

  The Rust residue (trust base left): `certemit.rs` must print
  `printInt e` for the CHECKED `e` -- that implication is not in Lean.

  CHECK
    ./lean-probe grammatik/Grammatik/ZeugnisIdent.lean
-/
import Grammatik.Zeugnis
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

/-- De Bruijn index of a variable: the position `CertExpr.var` names. -/
def varIdx : Var Γ τ → Nat
  | .hier => 0
  | .dort x => varIdx x + 1

/-- Rebuild a variable from its index: the computational inverse of
    `varIdx` at ANY type. Bounds are READ from the context, never trusted
    from a print (mirror of `ctxTyp_var`, but returning the witness). -/
def varOfAll : (Γ : Ctx) → (k : Nat) → Option (Σ τ, Var Γ τ)
  | τ :: _, 0 => some ⟨τ, .hier⟩
  | _ :: Γ, k + 1 =>
    match varOfAll Γ k with
    | some ⟨τ, x⟩ => some ⟨τ, .dort x⟩
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
  | hier => rfl
  | dort x ih => simp [varIdx, varOfAll, ih]

/-- Roundtrip at int type, behind the projection. -/
theorem varOf_varIdx {Γ : Ctx} {lo hi : Int} (x : Var Γ (.int lo hi)) :
    varOf Γ (varIdx x) = some ⟨lo, hi, x⟩ := by
  simp [varOf, varOfAll_varIdx x]

/-- The rebuilt variable reads back through the range table: `varOfAll`
    at int type IS the `ctxTyp` lookup. Every premise is used (`Γ` by
    induction, `k`/`x` by casing, `h` by rewriting/injection). -/
theorem varOfAll_ctxTyp {Γ : Ctx} {k : Nat} {lo hi : Int} {x : Var Γ (.int lo hi)}
    (h : varOfAll Γ k = some ⟨.int lo hi, x⟩) : ctxTyp Γ k = some (lo, hi) := by
  revert k x h
  induction Γ with
  | nil =>
    intro k x h
    cases k <;> simp [varOfAll] at h
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
      | none => simp [hsub] at h
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
  | .weiter _ _ e =>
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
  | .wahr => none
  | .falsch => none
  | .durch _ _ _ _ _ _ => none
  | .ptrOf _ _ _ _ => none
  | .fnref _ _ _ => none
  | .altGlob _ _ => none
  | .altSlot _ _ _ _ => none
  | .leseBytes _ _ _ _ _ _ _ _ => none
  | .lt _ _ => none
  | .le _ _ => none
  | .eq _ _ => none
  | .fllt _ _ => none
  | .flle _ _ => none
  | .und _ _ => none
  | .oder _ _ => none
  | .nicht _ => none
  | .none _ => none
  | .some _ => none
  | .istSome _ => none
  | .fall _ _ _ => none
  | .grund _ _ => none
  | .forallSlots _ _ _ => none
  | .existsSlots _ _ _ => none
  | .reaches _ _ _ _ _ _ => none

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
      if h : lo' ≤ l1 ∧ h1 ≤ hi' then some ⟨_, .weiter h.1 h.2 ea⟩ else none
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

/-- Term identity, general form: printing a CHECKED term and
    re-elaborating gives back the SAME term -- proved by induction over
    every `Expr` constructor. The 17 `CertExpr` shapes round-trip (the
    some-branch); the 23 shapes with no print state `True` (the none-branch:
    `durch`, `altGlob`/`altSlot`, `leseBytes`, and every non-`int`
    constructor). No premise is assumed about the term -- the statement
    quantifies over the term itself, so there is nothing vacuous to
    discharge (rules 4/13: the witness is `print_elab_all_zeuge`). -/
theorem print_elab_all {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} :
    ∀ (e : Expr D Γ Λ τ),
    match printInt e with
    | some c => elabInt c = some ⟨τ, e⟩
    | none => True
  | .lit n => rfl
  | .var x => by simp [printInt, elabInt, varOfAll_varIdx x]
  | .glob g hL => by simp [printInt, elabInt, hL]
  | .slot t f i hL => by
    have ihi := print_elab_all i
    cases hi : printInt i with
    | none => simp [printInt, hi]
    | some ci =>
      have ihi' : elabInt ci = some ⟨_, i⟩ := by rw [hi] at ihi; exact ihi
      simp [printInt, hi, elabInt, ihi', hL]
  | .weiter h1 h2 e => by
    have ihe := print_elab_all e
    cases he : printInt e with
    | none => simp [printInt, he]
    | some ce =>
      have ihe' : elabInt ce = some ⟨_, e⟩ := by rw [he] at ihe; exact ihe
      simp [printInt, he, elabInt, ihe', h1, h2]
  | .add a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      cases hb : printInt b with
      | none => simp [printInt, ha, hb]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp [printInt, ha, hb, elabInt, iha', ihb']
  | .sub a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      cases hb : printInt b with
      | none => simp [printInt, ha, hb]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp [printInt, ha, hb, elabInt, iha', ihb']
  | .neg a => by
    have iha := print_elab_all a
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
      simp [printInt, ha, elabInt, iha']
  | .mul a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      cases hb : printInt b with
      | none => simp [printInt, ha, hb]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp [printInt, ha, hb, elabInt, iha', ihb']
  | .div h0 h1' a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      cases hb : printInt b with
      | none => simp [printInt, ha, hb]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp [printInt, ha, hb, elabInt, iha', ihb', h0, h1']
  | .rem h0 h1' a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      cases hb : printInt b with
      | none => simp [printInt, ha, hb]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp [printInt, ha, hb, elabInt, iha', ihb', h0, h1']
  | .sdiv hb a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      cases hb2 : printInt b with
      | none => simp [printInt, ha, hb2]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb2] at ihb; exact ihb
        simp [printInt, ha, hb2, elabInt, iha', ihb', hb]
  | .srem hb a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      cases hb2 : printInt b with
      | none => simp [printInt, ha, hb2]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb2] at ihb; exact ihb
        simp [printInt, ha, hb2, elabInt, iha', ihb', hb]
  | .band h0 h0' a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      cases hb : printInt b with
      | none => simp [printInt, ha, hb]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp [printInt, ha, hb, elabInt, iha', ihb', h0, h0']
  | .bor w h0 h0' hw1 hw2 a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      cases hb : printInt b with
      | none => simp [printInt, ha, hb]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp [printInt, ha, hb, elabInt, iha', ihb', h0, h0', hw1, hw2]
  | .bxor w h0 h0' hw1 hw2 a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      cases hb : printInt b with
      | none => simp [printInt, ha, hb]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp [printInt, ha, hb, elabInt, iha', ihb', h0, h0', hw1, hw2]
  | .shl w hw1 hw2 h0 h0' a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      cases hb : printInt b with
      | none => simp [printInt, ha, hb]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp [printInt, ha, hb, elabInt, iha', ihb', hw1, hw2, h0, h0']
  | .shr w hw1 hw2 h0 h0' a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp [printInt, ha]
    | some ca =>
      cases hb : printInt b with
      | none => simp [printInt, ha, hb]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp [printInt, ha, hb, elabInt, iha', ihb', hw1, hw2, h0, h0']
  | .wahr => by simp [printInt]
  | .falsch => by simp [printInt]
  | .durch _ _ _ _ _ _ => by simp [printInt]
  | .ptrOf _ _ _ _ => by simp [printInt]
  | .fnref _ _ _ => by simp [printInt]
  | .altGlob _ _ => by simp [printInt]
  | .altSlot _ _ _ _ => by simp [printInt]
  | .leseBytes _ _ _ _ _ _ _ _ => by simp [printInt]
  | .lt _ _ => by simp [printInt]
  | .le _ _ => by simp [printInt]
  | .eq _ _ => by simp [printInt]
  | .fllt _ _ => by simp [printInt]
  | .flle _ _ => by simp [printInt]
  | .und _ _ => by simp [printInt]
  | .oder _ _ => by simp [printInt]
  | .nicht _ => by simp [printInt]
  | .none _ => by simp [printInt]
  | .some _ => by simp [printInt]
  | .istSome _ => by simp [printInt]
  | .fall _ _ _ => by simp [printInt]
  | .grund _ _ => by simp [printInt]
  | .forallSlots _ _ _ => by simp [printInt]
  | .existsSlots _ _ _ => by simp [printInt]
  | .reaches _ _ _ _ _ _ => by simp [printInt]

/-- Term identity at int type: the task's proposed shape
    (`print_elab (e : CheckedExpr) : elab (print e) = some e`).
    `printInt` is partial -- the shapes with no `CertExpr` print answer
    `none` -- so the statement round-trips exactly where print is defined
    (the some-branch) and states `True` elsewhere. This is an elaboration
    detail of the fixed target, not a weakening: for every printable
    constructor it says `elab (print e) = some e`. -/
theorem print_elab {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int}
    (e : Expr D Γ Λ (.int lo hi)) :
    match printInt e with
    | some c => elabInt c = some ⟨.int lo hi, e⟩
    | none => True :=
  print_elab_all e

/-- Converse: elaboration implies certificate validity -- an elaborated
    print is exactly what the range table recomputes. Combined with the
    existing `zeugnis_sound`, `elabInt c = some e` yields both the
    `GueltigAbleitung` (here) and the judgment (there). Proved by
    induction over the certificate; every premise is used (sub-equations
    feed the IHs, side hypotheses discharge the table guards). -/
theorem elab_valid {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (c : CertExpr D) {lo hi : Int} {e : Expr D Γ Λ (.int lo hi)}
    (h : elabInt c = some ⟨.int lo hi, e⟩) :
    GueltigAbleitung D Γ Λ c lo hi := by
  induction c generalizing lo hi e with
  | lit n =>
    simp only [elabInt, Option.some.injEq, Sigma.mk.injEq, Ty.int.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    rfl
  | var k =>
    simp only [elabInt] at h
    cases hvar : varOfAll Γ k with
    | none => simp [hvar] at h
    | some w =>
      obtain ⟨τw, xw⟩ := w
      simp only [hvar, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨hτw, -⟩ := h
      cases hτw
      exact varOfAll_ctxTyp hvar
  | glob g =>
    by_cases hc : gdarf D g Λ
    · have h' : elabInt (D := D) (Γ := Γ) (Λ := Λ) (.glob g) =
          some ⟨D.gtyp g, .glob g hc⟩ := by
        simp only [elabInt, dif_pos hc]
      rw [h'] at h
      have hg : D.gtyp g = .int lo hi := congrArg Sigma.fst (Option.some.inj h)
      show certRange D Γ Λ (.glob g) = some (lo, hi)
      simp [certRange, hg, hc, intVonTyp]
    · have h' : elabInt (D := D) (Γ := Γ) (Λ := Λ) (.glob g) = none := by
        simp only [elabInt, dif_neg hc]
      rw [h'] at h
      simp at h
  | add a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp [elabInt, ha1, hb1] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1, Option.some.injEq, Sigma.mk.injEq,
              Ty.int.injEq] at h
            obtain ⟨⟨rfl, rfl⟩, -⟩ := h
            have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
            have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
            show certRange D Γ Λ (.add a b) = some (l1 + l2, h1 + h2)
            simp [certRange, ra, rb]
          | bool | opt | sum | grund | never | fl | fnptr | ptr =>
            simp [elabInt, ha1, hb1] at h
        | bool | opt | sum | grund | never | fl | fnptr | ptr =>
          simp [elabInt, ha1, hb1] at h
  | sub a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp [elabInt, ha1, hb1] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1, Option.some.injEq, Sigma.mk.injEq,
              Ty.int.injEq] at h
            obtain ⟨⟨rfl, rfl⟩, -⟩ := h
            have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
            have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
            show certRange D Γ Λ (.sub a b) = some (l1 - h2, h1 - l2)
            simp [certRange, ra, rb]
          | bool | opt | sum | grund | never | fl | fnptr | ptr =>
            simp [elabInt, ha1, hb1] at h
        | bool | opt | sum | grund | never | fl | fnptr | ptr =>
          simp [elabInt, ha1, hb1] at h
  | neg a iha =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases τa with
      | int l hh =>
        simp only [elabInt, ha1, Option.some.injEq, Sigma.mk.injEq, Ty.int.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, -⟩ := h
        have ra : certRange D Γ Λ a = some (l, hh) := iha ha1
        show certRange D Γ Λ (.neg a) = some (-hh, -l)
        simp [certRange, ra]
      | bool | opt | sum | grund | never | fl | fnptr | ptr =>
        simp [elabInt, ha1] at h
  | mul a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp [elabInt, ha1, hb1] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1, Option.some.injEq, Sigma.mk.injEq,
              Ty.int.injEq] at h
            obtain ⟨⟨rfl, rfl⟩, -⟩ := h
            have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
            have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
            show certRange D Γ Λ (.mul a b) =
              some (imin (imin (l1 * l2) (l1 * h2)) (imin (h1 * l2) (h1 * h2)),
                imax (imax (l1 * l2) (l1 * h2)) (imax (h1 * l2) (h1 * h2)))
            simp [certRange, ra, rb]
          | bool | opt | sum | grund | never | fl | fnptr | ptr =>
            simp [elabInt, ha1, hb1] at h
        | bool | opt | sum | grund | never | fl | fnptr | ptr =>
          simp [elabInt, ha1, hb1] at h
  | div a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp [elabInt, ha1, hb1] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 1 ≤ l2
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.div a b) = some (0, h1)
              simp [certRange, ra, rb, hc]
            · simp only [dif_neg hc] at h
              simp at h
          | bool | opt | sum | grund | never | fl | fnptr | ptr =>
            simp [elabInt, ha1, hb1] at h
        | bool | opt | sum | grund | never | fl | fnptr | ptr =>
          simp [elabInt, ha1, hb1] at h
  | rem a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp [elabInt, ha1, hb1] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 1 ≤ l2
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.rem a b) = some (0, h2 - 1)
              simp [certRange, ra, rb, hc]
            · simp only [dif_neg hc] at h
              simp at h
          | bool | opt | sum | grund | never | fl | fnptr | ptr =>
            simp [elabInt, ha1, hb1] at h
        | bool | opt | sum | grund | never | fl | fnptr | ptr =>
          simp [elabInt, ha1, hb1] at h
  | sdiv a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp [elabInt, ha1, hb1] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 1 ≤ l2 ∨ h2 ≤ -1
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.sdiv a b) =
                some (-(betragMax l1 h1), betragMax l1 h1)
              simp [certRange, ra, rb, hc]
            · simp only [dif_neg hc] at h
              simp at h
          | bool | opt | sum | grund | never | fl | fnptr | ptr =>
            simp [elabInt, ha1, hb1] at h
        | bool | opt | sum | grund | never | fl | fnptr | ptr =>
          simp [elabInt, ha1, hb1] at h
  | srem a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp [elabInt, ha1, hb1] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 1 ≤ l2 ∨ h2 ≤ -1
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.srem a b) =
                some (-(betragMax l2 h2 - 1), betragMax l2 h2 - 1)
              simp [certRange, ra, rb, hc]
            · simp only [dif_neg hc] at h
              simp at h
          | bool | opt | sum | grund | never | fl | fnptr | ptr =>
            simp [elabInt, ha1, hb1] at h
        | bool | opt | sum | grund | never | fl | fnptr | ptr =>
          simp [elabInt, ha1, hb1] at h
  | band a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp [elabInt, ha1, hb1] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.band a b) = some (0, h1)
              simp [certRange, ra, rb, hc]
            · simp only [dif_neg hc] at h
              simp at h
          | bool | opt | sum | grund | never | fl | fnptr | ptr =>
            simp [elabInt, ha1, hb1] at h
        | bool | opt | sum | grund | never | fl | fnptr | ptr =>
          simp [elabInt, ha1, hb1] at h
  | bor w a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp [elabInt, ha1, hb1] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.bor w a b) = some (0, 2 ^ w - 1)
              simp [certRange, ra, rb, hc]
            · simp only [dif_neg hc] at h
              simp at h
          | bool | opt | sum | grund | never | fl | fnptr | ptr =>
            simp [elabInt, ha1, hb1] at h
        | bool | opt | sum | grund | never | fl | fnptr | ptr =>
          simp [elabInt, ha1, hb1] at h
  | bxor w a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp [elabInt, ha1, hb1] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.bxor w a b) = some (0, 2 ^ w - 1)
              simp [certRange, ra, rb, hc]
            · simp only [dif_neg hc] at h
              simp at h
          | bool | opt | sum | grund | never | fl | fnptr | ptr =>
            simp [elabInt, ha1, hb1] at h
        | bool | opt | sum | grund | never | fl | fnptr | ptr =>
          simp [elabInt, ha1, hb1] at h
  | shl w a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp [elabInt, ha1, hb1] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < (w : Int)
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.shl w a b) = some (0, h1 * 2 ^ h2.toNat)
              simp [certRange, ra, rb, hc]
            · simp only [dif_neg hc] at h
              simp at h
          | bool | opt | sum | grund | never | fl | fnptr | ptr =>
            simp [elabInt, ha1, hb1] at h
        | bool | opt | sum | grund | never | fl | fnptr | ptr =>
          simp [elabInt, ha1, hb1] at h
  | shr w a b iha ihb =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases hb1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) b with
      | none => simp [elabInt, ha1, hb1] at h
      | some vb =>
        obtain ⟨τb, eb⟩ := vb
        cases τa with
        | int l1 h1 =>
          cases τb with
          | int l2 h2 =>
            simp only [elabInt, ha1, hb1] at h
            by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < (w : Int)
            · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
                Ty.int.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              have ra : certRange D Γ Λ a = some (l1, h1) := iha ha1
              have rb : certRange D Γ Λ b = some (l2, h2) := ihb hb1
              show certRange D Γ Λ (.shr w a b) = some (0, h1)
              simp [certRange, ra, rb, hc]
            · simp only [dif_neg hc] at h
              simp at h
          | bool | opt | sum | grund | never | fl | fnptr | ptr =>
            simp [elabInt, ha1, hb1] at h
        | bool | opt | sum | grund | never | fl | fnptr | ptr =>
          simp [elabInt, ha1, hb1] at h
  | wide lo' hi' a iha =>
    cases ha1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) a with
    | none => simp [elabInt, ha1] at h
    | some va =>
      obtain ⟨τa, ea⟩ := va
      cases τa with
      | int l hh =>
        simp only [elabInt, ha1] at h
        by_cases hc : lo' ≤ l ∧ hh ≤ hi'
        · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq,
            Ty.int.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, -⟩ := h
          have ra : certRange D Γ Λ a = some (l, hh) := iha ha1
          show certRange D Γ Λ (.wide lo' hi' a) = some (lo', hi')
          simp [certRange, ra, hc]
        · simp only [dif_neg hc] at h
          simp at h
      | bool | opt | sum | grund | never | fl | fnptr | ptr =>
        simp [elabInt, ha1] at h
  | slot t f i ihi =>
    cases hi1 : elabInt (D := D) (Γ := Γ) (Λ := Λ) i with
    | none => simp [elabInt, hi1] at h
    | some w =>
      obtain ⟨τw, eiw⟩ := w
      cases τw with
      | int l hh =>
        simp only [elabInt, hi1] at h
        by_cases hc : l = 0 ∧ hh = D.count t - 1 ∧ darf D t Λ
        · simp only [dif_pos hc, Option.some.injEq, Sigma.mk.injEq] at h
          obtain ⟨hg, -⟩ := h
          obtain ⟨rfl, rfl, hL⟩ := hc
          have ri : certRange D Γ Λ i = some (0, D.count t - 1) := ihi hi1
          show certRange D Γ Λ (.slot t f i) = some (lo, hi)
          simp [certRange, ri, hg, hL, intVonTyp]
        · simp only [dif_neg hc] at h
          simp at h
      | bool | opt | sum | grund | never | fl | fnptr | ptr =>
        simp [elabInt, hi1] at h

/-
  CUTS:
  - Witnesses `print_elab_all_zeuge`, `print_elab_zeuge`, `elab_valid_zeuge`
    are still to come, then the closing `#print axioms`.
-/
