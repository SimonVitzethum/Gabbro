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
  | _ => none

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
        (by obtain ⟨rfl, rfl, hL⟩ := hc; exact some ⟨_, .slot t f ei hL⟩)
      else none
    | _ => none

/-
  CUTS:
  - `print_elab`/`elab_valid` plus witnesses are being added piece by
    piece (rule 10); `varIdx`/`varOfAll`/`varOf`/`printInt`/`elabInt`
    stand so far.
-/
