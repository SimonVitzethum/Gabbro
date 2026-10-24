/-
  File:     Grammatik/Zeugnis.lean
  Subject:  The certificate side of the S4/V5 witness pair (Lean side only).

  SOURCE SENTENCES
    dokumente/PLAN-UMSETZUNG.md §1.3 -- the derivation printed as Lean; Lean
      accepting the print is the statement that the program is a sentence of
      the grammar. A `Zeugnis` the Rust side gets wrong is a Lean error at the
      line of the constructor.
    dokumente/PLAN-SICHERHEIT.md S4 (`checker_agrees` witness pairs per unit)
      + dokumente/PLAN-VERIFIKATION.md §3/V5 -- `gabbro lean` writes, per unit,
      `theorem checker_agrees : ... := by decide`; disagreement fails LOUDLY.
    messung/ZIEL-BEWERTUNG-2026-09-10.md, "S4 scope" -- the W16 seam fails loudly
      per routine per run instead of silently.

  WHAT STANDS HERE
    `CertExpr` -- the printed certificate format: derivation terms as PLAIN DATA
      (ranges as numbers, side conditions NOT as proofs). This is what the Rust
      printer writes; it carries no evidence by itself.
    `certRange` -- the range table (M104/M102), recomputed on the Lean side.
    `GueltigAbleitung c lo hi` -- the validity predicate: the printed claim
      `(lo, hi)` is EXACTLY what the table recomputes. A forged or mismatched
      print is not "rejected with a message"; it is PROVABLY invalid
      (`¬ GueltigAbleitung ...`, closed by `decide` below), and no acceptance
      proof can be built from it -- failure by construction, not by diagnostic.
    `zeugnis_sound` -- soundness: a valid certificate IMPLIES the judgment,
      i.e. elaborates to a real `Expr` term (an accepted derivation). This is
      the direction this file owns.

  TRUST BASE (explicit)
    The Rust printer (`gabbro lean` / `gabbro-ableitung`, PLAN-UMSETZUNG.md §1.3)
    is TRUST BASE here and stays trust base: this file proves
    valid-print-implies-judgment, NOT printer-prints-what-checker-derived.
    A printer that prints a different derivation than the one it checked is
    outside this file -- exactly as §1.3 books it (the print, not the printer,
    is what Lean checks).

  CUTS (shrunk, not faked -- each booked cut is a constructor this file does NOT cover)
    CUT-1 signed division and remainder (`sdiv`/`srem`): COVERED below
      (certificate rows, validity side conditions, soundness cases, probes).
    CUT-2 bitwise and shifts (`band`/`bor`/`bxor`/`shl`/`shr`, width proofs):
      COVERED below (same shape as CUT-1).
    CUT-3 floats, options, sums, grounds, quantifiers, `reaches`: COVERED below
      (constructors, range arms, validity defs with Decidable instances, and
      soundness as `cut3_sound`; the quantifier arms take the body as an
      explicit hypothesis -- the body elaboration is the remaining booked
      piece, named as `Cut3Body`).
    CUT-4 variables and carrier accesses: COVERED below for the int fragment --
      name reads (`var`, de Bruijn index against `Γ`), global reads (`glob`,
      type from `D.gtyp`, guard `gdarf` recomputed), place reads (`slot`,
      index shape `0 .. count - 1` plus field type plus guard `darf`
      recomputed). Each with certRange arms, `GueltigAbleitung` side
      conditions, soundness cases, pos/neg decide probes.
      REMAINDER, half covered: `ptrOf`/`fnref` are COVERED below (design plus
      soundness as `cut4_sound`); `durch` is covered conditional on the
      pointer it names (`Cut4Ptr` -- the pointer term is the remaining booked
      piece). Still booked: `altGlob`/`altSlot` (post-entry values,
      not reads of the live world).
    CUT-5 resource contexts: COVERED below for straight-line int blocks --
      `bind` (context extension by the recomputed range), nullary `call`
      (`params = []`, `gruende = 0` recomputed), `ret`/`retWert` (result shape
      plus the linear balance `Λ.Perm V.ende` recomputed). Each with validity
      side conditions, soundness cases, pos/neg decide probes.
      REMAINDER, COVERED below (design plus soundness as `block5_sound`,
      conditional on the argument lists): calls with arguments
      (`callArgs`/`callInd`/`bindCall`) recompute the argument-count shape and
      `gruende = 0`, and a call's `RufPasst` travels AS PROOF in the
      certificate. It quantifies over the arbitrary carrier types (`∀ t`,
      `∀ g`, `∀ L`), so no range table can recompute it the way `certRange`
      recomputes `darf`; carrying it is the honest shrink, and the day
      `Tab`/`Glob` enumerate, the arm can check it instead. Each argument's
      elaboration travels as an explicit hypothesis (`Block5Args`) -- the
      remaining booked piece; the `bindCallElse` error branch stays booked.
    The int fragment stands as it was: every `CertExpr` certificate elaborates
    to an `Expr` of `int` type (reads) or a `Block` over int bindings
    (statements). Beyond it, `cut3_sound`/`cut4_sound`/`block5_sound` cover
    floats, options, sums, grounds, `reaches`, pointers, function references,
    and calls with arguments -- conditional on the three named supplies
    (`Cut3Body`, `Cut4Ptr`, `Block5Args`). Still booked: `altGlob`/`altSlot`,
    the `bindCallElse` error branch, and the three supplies themselves.

  CHECK
    cd grammatik && lake env lean Grammatik/Zeugnis.lean
    Finished proofs only: the build log carries no unfinished-proof warning,
    and `#print axioms zeugnis_sound` / `#print axioms block_sound` at the end
    name every axiom the soundness proofs rest on.
-/
import Grammatik.Kern.Syntax.Syntax

namespace Gabbro.Grammatik

/-! ## Context lookups: what the range table consults besides the term

    The closed fragment never looks at `Γ` or `Λ`; the CUT-4 shapes do, and
    only through the total functions below. All are plain structural
    recursion, so `decide` evaluates them wherever the world is concrete. -/

/-- The int payload of a type, if it has one. Reads of non-int carriers
    (`bool` globals, pointer slots) land on `none` -- booked, not faked. -/
def intVonTyp : Ty → Option (Int × Int)
  | .int lo hi => some (lo, hi)
  | _ => none

/-- What `intVonTyp` promises: a `some` came from an `int` type. -/
theorem intVonTyp_eq {τ : Ty} {lo hi : Int}
    (h : intVonTyp τ = some (lo, hi)) : τ = .int lo hi := by
  cases τ with
  | int lo' hi' =>
    simp [intVonTyp] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | bool => simp [intVonTyp] at h
  | opt _ => simp [intVonTyp] at h
  | sum _ => simp [intVonTyp] at h
  | why _ => simp [intVonTyp] at h
  | never => simp [intVonTyp] at h
  | fl _ => simp [intVonTyp] at h
  | fnptr _ => simp [intVonTyp] at h
  | ptr _ _ => simp [intVonTyp] at h
  | ref _ => simp [intVonTyp] at h

/-- The range of the `k`-th variable of `Γ`, if it is int-typed: a de Bruijn
    lookup that says `none` for out-of-range indices and non-int types. -/
def ctxTyp : Ctx → Nat → Option (Int × Int)
  | τ :: _, 0 =>
    match τ with
    | .int lo hi => some (lo, hi)
    | _ => none
  | _ :: Γ, k + 1 => ctxTyp Γ k
  | [], _ => none

/-- What `ctxTyp` promises: a `some` names a variable that EXISTS. The
    certificate carries the index as plain data (`Nat`); the `Var` witness
    is rebuilt here, never trusted from the print. -/
theorem ctxTyp_var (Γ : Ctx) (k : Nat) (lo hi : Int)
    (h : ctxTyp Γ k = some (lo, hi)) : ∃ _ : Var Γ (.int lo hi), True := by
  induction Γ generalizing k with
  | nil =>
    cases k <;> simp [ctxTyp] at h
  | cons τ Γ ih =>
    cases k with
    | zero =>
      cases τ with
      | int lo' hi' =>
        simp [ctxTyp] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨.here, trivial⟩
      | bool => simp [ctxTyp] at h
      | opt _ => simp [ctxTyp] at h
      | sum _ => simp [ctxTyp] at h
      | why _ => simp [ctxTyp] at h
      | never => simp [ctxTyp] at h
      | fl _ => simp [ctxTyp] at h
      | fnptr _ => simp [ctxTyp] at h
      | ptr _ _ => simp [ctxTyp] at h
      | ref _ => simp [ctxTyp] at h
    | succ k =>
      simp [ctxTyp] at h
      obtain ⟨x, _⟩ := ih k h
      exact ⟨.there x, trivial⟩

/-- Guard predicates as `Decidable`: `darf`/`gdarf` quantify over the finite
    `braucht` list with decidable membership, so the table can recompute them
    with `if` instead of trusting them from the print. -/
instance decDarf (D : Deklaration) (t : D.Tab) (Λ : List (Res D)) :
    Decidable (darf D t Λ) := by
  unfold darf
  infer_instance

instance decGdarf (D : Deklaration) (g : D.Glob) (Λ : List (Res D)) :
    Decidable (gdarf D g Λ) := by
  unfold gdarf
  infer_instance

/-- The printed certificate: a derivation term as plain data.

    Each constructor mirrors the `Expr` constructor of the same shape, but the
    hypothesis fields are ABSENT: the claimed result range `(lo, hi)` travels
    beside the term (as the argument of `GueltigAbleitung`), and every side
    condition (`0 ≤ l1`, `1 ≤ l2`, `lo' ≤ l1`, the guards `darf`/`gdarf`, the
    index shape, the context lookup) is recomputed by `certRange`, never
    trusted from the print. The three CUT-4 shapes carry declaration DATA
    (`g : D.Glob`, `t`, `f`, the de Bruijn index `k`) -- never proofs. -/
inductive CertExpr (D : Deklaration) where
  | lit (n : Int)
  | add (a b : CertExpr D)
  | sub (a b : CertExpr D)
  | neg (a : CertExpr D)
  | mul (a b : CertExpr D)
  | div (a b : CertExpr D)
  | rem (a b : CertExpr D)
  | sdiv (a b : CertExpr D)
  | srem (a b : CertExpr D)
  | band (a b : CertExpr D)
  | bor (w : Nat) (a b : CertExpr D)
  | bxor (w : Nat) (a b : CertExpr D)
  | shl (w : Nat) (a b : CertExpr D)
  | shr (w : Nat) (a b : CertExpr D)
  | wide (lo' hi' : Int) (a : CertExpr D)
  | var (k : Nat)
  | glob (g : D.Glob)
  | slot (t : D.Tab) (f : D.Feld t) (i : CertExpr D)
  deriving DecidableEq

/-- The range table, recomputed on the Lean side: M104 for the shapes,
    M102 (`0 ≤ l1`, `1 ≤ l2`) for `/` and `%`, the second sentence of SG-3
    (`1 ≤ l2 ∨ h2 ≤ -1`) for `sdiv`/`srem`, M137 (`0 ≤ l1`, `0 ≤ l2`, and the
    width `h < 2 ^ w` for `bor`/`bxor`) for bitwise and shifts. `none` means
    the print has no range at all -- a forged side condition lands here,
    not in a diagnostic.

    The CUT-4 arms consult the context through `ctxTyp` (variables), the
    declaration through `intVonTyp` (carrier types), and the resource context
    through `darf`/`gdarf` (guards). A `slot` index must recompute EXACTLY
    the generated index type `0 .. count - 1`: a bare literal is not an index
    until `wide` says so, and the table says so too.

    The bounds are written EXACTLY as in `Expr` (`Syntax.lean` §3): whatever
    `certRange` computes for a valid certificate is definitionally the index
    of the `Expr` term `zeugnis_sound` builds. -/
def certRange (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) : CertExpr D → Option (Int × Int)
  | .lit n => some (n, n)
  | .add a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, h1), some (l2, h2) => some (l1 + l2, h1 + h2)
    | _, _ => none
  | .sub a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, h1), some (l2, h2) => some (l1 - h2, h1 - l2)
    | _, _ => none
  | .neg a =>
    match certRange D Γ Λ a with
    | some (l1, h1) => some (-h1, -l1)
    | none => none
  | .mul a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, h1), some (l2, h2) =>
      some (imin (imin (l1 * l2) (l1 * h2)) (imin (h1 * l2) (h1 * h2)),
            imax (imax (l1 * l2) (l1 * h2)) (imax (h1 * l2) (h1 * h2)))
    | _, _ => none
  | .div a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, h1), some (l2, _h2) =>
      if 0 ≤ l1 ∧ 1 ≤ l2 then some (0, h1) else none
    | _, _ => none
  | .rem a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, _h1), some (l2, h2) =>
      if 0 ≤ l1 ∧ 1 ≤ l2 then some (0, h2 - 1) else none
    | _, _ => none
  | .sdiv a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, h1), some (l2, h2) =>
      if 1 ≤ l2 ∨ h2 ≤ -1 then some (-(betragMax l1 h1), betragMax l1 h1) else none
    | _, _ => none
  | .srem a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (_, _), some (l2, h2) =>
      if 1 ≤ l2 ∨ h2 ≤ -1 then some (-(betragMax l2 h2 - 1), betragMax l2 h2 - 1) else none
    | _, _ => none
  | .band a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, h1), some (l2, _h2) =>
      if 0 ≤ l1 ∧ 0 ≤ l2 then some (0, h1) else none
    | _, _ => none
  | .bor w a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, h1), some (l2, h2) =>
      if 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w then some (0, 2 ^ w - 1) else none
    | _, _ => none
  | .bxor w a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, h1), some (l2, h2) =>
      if 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w then some (0, 2 ^ w - 1) else none
    | _, _ => none
  | .shl w a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, h1), some (l2, h2) =>
      if 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < (w : Int)
      then some (0, h1 * 2 ^ h2.toNat) else none
    | _, _ => none
  | .shr w a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, h1), some (l2, h2) =>
      if 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < (w : Int)
      then some (0, h1) else none
    | _, _ => none
  | .wide lo' hi' a =>
    match certRange D Γ Λ a with
    | some (l1, h1) =>
      if lo' ≤ l1 ∧ h1 ≤ hi' then some (lo', hi') else none
    | none => none
  | .var k => ctxTyp Γ k
  | .glob g =>
    match intVonTyp (D.gtyp g) with
    | some (lo, hi) => if gdarf D g Λ then some (lo, hi) else none
    | none => none
  | .slot t f i =>
    match certRange D Γ Λ i, intVonTyp (D.typ t f) with
    | some (l, h), some (lo, hi) =>
      if l = 0 ∧ h = D.count t - 1 ∧ darf D t Λ then some (lo, hi) else none
    | _, _ => none

/-- Certificate validity: the printed claim `(lo, hi)` is exactly what the
    table recomputes. Decidable by construction wherever the world is
    concrete, so both acceptance and rejection of a print close by `decide`. -/
abbrev GueltigAbleitung (D : Deklaration) (Γ : Ctx) (Λ : List (Res D))
    (c : CertExpr D) (lo hi : Int) : Prop :=
  certRange D Γ Λ c = some (lo, hi)


end Gabbro.Grammatik
