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
import Grammatik.Syntax

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
  | grund _ => simp [intVonTyp] at h
  | never => simp [intVonTyp] at h
  | fl _ => simp [intVonTyp] at h
  | fnptr _ => simp [intVonTyp] at h
  | ptr _ _ => simp [intVonTyp] at h

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
        exact ⟨.hier, trivial⟩
      | bool => simp [ctxTyp] at h
      | opt _ => simp [ctxTyp] at h
      | sum _ => simp [ctxTyp] at h
      | grund _ => simp [ctxTyp] at h
      | never => simp [ctxTyp] at h
      | fl _ => simp [ctxTyp] at h
      | fnptr _ => simp [ctxTyp] at h
      | ptr _ _ => simp [ctxTyp] at h
    | succ k =>
      simp [ctxTyp] at h
      obtain ⟨x, _⟩ := ih k h
      exact ⟨.dort x, trivial⟩

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
  | shl (a b : CertExpr D)
  | shr (a b : CertExpr D)
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
  | .shl a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, h1), some (l2, h2) =>
      if 0 ≤ l1 ∧ 0 ≤ l2 then some (0, h1 * 2 ^ h2.toNat) else none
    | _, _ => none
  | .shr a b =>
    match certRange D Γ Λ a, certRange D Γ Λ b with
    | some (l1, h1), some (l2, _h2) =>
      if 0 ≤ l1 ∧ 0 ≤ l2 then some (0, h1) else none
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

/-- Soundness: a valid certificate IMPLIES the judgment -- there EXISTS an
    accepted derivation, the `Expr` term the grammar admits. The induction is
    over the certificate; each case hands the recomputed side conditions to
    the corresponding `Expr` constructor. (An `∃`, not the term itself: the
    judgment is the proposition that the derivation exists -- the witness-pair
    shape of S4/V5.) -/
theorem zeugnis_sound {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (c : CertExpr D) (lo hi : Int) (h : GueltigAbleitung D Γ Λ c lo hi) :
    ∃ _ : Expr D Γ Λ (.int lo hi), True := by
  induction c generalizing lo hi with
  | lit n =>
    simp only [GueltigAbleitung, certRange, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Expr.lit n, trivial⟩
  | add a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        obtain ⟨eb, _⟩ := ihb _ _ hb
        exact ⟨Expr.add ea eb, trivial⟩
  | sub a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        obtain ⟨eb, _⟩ := ihb _ _ hb
        exact ⟨Expr.sub ea eb, trivial⟩
  | neg a iha =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ea, _⟩ := iha _ _ ha
      exact ⟨Expr.neg ea, trivial⟩
  | mul a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        obtain ⟨eb, _⟩ := ihb _ _ hb
        exact ⟨Expr.mul ea eb, trivial⟩
  | div a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, _⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 1 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.div hc.1 hc.2 ea eb, trivial⟩
        · simp [hc] at h
  | rem a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, _⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 1 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.rem hc.1 hc.2 ea eb, trivial⟩
        · simp [hc] at h
  | sdiv a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 1 ≤ l2 ∨ h2 ≤ -1
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.sdiv hc ea eb, trivial⟩
        · simp [hc] at h
  | srem a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨_, _⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 1 ≤ l2 ∨ h2 ≤ -1
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.srem hc ea eb, trivial⟩
        · simp [hc] at h
  | band a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, _⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.band hc.1 hc.2 ea eb, trivial⟩
        · simp [hc] at h
  | bor w a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          obtain ⟨h0, h0', hw1, hw2⟩ := hc
          exact ⟨Expr.bor w h0 h0' hw1 hw2 ea eb, trivial⟩
        · simp [hc] at h
  | bxor w a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          obtain ⟨h0, h0', hw1, hw2⟩ := hc
          exact ⟨Expr.bxor w h0 h0' hw1 hw2 ea eb, trivial⟩
        · simp [hc] at h
  | shl a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.shl hc.1 hc.2 ea eb, trivial⟩
        · simp [hc] at h
  | shr a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange D Γ Λ b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, _⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.shr hc.1 hc.2 ea eb, trivial⟩
        · simp [hc] at h
  | wide lo' hi' a iha =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      simp only [ha] at h
      by_cases hc : lo' ≤ l1 ∧ h1 ≤ hi'
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        exact ⟨Expr.weiter hc.1 hc.2 ea, trivial⟩
      · simp [hc] at h
  | var k =>
    simp only [GueltigAbleitung, certRange] at h
    cases hk : ctxTyp Γ k with
    | none => simp [hk] at h
    | some p =>
      obtain ⟨lo', hi'⟩ := p
      simp only [hk, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨x, _⟩ := ctxTyp_var Γ k _ _ hk
      exact ⟨Expr.var x, trivial⟩
  | glob g =>
    simp only [GueltigAbleitung, certRange] at h
    cases ht : intVonTyp (D.gtyp g) with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨lo', hi'⟩ := p
      simp only [ht] at h
      by_cases hc : gdarf D g Λ
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have heq := intVonTyp_eq ht
        exact ⟨heq ▸ Expr.glob g hc, trivial⟩
      · simp [hc] at h
  | slot t f i ih =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange D Γ Λ i with
    | none =>
      cases ht : intVonTyp (D.typ t f) with
      | none => simp [ha, ht] at h
      | some _ => simp [ha, ht] at h
    | some p =>
      obtain ⟨l, h'⟩ := p
      cases ht : intVonTyp (D.typ t f) with
      | none => simp [ha, ht] at h
      | some q =>
        obtain ⟨lo', hi'⟩ := q
        simp only [ha, ht] at h
        by_cases hc : l = 0 ∧ h' = D.count t - 1 ∧ darf D t Λ
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ei, _⟩ := ih _ _ ha
          have heq := intVonTyp_eq ht
          obtain ⟨hc1, hc2, hc3⟩ := hc
          subst hc1
          subst hc2
          exact ⟨heq ▸ Expr.slot t f ei hc3, trivial⟩
        · simp [hc] at h

/-! ## The test world: one concrete declaration for the decide probes

    `decide` needs closed terms: it evaluates the table, and evaluation
    cannot look through an abstract `D`. So the probes below pin ONE world --
    one guarded global of `0 .. 7`, one guarded table with one int field of
    `0 .. 10` over eleven rows, one lock that guards both, one nullary
    procedure and one unary one. Every probe names this world explicitly;
    nothing about the soundness theorems depends on it. -/

/-- Nullary test signature: no params, no result, no reasons, no rights,
    no marks, no held locks. -/
def TestSig0 : Signatur Unit Unit Unit Empty :=
  ⟨[], none, 0, [], fun _ => false, fun _ => false, [], []⟩

/-- Unary test signature: one int param -- for the negative call probe. -/
def TestSig1 : Signatur Unit Unit Unit Empty :=
  ⟨[.int 0 5], none, 0, [], fun _ => false, fun _ => false, [], []⟩

/-- A one-glob, one-table, one-lock test world: every access is guarded. -/
def TestD : Deklaration where
  Tab := Unit
  count := fun _ => 11
  Feld := fun _ => Unit
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => true
  tabNr := fun _ => some ()
  Glob := Unit
  gtyp := fun _ => .int 0 7
  nutzlast := fun _ => []
  atomar := fun _ => true
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Unit
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  stufen := fun e => e.elim
  braucht := fun _ => [.inl ()]
  gbraucht := fun _ => [.inl ()]
  eigner := fun _ => []
  Fn := Bool
  sig := fun | false => 0 | true => 1
  sigNr := fun | 0 => TestSig0 | 1 => TestSig1 | _ => TestSig0
  eigner_nie_erzeugt := fun _ _ m _ _ => m.elim
  Inv := Empty
  traeger := fun e => e.elim
  invs := []
  Ax := Empty
  aparams := fun e => e.elim
  aerg := fun e => e.elim
  aschreibt := fun e => e.elim
  agschreibt := fun e => e.elim
  Reg := Empty
  rtyp := fun e => e.elim
  rklasse := fun e => e.elim
  spiegel := fun e => e.elim
  rzusage := fun e => e.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => i.elim
  ggeteilt_bewacht := fun g h => by simp at h

/-- Procedure contract: no result, holds nothing, produces nothing. -/
def TestV : Vertrag TestD :=
  ⟨fun _ => true, fun _ => true, none, 0, [], []⟩

/-- Value contract: returns an int in `1 .. 1`. -/
def TestVw : Vertrag TestD :=
  ⟨fun _ => true, fun _ => true, some (.int 1 1), 0, [], []⟩

/-- The nullary call fits the procedure contract at empty resources: no
    rights to check (both write maps are `false`), nothing consumed, and the
    held-lock check is vacuous in both directions over the empty lists. -/
theorem TestHp : RufPasst TestD TestV (TestD.signatur false) [] where
  hw := fun t h => by simp [Deklaration.signatur, TestD, TestSig0, TestSig1] at h
  hg := fun g h => by simp [Deklaration.signatur, TestD, TestSig0, TestSig1] at h
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh := fun L => iff_of_false List.not_mem_nil List.not_mem_nil

/-- Same fit for the unary callee: `RufPasst` never constrained the params,
    so the same vacuous proofs go through -- and the table still rejects the
    call, on `params = []`. -/
theorem TestHp1 : RufPasst TestD TestV (TestD.signatur true) [] where
  hw := fun t h => by simp [Deklaration.signatur, TestD, TestSig0, TestSig1] at h
  hg := fun g h => by simp [Deklaration.signatur, TestD, TestSig0, TestSig1] at h
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh := fun L => iff_of_false List.not_mem_nil List.not_mem_nil

/-! ## Witness pairs: acceptance and rejection, both by `decide` -/

/-- `1 + 2` printed as `(3, 3)`: Lean accepts the print. -/
example : GueltigAbleitung TestD [] [] (.add (.lit 1) (.lit 2)) 3 3 := by decide

/-- `5 / 2` printed as `(0, 5)`: nonneg dividend, positive divisor (M102). -/
example : GueltigAbleitung TestD [] [] (.div (.lit 5) (.lit 2)) 0 5 := by decide

/-- `5` widened to `0 .. 10`: a checked `weiter` in the safe direction. -/
example : GueltigAbleitung TestD [] [] (.wide 0 10 (.lit 5)) 0 10 := by decide

/-- MISMATCHED print: `1 + 2` claimed as `(0, 0)` -- provably not valid.
    This is the loud failure: no acceptance proof can be built from it. -/
example : ¬ GueltigAbleitung TestD [] [] (.add (.lit 1) (.lit 2)) 0 0 := by decide

/-- FORGED proof: `5 / 0` -- the divisor range admits zero, so the table
    yields no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.div (.lit 5) (.lit 0)) 0 5 := by decide

/-- FORGED widening: `20` claimed in `0 .. 10` -- outside, no certificate. -/
example : ¬ GueltigAbleitung TestD [] [] (.wide 0 10 (.lit 20)) 0 10 := by decide

/-! ### CUT-1 and CUT-2 probes: signed division, bitwise, shifts -/

/-- `7 sdiv 2` printed as `(-7, 7)`: the divisor excludes zero (SG-3, second sentence). -/
example : GueltigAbleitung TestD [] [] (.sdiv (.lit 7) (.lit 2)) (-7) 7 := by decide

/-- FORGED proof: `7 sdiv 0` -- same claim as above, but the divisor admits zero. -/
example : ¬ GueltigAbleitung TestD [] [] (.sdiv (.lit 7) (.lit 0)) (-7) 7 := by decide

/-- `7 srem 2` printed as `(-1, 1)`: the remainder range comes from the DIVISOR. -/
example : GueltigAbleitung TestD [] [] (.srem (.lit 7) (.lit 2)) (-1) 1 := by decide

/-- FORGED proof: `7 srem 0` -- same claim as above, but the divisor admits zero. -/
example : ¬ GueltigAbleitung TestD [] [] (.srem (.lit 7) (.lit 0)) (-1) 1 := by decide

/-- `6 band 3` printed as `(0, 6)`: both operands nonneg (M137). -/
example : GueltigAbleitung TestD [] [] (.band (.lit 6) (.lit 3)) 0 6 := by decide

/-- FORGED proof: a negative operand under `band` -- no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.band (.sub (.lit 0) (.lit 1)) (.lit 3)) 0 0 := by decide

/-- `6 bor 3` in width 3 printed as `(0, 7)`: both bounds fit under `2 ^ 3`. -/
example : GueltigAbleitung TestD [] [] (.bor 3 (.lit 6) (.lit 3)) 0 7 := by decide

/-- FORGED proof: width 2 does not hold `6` -- the width side condition fails. -/
example : ¬ GueltigAbleitung TestD [] [] (.bor 2 (.lit 6) (.lit 3)) 0 3 := by decide

/-- `6 bxor 3` in width 3 printed as `(0, 7)`: same width rule as `bor`. -/
example : GueltigAbleitung TestD [] [] (.bxor 3 (.lit 6) (.lit 3)) 0 7 := by decide

/-- FORGED proof: width 2 does not hold `6` under `bxor` either. -/
example : ¬ GueltigAbleitung TestD [] [] (.bxor 2 (.lit 6) (.lit 3)) 0 3 := by decide

/-- `3 shl 2` printed as `(0, 12)`: `3 * 2 ^ 2`, both operands nonneg. -/
example : GueltigAbleitung TestD [] [] (.shl (.lit 3) (.lit 2)) 0 12 := by decide

/-- FORGED proof: a negative value shifted -- no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.shl (.sub (.lit 0) (.lit 1)) (.lit 2)) 0 0 := by decide

/-- `12 shr 2` printed as `(0, 12)`: a right shift never widens (M137). -/
example : GueltigAbleitung TestD [] [] (.shr (.lit 12) (.lit 2)) 0 12 := by decide

/-- FORGED proof: a negative value shifted right -- no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.shr (.sub (.lit 0) (.lit 1)) (.lit 2)) 0 0 := by decide

/-! ### CUT-4 probes: variables and carrier accesses -/

/-- Variable `0` in `[3 .. 3]` printed as `(3, 3)`: the context lookup hits. -/
example : GueltigAbleitung TestD [.int 3 3] [] (.var 0) 3 3 := by decide

/-- MISMATCHED print: variable `0` claimed as `(0, 0)` -- the lookup says
    `(3, 3)`, so the claim is provably not valid. -/
example : ¬ GueltigAbleitung TestD [.int 3 3] [] (.var 0) 0 0 := by decide

/-- DANGLING print: variable `5` in a one-entry context -- no lookup, no range. -/
example : ¬ GueltigAbleitung TestD [.int 3 3] [] (.var 5) 3 3 := by decide

/-- MISTYPED print: variable `0` of type `bool` claimed as an int range --
    the lookup says `none` for non-int types. -/
example : ¬ GueltigAbleitung TestD [.bool] [] (.var 0) 0 0 := by decide

/-- The global printed as `(0, 7)`: its declared type, under the held guard. -/
example : GueltigAbleitung TestD [] [Res.held ()] (.glob ()) 0 7 := by decide

/-- FORGED guard: the same global with empty hands -- the guard fails, so the
    table yields no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.glob ()) 0 7 := by decide

/-- A variable under arithmetic: `x + 1` with `x : 3 .. 3` is `(4, 4)` --
    reads lift through the closed shapes. -/
example : GueltigAbleitung TestD [.int 3 3] [Res.held ()] (.add (.var 0) (.lit 1)) 4 4 := by decide

/-- The place read: `T.slots[i].f` with `i` widened to the generated index
    type `0 .. 10`, under the held guard -- printed as the field `(0, 10)`. -/
example : GueltigAbleitung TestD [] [Res.held ()]
    (.slot () () (.wide 0 10 (.lit 3))) 0 10 := by decide

/-- FORGED index: a bare `3` is not of index type `0 .. 10` -- without the
    widening the slot has no range. -/
example : ¬ GueltigAbleitung TestD [] [Res.held ()]
    (.slot () () (.lit 3)) 0 10 := by decide

/-- FORGED guard: the widened index is right, but the hands are empty. -/
example : ¬ GueltigAbleitung TestD [] []
    (.slot () () (.wide 0 10 (.lit 3))) 0 10 := by decide

/-- End to end: a valid print YIELDS an accepted derivation. -/
example : ∃ _ : Expr TestD [] [] (.int 3 3), True :=
  zeugnis_sound (D := TestD) (Γ := []) (Λ := []) (.add (.lit 1) (.lit 2)) 3 3 (by decide)

/-- End to end over a read: a valid variable print yields its derivation. -/
example : ∃ _ : Expr TestD [.int 3 3] [] (.int 3 3), True :=
  zeugnis_sound (D := TestD) (.var 0) 3 3 (by decide)

/-! ## Blocks: straight-line statements over int bindings (CUT-5)

    `CertBlock` is the printed certificate for a `Block`: `bind` extends the
    context by the RECOMPUTED range, `call` covers nullary callees (the
    `params = []` and `gruende = 0` checks recomputed; `RufPasst` travels as
    proof -- see the CUT-5 remainder above), `ret`/`retWert` check the result
    shape and recompute the linear balance `Λ.Perm V.ende`. -/

inductive CertBlock (D : Deklaration) (V : Vertrag D) :
    Ctx → List (Res D) → List (Res D) → Type where
  | nil : CertBlock D V Γ Λ Λ
  | bind (e : CertExpr D) (lo hi : Int) (rest : CertBlock D V (.int lo hi :: Γ) Λ Λ') :
      CertBlock D V Γ Λ Λ'
  | call (f : D.Fn) (hp : RufPasst D V (D.signatur f) Λ)
      (rest : CertBlock D V Γ (nach D f Λ) Λ') : CertBlock D V Γ Λ Λ'
  | ret : CertBlock D V Γ Λ Λ
  | retWert (e : CertExpr D) (lo hi : Int) : CertBlock D V Γ Λ Λ

/-- Block validity: the structural checks the table recomputes -- sub-ranges,
    the nullary-call shape, the result shape, the linear balance. Decidable
    wherever the world is concrete (see `decGueltigBlock` below), so block
    acceptance and rejection both close by `decide`. -/
def certBlockGueltig (D : Deklaration) (V : Vertrag D) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : CertBlock D V Γ Λ Λ' → Prop
  | .nil => True
  | .bind e lo hi rest =>
    certRange D Γ Λ e = some (lo, hi) ∧ certBlockGueltig D V (.int lo hi :: Γ) Λ Λ' rest
  | .call f _ rest =>
    D.params f = [] ∧ D.gruende f = 0 ∧ certBlockGueltig D V Γ (nach D f Λ) Λ' rest
  | .ret => V.erg = none ∧ Λ.Perm V.ende
  | .retWert e lo hi =>
    V.erg = some (.int lo hi) ∧ certRange D Γ Λ e = some (lo, hi) ∧ Λ.Perm V.ende

/-- The validity predicate as `Decidable`, by structural recursion: each arm
    restates its equation, so typeclass search closes it from the pieces
    (`haveI` carries the tail). -/
instance decGueltigBlock (D : Deklaration) (V : Vertrag D) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (b : CertBlock D V Γ Λ Λ') :
    Decidable (certBlockGueltig D V Γ Λ Λ' b) :=
  match b with
  | .nil => inferInstanceAs (Decidable True)
  | .bind e lo hi rest =>
    haveI := decGueltigBlock D V (.int lo hi :: Γ) Λ Λ' rest
    inferInstanceAs
      (Decidable (certRange D Γ Λ e = some (lo, hi) ∧
        certBlockGueltig D V (.int lo hi :: Γ) Λ Λ' rest))
  | .call f _ rest =>
    haveI := decGueltigBlock D V Γ (nach D f Λ) Λ' rest
    inferInstanceAs
      (Decidable (D.params f = [] ∧ D.gruende f = 0 ∧
        certBlockGueltig D V Γ (nach D f Λ) Λ' rest))
  | .ret => inferInstanceAs (Decidable (V.erg = none ∧ Λ.Perm V.ende))
  | .retWert e lo hi =>
    inferInstanceAs
      (Decidable (V.erg = some (.int lo hi) ∧ certRange D Γ Λ e = some (lo, hi) ∧
        Λ.Perm V.ende))

/-- Block soundness: a valid block certificate IMPLIES the judgment -- there
    EXISTS an accepted `Block`. `bind` elaborates the bound expression through
    `zeugnis_sound` and extends the context; `call` forwards the carried
    `RufPasst` with the recomputed nullary shape; `ret`/`retWert` close the
    block with the recomputed balance. -/
theorem block_sound {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (b : CertBlock D V Γ Λ Λ') :
    certBlockGueltig D V Γ Λ Λ' b → ∃ _ : Block D V l Γ Λ Λ', True := by
  induction b with
  | nil => intro _; exact ⟨Block.nil, trivial⟩
  | bind e lo hi rest ih =>
    intro h
    simp only [certBlockGueltig] at h
    obtain ⟨he, hr⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi he
    obtain ⟨blk, _⟩ := ih hr
    exact ⟨Block.bind ee blk, trivial⟩
  | call f hp rest ih =>
    intro h
    simp only [certBlockGueltig] at h
    obtain ⟨hpar, hgr, hr⟩ := h
    obtain ⟨blk, _⟩ := ih hr
    exact ⟨Block.cons (Stmt.call f (by rw [hpar]; exact Args.nil) hp hgr) blk, trivial⟩
  | ret =>
    intro h
    simp only [certBlockGueltig] at h
    obtain ⟨he, hΛ⟩ := h
    exact ⟨Block.cons (Stmt.ret (by rw [he]; exact ErgExpr.keine) hΛ) Block.nil, trivial⟩
  | retWert e lo hi =>
    intro h
    simp only [certBlockGueltig] at h
    obtain ⟨he, hrng, hΛ⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi hrng
    exact ⟨Block.cons (Stmt.ret (by rw [he]; exact ErgExpr.wert ee) hΛ) Block.nil, trivial⟩

/-! ### CUT-5 probes: bind, call, return -/

/-- A binding that ends the block without returning: `nil` is unconditionally
    valid -- the checks live in the statements, not in the sequencing. -/
example : certBlockGueltig TestD TestV [] [] []
    (.bind (.lit 1) 1 1 .nil) := by decide

/-- `return` with empty hands: the procedure contract holds nothing, so the
    empty balance is exact. -/
example : certBlockGueltig TestD TestV [] [] [] (.ret) := by decide

/-- BROKEN balance: a held lock with nowhere to return it -- provably no
    certificate. This is the linear failure, loud. -/
example : ¬ certBlockGueltig TestD TestV [] [Res.held ()] [Res.held ()] (.ret) := by decide

/-- `let x = 1; return x`: the binding recomputes `(1, 1)`, the return reads
    variable `0` at `(1, 1)` against a matching contract. -/
example : certBlockGueltig TestD TestVw [] [] []
    (.bind (.lit 1) 1 1 (.retWert (.var 0) 1 1)) := by decide

/-- MISMATCHED return: `x` is `(1, 1)`, claimed as `(2, 2)`. -/
example : ¬ certBlockGueltig TestD TestVw [] [] []
    (.bind (.lit 1) 1 1 (.retWert (.var 0) 2 2)) := by decide

/-- MISMATCHED binding: `1` claimed as `(9, 9)` -- the tail never gets its
    context, because the head already fails. -/
example : ¬ certBlockGueltig TestD TestVw [] [] []
    (.bind (.lit 1) 9 9 (.retWert (.var 0) 1 1)) := by decide

/-- The nullary call, then `return`: params empty and no reasons, so the
    table accepts and the balance holds behind it. -/
example : certBlockGueltig TestD TestV [] [] [] (.call false TestHp .ret) := by decide

/-- A call WITH a param is no nullary call: `RufPasst` goes through, but the
    `params = []` check fails -- the certificate is honestly rejected. -/
example : ¬ certBlockGueltig TestD TestV [] [] []
    (.call true TestHp1 .ret) := by decide

/-- End to end: a valid block print YIELDS an accepted block. -/
example : ∃ _ : Block TestD TestV false [] [] [], True :=
  block_sound (.call false TestHp .ret) (by decide)

#eval certRange TestD [] [] (.mul (.lit 2) (.lit 3))
#eval certRange TestD [] [] (.div (.lit 5) (.lit 0))
#eval certRange TestD [] [] (.sdiv (.lit 7) (.lit 2))
#eval certRange TestD [] [] (.bor 3 (.lit 6) (.lit 3))
#eval certRange TestD [.int 3 3] [] (.var 0)
#eval certRange TestD [] [Res.held ()] (.glob ())

#print axioms zeugnis_sound
#print axioms block_sound

/-! ## CUT-3 design rows: floats, options, sums, grounds, quantifiers, `reaches`

    DESIGN ONLY. Each constructor below mirrors the `Expr` constructor of the
    same shape, but every proof field travels as PLAIN DATA (bounds, indices,
    table numbers, case lists) and every side condition the table CAN recompute
    is a `def` (`flVonTyp`, `ctxFlTyp`, `certFlTyp`, `certCut3Ok` with its two
    `Bool` helpers), with `Decidable` instances wherever the world is concrete.
    What the table CANNOT recompute is said out loud per arm; the soundness
    cases are proved below as `cut3_sound` (a valid CUT-3 print elaborates to
    the corresponding `Expr`), with the quantifier bodies as the explicit
    `Cut3Body` hypothesis. -/

/-- The float bounds of a type, if it has any. Reads of non-float carriers
    land on `none` -- booked, not faked (mirror of `intVonTyp`). -/
def flVonTyp : Ty → Option ((Int × Int) × (Int × Int))
  | .fl lo hi => some (lo, hi)
  | _ => none

/-- The float bounds of the `k`-th variable of `Γ`, if it is float-typed: a de
    Bruijn lookup that says `none` for out-of-range indices and non-float types
    (mirror of `ctxTyp`). The `Var` witness is rebuilt by the booked soundness
    case, never trusted from the print. -/
def ctxFlTyp : Ctx → Nat → Option ((Int × Int) × (Int × Int))
  | τ :: _, 0 => flVonTyp τ
  | _ :: Γ, k + 1 => ctxFlTyp Γ k
  | [], _ => none

/-- Float reads as plain data: variable, global, and place reads at `.fl`
    type. The index of a `slotFl` travels as an int certificate and must
    recompute EXACTLY the generated index type `0 .. count - 1` (mirror of the
    `slot` arm of `certRange`); the float bounds themselves come from the
    declaration, never from the print. -/
inductive CertFl (D : Deklaration) where
  | varFl (k : Nat)
  | globFl (g : D.Glob)
  | slotFl (t : D.Tab) (f : D.Feld t) (i : CertExpr D)

/-- The float table, recomputed on the Lean side (mirror of the CUT-4 arms of
    `certRange`): context lookup for variables, declared type plus recomputed
    `gdarf` guard for globals, generated index shape plus declared field type
    plus recomputed `darf` guard for places. `none` means the print has no
    float bounds at all. -/
def certFlTyp (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) :
    CertFl D → Option ((Int × Int) × (Int × Int))
  | .varFl k => ctxFlTyp Γ k
  | .globFl g =>
    match flVonTyp (D.gtyp g) with
    | some q => if gdarf D g Λ then some q else none
    | none => none
  | .slotFl t f i =>
    match certRange D Γ Λ i, flVonTyp (D.typ t f) with
    | some (l, h), some q =>
      if l = 0 ∧ h = D.count t - 1 ∧ darf D t Λ then some q else none
    | _, _ => none

/-- The CUT-3 certificate shapes as plain data (mirror of the `CertExpr`
    docstring): float comparisons over `CertFl` operands; option introduction
    (`none` carries its bound, `some` its index certificate plus bound) and
    elimination (`istSome` nests the scrutinised option print); sum
    introduction (`fall` carries the FULL case list, the case index, and the
    payload print -- `none` for a caseless arm, `some e` for a `zahl` arm);
    ground introduction (`grund` carries the reason count and the case);
    quantifiers (the bound variable is the generated index -- named by the
    table, not the print -- so only the guard travels, and the body
    elaboration is BOOKED); `reaches` (the field equation, two index
    certificates, the guard). -/
inductive CertCut3 (D : Deklaration) where
  | fllt (a b : CertFl D)
  | flle (a b : CertFl D)
  | none (n : Int)
  | some (e : CertExpr D) (n : Int)
  | istSome (o : CertCut3 D) (n : Int)
  | fall (cs : List (Option (Int × Int))) (i : Nat) (p : Option (CertExpr D))
  | grund (n r : Nat)
  | forallSlots (t : D.Tab)
  | existsSlots (t : D.Tab)
  | reaches (t : D.Tab) (f : D.Feld t) (a b : CertExpr D)

/-- Which option bound a CUT-3 print claims, if it is an option introduction:
    `none`/`some` name their bound as data; every other shape answers `false`.
    A nested `istSome` under `istSome` is correctly rejected -- the scrutinee
    of `istSome` must INTRODUCE the option, and `Bool` has no bound. -/
def certCut3IsOpt : CertCut3 D → Int → Bool
  | .none m, n => decide (m = n)
  | .some _ m, n => decide (m = n)
  | _, _ => false

/-- The sum payload check, as a `Bool`: the case the list names at `i` and the
    payload the print carries must agree -- caseless with absent, `zahl` with a
    certificate that recomputes EXACTLY the cased range. Anything else (an
    out-of-range index, a shape mismatch) is `false`, not a diagnostic. -/
def certCut3PayloadOk (D : Deklaration) (Γ : Ctx) (Λ : List (Res D))
    (slot : Option (Option (Int × Int))) (p : Option (CertExpr D)) : Bool :=
  match slot, p with
  | some none, none => true
  | some (some (lo, hi)), some e => decide (certRange D Γ Λ e = some (lo, hi))
  | _, _ => false

/-- CUT-3 validity, recomputed on the Lean side (mirror of the `certRange`
    arms): float comparisons need float bounds on BOTH operands; `some` needs
    the index shape `0 .. n - 1`; `istSome` needs a valid option print AT that
    bound; `fall` needs the index inside the case list plus the payload check;
    `grund` needs the case inside the reason count; quantifiers and `reaches`
    recompute the guards, `reaches` additionally the field equation (`option
    index into Self`) and both endpoint index shapes. -/
def certCut3Ok (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) : CertCut3 D → Prop
  | .fllt a b => certFlTyp D Γ Λ a ≠ none ∧ certFlTyp D Γ Λ b ≠ none
  | .flle a b => certFlTyp D Γ Λ a ≠ none ∧ certFlTyp D Γ Λ b ≠ none
  | .none _ => True
  | .some e n => certRange D Γ Λ e = some (0, n - 1)
  | .istSome o n => certCut3Ok D Γ Λ o ∧ certCut3IsOpt o n = true
  | .fall cs i p => i < cs.length ∧ certCut3PayloadOk D Γ Λ cs[i]? p = true
  | .grund n r => r < n
  | .forallSlots t => darf D t Λ
  | .existsSlots t => darf D t Λ
  | .reaches t f a b =>
    D.typ t f = .opt (D.count t) ∧ certRange D Γ Λ a = some (0, D.count t - 1) ∧
      certRange D Γ Λ b = some (0, D.count t - 1) ∧ darf D t Λ

/-- CUT-3 validity as `Decidable`, by structural recursion (mirror of
    `decGueltigBlock`): each arm restates its equation, so typeclass search
    closes it from the pieces (`haveI` carries the scrutinee tail). -/
instance decCut3Ok (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) (c : CertCut3 D) :
    Decidable (certCut3Ok D Γ Λ c) :=
  match c with
  | .fllt a b =>
    inferInstanceAs (Decidable (certFlTyp D Γ Λ a ≠ none ∧ certFlTyp D Γ Λ b ≠ none))
  | .flle a b =>
    inferInstanceAs (Decidable (certFlTyp D Γ Λ a ≠ none ∧ certFlTyp D Γ Λ b ≠ none))
  | .none _ => inferInstanceAs (Decidable True)
  | .some e n =>
    inferInstanceAs (Decidable (certRange D Γ Λ e = some (0, n - 1)))
  | .istSome o n =>
    haveI := decCut3Ok D Γ Λ o
    inferInstanceAs (Decidable (certCut3Ok D Γ Λ o ∧ certCut3IsOpt o n = true))
  | .fall cs i p =>
    inferInstanceAs
      (Decidable (i < cs.length ∧ certCut3PayloadOk D Γ Λ cs[i]? p = true))
  | .grund n r => inferInstanceAs (Decidable (r < n))
  | .forallSlots t => inferInstanceAs (Decidable (darf D t Λ))
  | .existsSlots t => inferInstanceAs (Decidable (darf D t Λ))
  | .reaches t f a b =>
    inferInstanceAs
      (Decidable (D.typ t f = .opt (D.count t) ∧
        certRange D Γ Λ a = some (0, D.count t - 1) ∧
        certRange D Γ Λ b = some (0, D.count t - 1) ∧ darf D t Λ))

/-! ## CUT-4 remainder design rows: `durch`, `ptrOf`, `fnref`

    DESIGN rows plus soundness. Pointer and function types carry no range, so
    the range table has nothing to recompute -- validity here is the SHAPE the
    table CAN check: the table-number equation, the generated index shape, the
    guard. The soundness cases are proved below as `cut4_sound` (a valid
    remainder print elaborates to the corresponding `Expr`), with the `durch`
    pointer as the explicit `Cut4Ptr` hypothesis. -/

/-- The CUT-4 remainder as plain data: `ptrOf` names its table and number;
    `fnref` its function and signature number; `durch` the carrier, the field,
    the table number the pointer claims, and the index certificate. The pointer
    TERM of `durch` is BOOKED (its elaboration is a future soundness case, like
    everything in this section): the arm checks the capability the pointer
    NAMES, not the pointer itself. -/
inductive CertCut4 (D : Deklaration) where
  | ptrOf (t : D.Tab) (n : Nat) (rw : Bool)
  | fnref (f : D.Fn) (n : Nat)
  | durch (t : D.Tab) (f : D.Feld t) (n : Nat) (i : CertExpr D)

/-- CUT-4 remainder validity: `ptrOf` recomputes the table-number equation;
    `fnref` the signature equation; `durch` the table-number equation, the
    generated index shape, and the guard. The field type is NOT constrained --
    `durch` reads `D.typ t f` whatever it is, exactly as `Expr.durch` does. -/
def certCut4Ok (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) : CertCut4 D → Prop
  | .ptrOf t n _ => D.tabNr n = some t
  | .fnref f n => D.sig f = n
  | .durch t _f n i =>
    D.tabNr n = some t ∧ certRange D Γ Λ i = some (0, D.count t - 1) ∧ darf D t Λ

/-- CUT-4 remainder validity as `Decidable` (mirror of `decGueltigBlock`). -/
instance decCut4Ok (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) (c : CertCut4 D) :
    Decidable (certCut4Ok D Γ Λ c) :=
  match c with
  | .ptrOf t n _ => inferInstanceAs (Decidable (D.tabNr n = some t))
  | .fnref f n => inferInstanceAs (Decidable (D.sig f = n))
  | .durch t _f n i =>
    inferInstanceAs
      (Decidable (D.tabNr n = some t ∧ certRange D Γ Λ i = some (0, D.count t - 1) ∧
        darf D t Λ))

/-! ## CUT-5 remainder design rows: calls WITH arguments, carrying `RufPasst`

    DESIGN rows plus soundness. The existing `CertBlock.call` covers nullary
    callees; the arms below generalise the recomputed shape from `params = []`
    to `(D.params f).length = nargs` (and `(D.sigNr n).params.length = nargs`
    through a pointer), keep `gruende = 0` recomputed, and carry `RufPasst` AS
    PROOF -- the honest shrink the CUT-5 remainder above books: it quantifies
    over the arbitrary carrier types, so no range table can recompute it.
    Each argument's elaboration travels as the explicit `Block5Args`
    hypothesis of `block5_sound` below (a valid remainder block elaborates to
    the corresponding `Block`); the `bindCallElse` error branch has no arm
    and stays BOOKED. -/

/-- Call certificates with arguments: `callArgs` names the callee and its
    argument COUNT (each argument's type is BOOKED -- `CertExpr` covers the int
    fragment only, and `params` ranges over arbitrary `Ty`); `callInd` the same
    through a signature number; `bindCall` additionally the claimed result type
    (checked against `D.erg`) and extends the context behind it. Every arm
    carries the call's `RufPasst` as proof and forwards it, exactly as
    `CertBlock.call` does. -/
inductive CertBlock5 (D : Deklaration) (V : Vertrag D) :
    Ctx → List (Res D) → List (Res D) → Type where
  | nil : CertBlock5 D V Γ Λ Λ
  | callArgs (f : D.Fn) (nargs : Nat) (hp : RufPasst D V (D.signatur f) Λ)
      (rest : CertBlock5 D V Γ (nach D f Λ) Λ') : CertBlock5 D V Γ Λ Λ'
  | callInd (n nargs : Nat) (hp : RufPasst D V (D.sigNr n) Λ)
      (rest : CertBlock5 D V Γ (nachSig D (D.sigNr n) Λ) Λ') :
      CertBlock5 D V Γ Λ Λ'
  | bindCall (f : D.Fn) (nargs : Nat) (τ : Ty) (hp : RufPasst D V (D.signatur f) Λ)
      (rest : CertBlock5 D V (τ :: Γ) (nach D f Λ) Λ') : CertBlock5 D V Γ Λ Λ'

/-- CUT-5 remainder validity: the argument-count shape, the result shape, the
    reason-freedom `gruende = 0`, structurally behind the call (mirror of the
    `call` arm of `certBlockGueltig`, with `params = []` generalised to the
    counted shape). The carried `RufPasst` is forwarded, never recomputed. -/
def certBlock5Ok (D : Deklaration) (V : Vertrag D) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : CertBlock5 D V Γ Λ Λ' → Prop
  | .nil => True
  | .callArgs f nargs _ rest =>
    (D.params f).length = nargs ∧ D.gruende f = 0 ∧
      certBlock5Ok D V Γ (nach D f Λ) Λ' rest
  | .callInd n nargs _ rest =>
    (D.sigNr n).params.length = nargs ∧ (D.sigNr n).gruende = 0 ∧
      certBlock5Ok D V Γ (nachSig D (D.sigNr n) Λ) Λ' rest
  | .bindCall f nargs τ _ rest =>
    (D.params f).length = nargs ∧ D.erg f = some τ ∧ D.gruende f = 0 ∧
      certBlock5Ok D V (τ :: Γ) (nach D f Λ) Λ' rest

/-- CUT-5 remainder validity as `Decidable`, by structural recursion (mirror of
    `decGueltigBlock`). -/
instance decBlock5Ok (D : Deklaration) (V : Vertrag D) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (b : CertBlock5 D V Γ Λ Λ') :
    Decidable (certBlock5Ok D V Γ Λ Λ' b) :=
  match b with
  | .nil => inferInstanceAs (Decidable True)
  | .callArgs f nargs _ rest =>
    haveI := decBlock5Ok D V Γ (nach D f Λ) Λ' rest
    inferInstanceAs
      (Decidable ((D.params f).length = nargs ∧ D.gruende f = 0 ∧
        certBlock5Ok D V Γ (nach D f Λ) Λ' rest))
  | .callInd n nargs _ rest =>
    haveI := decBlock5Ok D V Γ (nachSig D (D.sigNr n) Λ) Λ' rest
    inferInstanceAs
      (Decidable ((D.sigNr n).params.length = nargs ∧ (D.sigNr n).gruende = 0 ∧
        certBlock5Ok D V Γ (nachSig D (D.sigNr n) Λ) Λ' rest))
  | .bindCall f nargs τ _ rest =>
    haveI := decBlock5Ok D V (τ :: Γ) (nach D f Λ) Λ' rest
    inferInstanceAs
      (Decidable ((D.params f).length = nargs ∧ D.erg f = some τ ∧ D.gruende f = 0 ∧
        certBlock5Ok D V (τ :: Γ) (nach D f Λ) Λ' rest))

/-! ## CUT-3 soundness: floats, options, sums, grounds, quantifiers, `reaches`

    Proved as `cut3_sound` below, with the `certFl_sound` helper for float
    reads (`flVonTyp_eq`, `ctxFlTyp_var` mirror `intVonTyp_eq`, `ctxTyp_var`).
    Every arm elaborates to the `Expr` constructor of the same shape; the
    result type varies per arm, so the statement is `∃ τ, Expr ... τ`.
    The two quantifier arms take the body as an explicit hypothesis
    (`Cut3Body`): the certificate carries the guard only, so the body
    elaboration is the remaining booked piece -- named here as data, not
    faked with an invented body. -/

/-- The float bounds of a type, if it has any: a `some` came from a `.fl`
    type (mirror of `intVonTyp_eq`). -/
theorem flVonTyp_eq {τ : Ty} {lo hi : Int × Int}
    (h : flVonTyp τ = some (lo, hi)) : τ = .fl lo hi := by
  cases τ with
  | int _ _ => simp [flVonTyp] at h
  | bool => simp [flVonTyp] at h
  | opt _ => simp [flVonTyp] at h
  | sum _ => simp [flVonTyp] at h
  | grund _ => simp [flVonTyp] at h
  | never => simp [flVonTyp] at h
  | fl lo' hi' =>
    simp [flVonTyp] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | fnptr _ => simp [flVonTyp] at h
  | ptr _ _ => simp [flVonTyp] at h

/-- What `ctxFlTyp` promises: a `some` names a variable that EXISTS (mirror
    of `ctxTyp_var`). The `Var` witness is rebuilt here, never trusted from
    the print. -/
theorem ctxFlTyp_var (Γ : Ctx) (k : Nat) (lo hi : Int × Int)
    (h : ctxFlTyp Γ k = some (lo, hi)) : ∃ _ : Var Γ (.fl lo hi), True := by
  induction Γ generalizing k with
  | nil =>
    cases k <;> simp [ctxFlTyp] at h
  | cons τ Γ ih =>
    cases k with
    | zero =>
      cases τ with
      | int _ _ => simp [ctxFlTyp, flVonTyp] at h
      | bool => simp [ctxFlTyp, flVonTyp] at h
      | opt _ => simp [ctxFlTyp, flVonTyp] at h
      | sum _ => simp [ctxFlTyp, flVonTyp] at h
      | grund _ => simp [ctxFlTyp, flVonTyp] at h
      | never => simp [ctxFlTyp, flVonTyp] at h
      | fl lo' hi' =>
        simp [ctxFlTyp, flVonTyp] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨.hier, trivial⟩
      | fnptr _ => simp [ctxFlTyp, flVonTyp] at h
      | ptr _ _ => simp [ctxFlTyp, flVonTyp] at h
    | succ k =>
      simp [ctxFlTyp] at h
      obtain ⟨x, _⟩ := ih k h
      exact ⟨.dort x, trivial⟩

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
    | fall _ _ _ => simp [certCut3IsOpt] at hi
    | grund _ _ => simp [certCut3IsOpt] at hi
    | forallSlots _ => simp [certCut3IsOpt] at hi
    | existsSlots _ => simp [certCut3IsOpt] at hi
    | reaches _ _ _ _ => simp [certCut3IsOpt] at hi
  | fall cs i p =>
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
          exact ⟨.sum cs, Expr.fall cs ⟨i, hi⟩ (hget'.symm ▸ NutzlastExpr.keine),
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
          exact ⟨.sum cs, Expr.fall cs ⟨i, hi⟩ (hget'.symm ▸ NutzlastExpr.zahl ee),
            trivial⟩
  | grund n r =>
    simp only [certCut3Ok] at h
    exact ⟨.grund n, Expr.grund n ⟨r, h⟩, trivial⟩
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
  cut3_sound (.fall [some (0, 0)] 0 (some (.lit 0))) () (by decide)

/-- The caseless arm: `fall` at index `0` with no payload. -/
example : ∃ τ, ∃ _ : Expr TestD [] [] τ, True :=
  cut3_sound (.fall [none] 0 none) () (by decide)

/-- FORGED payload: the `zahl` arm carries `1`, cased at `(0, 0)`. -/
example : ¬ certCut3Ok TestD [] []
    (.fall [some (0, 0)] 0 (some (.lit 1))) := by decide

/-- `grund 1 of 2` elaborates to `Expr.grund`. -/
example : ∃ τ, ∃ _ : Expr TestD [] [] τ, True :=
  cut3_sound (.grund 2 1) () (by decide)

/-- The quantifier guard, then `return`: `forallSlots` over the guarded
    table elaborates behind the supplied body. -/
example : ∃ τ, ∃ _ : Expr TestD [] [Res.held ()] τ, True :=
  cut3_sound (.forallSlots ()) Expr.wahr (by decide)

/-- Same guard, existential half. -/
example : ∃ τ, ∃ _ : Expr TestD [] [Res.held ()] τ, True :=
  cut3_sound (.existsSlots ()) Expr.wahr (by decide)

/-- FORGED payload: `some 1` at bound `1` claims the index shape `0 .. 0`,
    but the payload recomputes `(1, 1)` -- provably not valid. -/
example : ¬ certCut3Ok TestD [] [] (.some (.lit 1) 1) := by decide

/-- FORGED ground: case `2` of `2` reasons is out of range (`r < n` fails). -/
example : ¬ certCut3Ok TestD [] [] (.grund 2 2) := by decide

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
  | .durch _ _ n _ => Σ rw : Bool, Expr D Γ Λ (.ptr n rw)
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
  | durch t f n i =>
    simp only [certCut4Ok] at h
    obtain ⟨ht, hrng, hL⟩ := h
    obtain ⟨rw, p⟩ := s
    obtain ⟨ei, _⟩ := zeugnis_sound i 0 (D.count t - 1) hrng
    exact ⟨D.typ t f, Expr.durch p t ht f ei hL, trivial⟩

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
  cut4_sound (.durch () () 0 (.wide 0 10 (.lit 3)))
    ⟨true, Expr.ptrOf () 0 rfl true⟩ (by decide)

/-- FORGED signature: the nullary function claimed at signature `1` -- the
    signature equation fails, so the print is provably not valid. -/
example : ¬ certCut4Ok TestD [] [] (.fnref false 1) := by decide

/-- FORGED index: a bare `3` is not of index type `0 .. 10` -- without the
    widening the `durch` has no validity. -/
example : ¬ certCut4Ok TestD [] [Res.held ()]
    (.durch () () 0 (.lit 3)) := by decide

/-- FORGED guard: the widened index is right, but the hands are empty. -/
example : ¬ certCut4Ok TestD [] []
    (.durch () () 0 (.wide 0 10 (.lit 3))) := by decide

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
