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
    CUT-3 floats, options, sums, grounds, quantifiers, `reaches`: STILL BOOKED.
    CUT-4 variables and carrier accesses: COVERED below for the int fragment --
      name reads (`var`, de Bruijn index against `Γ`), global reads (`glob`,
      type from `D.gtyp`, guard `gdarf` recomputed), place reads (`slot`,
      index shape `0 .. count - 1` plus field type plus guard `darf`
      recomputed). Each with certRange arms, `GueltigAbleitung` side
      conditions, soundness cases, pos/neg decide probes.
      REMAINDER, still booked: `durch`/`ptrOf`/`fnref` (pointer and function
      types carry no range, so the range table has nothing to recompute) and
      `altGlob`/`altSlot` (post-entry values, not reads of the live world).
    CUT-5 resource contexts: COVERED below for straight-line int blocks --
      `bind` (context extension by the recomputed range), nullary `call`
      (`params = []`, `gruende = 0` recomputed), `ret`/`retWert` (result shape
      plus the linear balance `Λ.Perm V.ende` recomputed). Each with validity
      side conditions, soundness cases, pos/neg decide probes.
      REMAINDER, still booked and said out loud: a call's `RufPasst` travels
      AS PROOF in the certificate. It quantifies over the arbitrary carrier
      types (`∀ t`, `∀ g`, `∀ L`), so no range table can recompute it the way
      `certRange` recomputes `darf`; carrying it is the honest shrink, and the
      day `Tab`/`Glob` enumerate, the arm can check it instead.
    The fragment is int-typed throughout: every certificate elaborates to an
    `Expr` of `int` type (reads) or a `Block` over int bindings (statements).
    Non-int types -- `bool`, pointers, functions, options, sums -- stay booked
    under CUT-3 and the CUT-4 remainder above.

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

end Gabbro.Grammatik
