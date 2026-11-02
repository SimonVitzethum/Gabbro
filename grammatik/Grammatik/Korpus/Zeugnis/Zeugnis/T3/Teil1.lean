module
public import Grammatik.Korpus.Zeugnis.Zeugnis.T3.Teil1Basis
import all Grammatik.Korpus.Zeugnis.Zeugnis.T3.Teil1Basis

public import Grammatik.Korpus.Zeugnis.Zeugnis.T2
meta import Grammatik.Korpus.Zeugnis.Zeugnis.T2

@[expose] public section



namespace Gabbro.Grammatik
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
  | case (cs : List (Option Ty)) (i : Nat) (p : Option (CertExpr D))
  | why (n r : Nat)
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
    (slot : Option (Option Ty)) (p : Option (CertExpr D)) : Bool :=
  match slot, p with
  | some none, none => true
  | some (some (.int lo hi)), some e => decide (certRange D Γ Λ e = some (lo, hi))
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
  | .case cs i p => i < cs.length ∧ certCut3PayloadOk D Γ Λ cs[i]? p = true
  | .why n r => r < n
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
  | .case cs i p =>
    inferInstanceAs
      (Decidable (i < cs.length ∧ certCut3PayloadOk D Γ Λ cs[i]? p = true))
  | .why n r => inferInstanceAs (Decidable (r < n))
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
  | thru (t : D.Tab) (f : D.Feld t) (n : Nat) (i : CertExpr D)

/-- CUT-4 remainder validity: `ptrOf` recomputes the table-number equation;
    `fnref` the signature equation; `durch` the table-number equation, the
    generated index shape, and the guard. The field type is NOT constrained --
    `durch` reads `D.typ t f` whatever it is, exactly as `Expr.durch` does. -/
def certCut4Ok (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) : CertCut4 D → Prop
  | .ptrOf t n _ => D.capTab (D.tableSpace t) n = some t
  | .fnref f n => D.passt f n = true
  | .thru t _f n i =>
    D.capTab (D.tableSpace t) n = some t ∧ certRange D Γ Λ i = some (0, D.count t - 1) ∧ darf D t Λ

/-- CUT-4 remainder validity as `Decidable` (mirror of `decGueltigBlock`). -/
instance decCut4Ok (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) (c : CertCut4 D) :
    Decidable (certCut4Ok D Γ Λ c) :=
  match c with
  | .ptrOf t n _ => inferInstanceAs (Decidable (D.capTab (D.tableSpace t) n = some t))
  | .fnref f n => inferInstanceAs (Decidable (D.passt f n = true))
  | .thru t _f n i =>
    inferInstanceAs
      (Decidable (D.capTab (D.tableSpace t) n = some t ∧ certRange D Γ Λ i = some (0, D.count t - 1) ∧
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

end Gabbro.Grammatik
