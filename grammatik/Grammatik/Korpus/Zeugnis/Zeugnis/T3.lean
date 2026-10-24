/- Part 3 of 4 of `Zeugnis` (split by instrumente/teile/lean-teilen.py; the umbrella `Zeugnis.lean` imports all parts). -/
import Grammatik.Korpus.Zeugnis.Zeugnis.T2

namespace Gabbro.Grammatik

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
    exact ⟨Block.cons (Stmt.ret (by rw [he]; exact ErgExpr.empty) hΛ) Block.nil, trivial⟩
  | retWert e lo hi =>
    intro h
    simp only [certBlockGueltig] at h
    obtain ⟨he, hrng, hΛ⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi hrng
    exact ⟨Block.cons (Stmt.ret (by rw [he]; exact ErgExpr.val ee) hΛ) Block.nil, trivial⟩

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
  | case (cs : List (Option (Int × Int))) (i : Nat) (p : Option (CertExpr D))
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
  | .ptrOf t n _ => D.tabNr n = some t
  | .fnref f n => D.passt f n = true
  | .thru t _f n i =>
    D.tabNr n = some t ∧ certRange D Γ Λ i = some (0, D.count t - 1) ∧ darf D t Λ

/-- CUT-4 remainder validity as `Decidable` (mirror of `decGueltigBlock`). -/
instance decCut4Ok (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) (c : CertCut4 D) :
    Decidable (certCut4Ok D Γ Λ c) :=
  match c with
  | .ptrOf t n _ => inferInstanceAs (Decidable (D.tabNr n = some t))
  | .fnref f n => inferInstanceAs (Decidable (D.passt f n = true))
  | .thru t _f n i =>
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
  | why _ => simp [flVonTyp] at h
  | never => simp [flVonTyp] at h
  | fl lo' hi' =>
    simp [flVonTyp] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | fnptr _ => simp [flVonTyp] at h
  | ptr _ _ => simp [flVonTyp] at h
  | ref _ => simp [flVonTyp] at h

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
      | why _ => simp [ctxFlTyp, flVonTyp] at h
      | never => simp [ctxFlTyp, flVonTyp] at h
      | fl lo' hi' =>
        simp [ctxFlTyp, flVonTyp] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨.here, trivial⟩
      | fnptr _ => simp [ctxFlTyp, flVonTyp] at h
      | ptr _ _ => simp [ctxFlTyp, flVonTyp] at h
      | ref _ => simp [ctxFlTyp, flVonTyp] at h
    | succ k =>
      simp [ctxFlTyp] at h
      obtain ⟨x, _⟩ := ih k h
      exact ⟨.there x, trivial⟩


end Gabbro.Grammatik
