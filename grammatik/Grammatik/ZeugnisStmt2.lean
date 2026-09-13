/-
  File:     Grammatik/ZeugnisStmt2.lean
  Subject:  Certificate soundness for the REMAINING statement/block
            constructors (T1 of PLAN-UEBERSETZUNGSVALIDIERUNG.md, part 2).

  Extends `ZeugnisStmt.lean` (38 of 50 constructors) with the shapes that
  fit the current certificate data (`CertExpr` for the int fragment,
  `CertCut3` sum/ground rows, `CertCut4` pointer rows, `CertFl` float
  rows): `Stmt`: assignDurch, callInd (nullary, the R-2 fragment),
  onTag, onGrund; `Block`: bindCallInd (nullary), gleit, gleitLit,
  gleitVon, gleitNarrow. `axiomCall`/`bindAxiom`/`transition` stay listed
  (see CUTS): no rule-13 witness exists on the reference fixture.
-/
import Grammatik.ZeugnisStmt

namespace Gabbro.Grammatik

/-- Case-list certificates for `Stmt.onTag`: one `CertSeq` per `sum` case,
    the case pinned in the constructor (the `Arms` correspondence). -/
inductive CertArms2 (D : Deklaration) (V : Vertrag D) : List (Option (Int × Int)) → Type where
  | nil : CertArms2 D V []
  | cons (c : Option (Int × Int)) (b : CertSeq D V) {cs : List (Option (Int × Int))}
    (rest : CertArms2 D V cs) : CertArms2 D V (c :: cs)

/-- Reason-list certificates for `Stmt.onGrund`: one `CertSeq` per reason
    (the `GrundArms` correspondence, length `n`). -/
inductive CertGrundArms2 (D : Deklaration) (V : Vertrag D) : Nat → Type where
  | nil : CertGrundArms2 D V 0
  | cons (b : CertSeq D V) {n : Nat} (rest : CertGrundArms2 D V n) :
    CertGrundArms2 D V (n + 1)

/-- The four remaining `Stmt` shapes as plain data. `assignDurch` names the
    table number (the `tabNr` equation recomputes, the pointer is rebuilt
    from it); `callInd` names the callee and its signature number (the
    `sig` equation recomputes, nullary only, the R-2 fragment, `RufPasst`
    travels as proof); `onTag`/`onGrund` carry the scrutinee shapes the
    CUT-3 rows already print (`fall` payload check, `r < n`). -/
inductive CertStmt2 (D : Deklaration) (V : Vertrag D) where
  | assignDurch (t : D.Tab) (f : D.Feld t) (n : Nat) (rw : Bool) (i e : CertExpr D)
  | callInd (f : D.Fn) (n : Nat) (Λc : List (Res D)) (hp : RufPasst D V (D.sigNr n) Λc)
  | onTag (cs : List (Option (Int × Int))) (i : Nat) (p : Option (CertExpr D))
    (arms : CertArms2 D V cs)
  | onGrund (n r : Nat) (arms : CertGrundArms2 D V n)

/-! ## Arm validity: every side condition recomputed -/

/-- Case-list validity: each arm recomputes at its pinned case context
    (`ArmCtx`), the resource flow shared across arms. -/
def certArms2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : {cs : List (Option (Int × Int))} →
    CertArms2 D V cs → Prop
  | [], .nil => Λ = Λ'
  | _ :: _, .cons c b rest =>
    certSeqGueltig D V l (ArmCtx Γ c) Λ Λ' b ∧ certArms2Gueltig D V l Γ Λ Λ' rest

/-- Reason-list validity: each of the `n` arms recomputes at the shared
    flow (reasons bind nothing, like `GrundArms.cons`). -/
def certGrundArms2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : {n : Nat} → CertGrundArms2 D V n → Prop
  | 0, .nil => Λ = Λ'
  | _ + 1, .cons b rest =>
    certSeqGueltig D V l Γ Λ Λ' b ∧ certGrundArms2Gueltig D V l Γ Λ Λ' rest

/-- Arm validity as `Decidable`, by structural recursion. -/
def decArms2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) {cs : List (Option (Int × Int))}
    (a : CertArms2 D V cs) : Decidable (certArms2Gueltig D V l Γ Λ Λ' a) :=
  match a with
  | .nil => inferInstanceAs (Decidable (Λ = Λ'))
  | .cons c b rest =>
    haveI := decSeqGueltig D V l (ArmCtx Γ c) Λ Λ' b
    haveI := decArms2Gueltig D V l Γ Λ Λ' rest
    inferInstanceAs (Decidable (certSeqGueltig D V l (ArmCtx Γ c) Λ Λ' b ∧
      certArms2Gueltig D V l Γ Λ Λ' rest))

instance instDecArms2 (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) {cs : List (Option (Int × Int))}
    (a : CertArms2 D V cs) : Decidable (certArms2Gueltig D V l Γ Λ Λ' a) :=
  decArms2Gueltig D V l Γ Λ Λ' a

/-- Reason-list validity as `Decidable`, by structural recursion. -/
def decGrundArms2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) {n : Nat}
    (a : CertGrundArms2 D V n) :
    Decidable (certGrundArms2Gueltig D V l Γ Λ Λ' a) :=
  match a with
  | .nil => inferInstanceAs (Decidable (Λ = Λ'))
  | .cons b rest =>
    haveI := decSeqGueltig D V l Γ Λ Λ' b
    haveI := decGrundArms2Gueltig D V l Γ Λ Λ' rest
    inferInstanceAs (Decidable (certSeqGueltig D V l Γ Λ Λ' b ∧
      certGrundArms2Gueltig D V l Γ Λ Λ' rest))

instance instDecGrundArms2 (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ Λ' : List (Res D)) {n : Nat}
    (a : CertGrundArms2 D V n) :
    Decidable (certGrundArms2Gueltig D V l Γ Λ Λ' a) :=
  decGrundArms2Gueltig D V l Γ Λ Λ' a

/-- Case-list soundness: a valid arm print elaborates to `Arms`. Every
    hypothesis is used: the head arm via `seq_sound`, the tail via the
    induction. -/
theorem arms2_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) {cs : List (Option (Int × Int))}
    (a : CertArms2 D V cs) (h : certArms2Gueltig D V l Γ Λ Λ' a) :
    ∃ _ : Arms D V l Γ Λ Λ' cs, True := by
  revert h
  match a with
  | .nil =>
    intro h
    simp only [certArms2Gueltig] at h
    subst h
    exact ⟨Arms.nil, trivial⟩
  | .cons c b rest =>
    intro h
    simp only [certArms2Gueltig] at h
    obtain ⟨hb, hrest⟩ := h
    obtain ⟨b', _⟩ := seq_sound D V l (ArmCtx Γ c) Λ Λ' b hb
    obtain ⟨r', _⟩ := arms2_sound D V l Γ Λ Λ' rest hrest
    exact ⟨Arms.cons b' r', trivial⟩

/-- Reason-list soundness: a valid reason print elaborates to `GrundArms`. -/
theorem grundArms2_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) {n : Nat}
    (a : CertGrundArms2 D V n) (h : certGrundArms2Gueltig D V l Γ Λ Λ' a) :
    ∃ _ : GrundArms D V l Γ Λ Λ' n, True := by
  revert h
  match a with
  | .nil =>
    intro h
    simp only [certGrundArms2Gueltig] at h
    subst h
    exact ⟨GrundArms.nil, trivial⟩
  | .cons b rest =>
    intro h
    simp only [certGrundArms2Gueltig] at h
    obtain ⟨hb, hrest⟩ := h
    obtain ⟨b', _⟩ := seq_sound D V l Γ Λ Λ' b hb
    obtain ⟨r', _⟩ := grundArms2_sound D V l Γ Λ Λ' rest hrest
    exact ⟨GrundArms.cons b' r', trivial⟩

/-! ## Typed scrutinees: the CUT-3 rows pinned to their types

    `cut3_sound` elaborates to an existential type; `Stmt.onTag` needs the
    scrutinee at EXACTLY `.sum cs`. The `fall` case below mirrors that
    proof with the type pinned (same payload equations, same
    `certCut3PayloadOk` check). -/

/-- A valid `fall` print elaborates to a `sum` scrutinee at exactly `cs`.
    Every hypothesis is used: the payload equations via `zeugnis_sound`,
    the length fact for the `Fin`, the check for the payload shape. -/
theorem fall_typed (D : Deklaration) (Γ : Ctx) (Λ : List (Res D))
    (cs : List (Option (Int × Int))) (i : Nat)
    (p : Option (CertExpr D))
    (h : i < cs.length ∧ certCut3PayloadOk D Γ Λ cs[i]? p = true) :
    ∃ _ : Expr D Γ Λ (.sum cs), True := by
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
        exact ⟨Expr.fall cs ⟨i, hi⟩ (hget'.symm ▸ NutzlastExpr.keine),
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
        exact ⟨Expr.fall cs ⟨i, hi⟩ (hget'.symm ▸ NutzlastExpr.zahl ee),
          trivial⟩

/-! ## Statement validity: every side condition recomputed -/

/-- Second-batch statement validity. `assignDurch` recomputes the table
    number equation (via `decTab`), the generated index shape, the field
    type equation, the write fact and the guard; `callInd` the signature
    equation, the nullary shape and the reason freedom (the R-2 fragment,
    `RufPasst` carried as proof); `onTag` the case index, the payload
    check and the arm list; `onGrund` the reason bound and the arm list. -/
def certStmt2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : CertStmt2 D V → Prop
  | .assignDurch t f n rw i e =>
    rw = true ∧ D.tabNr n = some t ∧
      certRange D Γ Λ i = some (0, D.count t - 1) ∧
      certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.typ t f) ∧
      V.schreibt t = true ∧ darf D t Λ ∧ Λ = Λ'
  | .callInd f n Λc _ =>
    D.sig f = n ∧ Λ = Λc ∧ (D.sigNr n).params = [] ∧
      (D.sigNr n).gruende = 0 ∧ nachSig D (D.sigNr n) Λ = Λ'
  | .onTag cs i p arms =>
    i < cs.length ∧ certCut3PayloadOk D Γ Λ cs[i]? p = true ∧
      certArms2Gueltig D V l Γ Λ Λ' arms ∧ Λ = Λ'
  | .onGrund n r arms =>
    r < n ∧ certGrundArms2Gueltig D V l Γ Λ Λ' arms ∧ Λ = Λ'

/-- Second-batch validity as `Decidable`, by structural recursion. -/
def decStmt2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (s : CertStmt2 D V) :
    Decidable (certStmt2Gueltig D V l Γ Λ Λ' s) :=
  match s with
  | .assignDurch t f n rw i e =>
    inferInstanceAs (Decidable (rw = true ∧ D.tabNr n = some t ∧
      certRange D Γ Λ i = some (0, D.count t - 1) ∧
      certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.typ t f) ∧
      V.schreibt t = true ∧ darf D t Λ ∧ Λ = Λ'))
  | .callInd f n Λc _ =>
    inferInstanceAs (Decidable (D.sig f = n ∧ Λ = Λc ∧
      (D.sigNr n).params = [] ∧ (D.sigNr n).gruende = 0 ∧
      nachSig D (D.sigNr n) Λ = Λ'))
  | .onTag cs i p arms =>
    haveI := decArms2Gueltig D V l Γ Λ Λ' arms
    inferInstanceAs (Decidable (i < cs.length ∧
      certCut3PayloadOk D Γ Λ cs[i]? p = true ∧
      certArms2Gueltig D V l Γ Λ Λ' arms ∧ Λ = Λ'))
  | .onGrund n r arms =>
    haveI := decGrundArms2Gueltig D V l Γ Λ Λ' arms
    inferInstanceAs (Decidable (r < n ∧
      certGrundArms2Gueltig D V l Γ Λ Λ' arms ∧ Λ = Λ'))

instance instDecStmt2 (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (s : CertStmt2 D V) :
    Decidable (certStmt2Gueltig D V l Γ Λ Λ' s) :=
  decStmt2Gueltig D V l Γ Λ Λ' s

/-! ## Soundness, one lemma per constructor -/

/-- `assignDurch` soundness: the table-number equation rebuilds the
    pointer (`ptrOf`), the index and value elaborate from the int
    fragment. Every hypothesis is used. -/
theorem assignDurch_sound (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ Λ' : List (Res D)) (t : D.Tab) (f : D.Feld t) (n : Nat)
    (rw : Bool) (i e : CertExpr D)
    (h : certStmt2Gueltig D V l Γ Λ Λ'
      (.assignDurch t f n rw i e)) :
    ∃ _ : Stmt D V l Γ Λ Λ', True := by
  simp only [certStmt2Gueltig] at h
  obtain ⟨hrw, htab, hii, hne, htyp, hw, hL, hout⟩ := h
  subst hrw
  subst hout
  obtain ⟨ei, _⟩ := zeugnis_sound i 0 (D.count t - 1) hii
  cases he : certRange D Γ Λ e with
  | none => exact absurd he hne
  | some p =>
    obtain ⟨lo, hi'⟩ := p
    have hft : intVonTyp (D.typ t f) = some (lo, hi') := by
      rw [← he]
      exact htyp.symm
    have hτ : D.typ t f = .int lo hi' := intVonTyp_eq hft
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi' he
    have ee' : Expr D Γ Λ (D.typ t f) := by rw [hτ]; exact ee
    exact ⟨Stmt.assignDurch (Expr.ptrOf t n htab true) t htab f ei ee' hw hL,
      trivial⟩

/-- `callInd` soundness (nullary callees, the R-2 fragment): the signature
    equation rebuilds the pointer (`fnref`), the carried `RufPasst` feeds
    the call. Every hypothesis is used. -/
theorem callInd_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (f : D.Fn) (n : Nat) (Λc : List (Res D))
    (hp : RufPasst D V (D.sigNr n) Λc)
    (h : certStmt2Gueltig D V l Γ Λ Λ' (.callInd f n Λc hp)) :
    ∃ _ : Stmt D V l Γ Λ Λ', True := by
  simp only [certStmt2Gueltig] at h
  obtain ⟨hsig, hΛc, hpar, hgr, hnach⟩ := h
  subst hΛc
  subst hnach
  exact ⟨Stmt.callInd (Expr.fnref f n hsig)
    (by rw [hpar]; exact Args.nil) hp hgr, trivial⟩

/-- `onTag` soundness: the `fall` print elaborates to the `sum`
    scrutinee at exactly `cs`, the arm print to `Arms`. Every hypothesis
    is used. -/
theorem onTag_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (cs : List (Option (Int × Int))) (i : Nat)
    (p : Option (CertExpr D)) (arms : CertArms2 D V cs)
    (h : certStmt2Gueltig D V l Γ Λ Λ' (.onTag cs i p arms)) :
    ∃ _ : Stmt D V l Γ Λ Λ', True := by
  simp only [certStmt2Gueltig] at h
  obtain ⟨hi, hp, harms, hout⟩ := h
  subst hout
  obtain ⟨v, _⟩ := fall_typed D Γ Λ cs i p ⟨hi, hp⟩
  obtain ⟨as, _⟩ := arms2_sound D V l Γ Λ Λ arms harms
  exact ⟨Stmt.onTag v as, trivial⟩

/-- `onGrund` soundness: the reason literal elaborates to the `grund`
    scrutinee, the arm print to `GrundArms`. Every hypothesis is used. -/
theorem onGrund_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (n r : Nat) (arms : CertGrundArms2 D V n)
    (h : certStmt2Gueltig D V l Γ Λ Λ' (.onGrund n r arms)) :
    ∃ _ : Stmt D V l Γ Λ Λ', True := by
  simp only [certStmt2Gueltig] at h
  obtain ⟨hlt, harms, hout⟩ := h
  subst hout
  obtain ⟨as, _⟩ := grundArms2_sound D V l Γ Λ Λ arms harms
  exact ⟨Stmt.onGrund (Expr.grund n ⟨r, hlt⟩) as, trivial⟩

end Gabbro.Grammatik
