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

/-! ## Block certificates: the five remaining `Block` shapes

    `CertSeq` (in `ZeugnisStmt.lean`) is a closed inductive and cannot be
    extended from here; `CertSeq2` therefore carries the five new shapes
    with `CertSeq2` tails and a `lift` arm that reuses every old block
    print (validity and soundness delegate). -/

/-- The five remaining `Block` shapes as plain data: `bindCallInd`
    (nullary through a signature number, the R-2 fragment, `RufPasst` as
    proof) and the four float steps (`gleit` over two `CertFl` reads,
    `gleitLit` over literal data, `gleitVon` over the int fragment,
    `gleitNarrow` with a falling branch). -/
inductive CertSeq2 (D : Deklaration) (V : Vertrag D) where
  | lift (q : CertSeq D V)
  | cons2 (s : CertStmt2 D V) (Λm : List (Res D)) (rest : CertSeq2 D V)
  | bindCallInd (f : D.Fn) (n : Nat) (lo hi : Int) (Λc : List (Res D))
    (hp : RufPasst D V (D.sigNr n) Λc) (rest : CertSeq2 D V)
  | gleit (op : GleitOp) (a b : CertFl D) (lo hi : Int × Int) (rest : CertSeq2 D V)
  | gleitLit (q lo hi : Int × Int) (rest : CertSeq2 D V)
  | gleitVon (e : CertExpr D) (lo hi : Int × Int) (rest : CertSeq2 D V)
  | gleitNarrow (e : CertFl D) (lo hi : Int × Int) (sonst : CertEnd D V)
    (rest : CertSeq2 D V)

/-- Second-batch block validity. `bindCallInd` recomputes the signature
    equation, the nullary shape, the reason freedom and the claimed
    result type; `gleit`/`gleitNarrow` the float bounds on every operand;
    `gleitVon` the int range; `gleitLit` carries literal data the model
    does not constrain, so only the tail recomputes. -/
def certSeq2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : CertSeq2 D V → Prop
  | .lift q => certSeqGueltig D V l Γ Λ Λ' q
  | .cons2 s Λm rest =>
    certStmt2Gueltig D V l Γ Λ Λm s ∧ certSeq2Gueltig D V l Γ Λm Λ' rest
  | .bindCallInd f n lo hi Λc _ rest =>
    D.sig f = n ∧ Λ = Λc ∧ (D.sigNr n).params = [] ∧
      (D.sigNr n).gruende = 0 ∧ (D.sigNr n).erg = some (.int lo hi) ∧
      certSeq2Gueltig D V l (.int lo hi :: Γ) (nachSig D (D.sigNr n) Λ) Λ' rest
  | .gleit _ a b lo hi rest =>
    certFlTyp D Γ Λ a ≠ none ∧ certFlTyp D Γ Λ b ≠ none ∧
      certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
  | .gleitLit _ lo hi rest =>
    certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
  | .gleitVon e lo hi rest =>
    certRange D Γ Λ e ≠ none ∧
      certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
  | .gleitNarrow e lo hi sonst rest =>
    certFlTyp D Γ Λ e ≠ none ∧ certEndGueltig D V l Γ Λ sonst ∧
      certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest

/-- Second-batch block validity as `Decidable`, by structural recursion. -/
def decSeq2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (q : CertSeq2 D V) :
    Decidable (certSeq2Gueltig D V l Γ Λ Λ' q) :=
  match q with
  | .lift r =>
    inferInstanceAs (Decidable (certSeqGueltig D V l Γ Λ Λ' r))
  | .cons2 s Λm rest =>
    haveI := decStmt2Gueltig D V l Γ Λ Λm s
    haveI := decSeq2Gueltig D V l Γ Λm Λ' rest
    inferInstanceAs (Decidable (certStmt2Gueltig D V l Γ Λ Λm s ∧
      certSeq2Gueltig D V l Γ Λm Λ' rest))
  | .bindCallInd f n lo hi Λc _ rest =>
    haveI := decSeq2Gueltig D V l (.int lo hi :: Γ) (nachSig D (D.sigNr n) Λ) Λ' rest
    inferInstanceAs (Decidable (D.sig f = n ∧ Λ = Λc ∧
      (D.sigNr n).params = [] ∧ (D.sigNr n).gruende = 0 ∧
      (D.sigNr n).erg = some (.int lo hi) ∧
      certSeq2Gueltig D V l (.int lo hi :: Γ) (nachSig D (D.sigNr n) Λ) Λ' rest))
  | .gleit _ a b lo hi rest =>
    haveI := decSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable (certFlTyp D Γ Λ a ≠ none ∧
      certFlTyp D Γ Λ b ≠ none ∧
      certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest))
  | .gleitLit _ lo hi rest =>
    haveI := decSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
    inferInstanceAs
      (Decidable (certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest))
  | .gleitVon e lo hi rest =>
    haveI := decSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable (certRange D Γ Λ e ≠ none ∧
      certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest))
  | .gleitNarrow e lo hi sonst rest =>
    haveI := decEndGueltig D V l Γ Λ sonst
    haveI := decSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable (certFlTyp D Γ Λ e ≠ none ∧
      certEndGueltig D V l Γ Λ sonst ∧
      certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest))

instance instDecSeq2 (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (q : CertSeq2 D V) :
    Decidable (certSeq2Gueltig D V l Γ Λ Λ' q) :=
  decSeq2Gueltig D V l Γ Λ Λ' q

/-! ## Joint second-batch statement soundness -/

/-- Joint second-batch statement soundness: dispatch to the four
    per-constructor lemmas. -/
theorem stmt2_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (s : CertStmt2 D V)
    (h : certStmt2Gueltig D V l Γ Λ Λ' s) :
    ∃ _ : Stmt D V l Γ Λ Λ', True := by
  revert h
  match s with
  | .assignDurch t f n rw i e =>
    intro h
    exact assignDurch_sound D V l Γ Λ Λ' t f n rw i e h
  | .callInd f n Λc hp =>
    intro h
    exact callInd_sound D V l Γ Λ Λ' f n Λc hp h
  | .onTag cs i p arms =>
    intro h
    exact onTag_sound D V l Γ Λ Λ' cs i p arms h
  | .onGrund n r arms =>
    intro h
    exact onGrund_sound D V l Γ Λ Λ' n r arms h

/-! ## Joint second-batch block soundness: structural, all cases inline

    The five new shapes elaborate here (not in the per-constructor
    lemmas below, which are single-constructor corollaries of this
    function): splitting them into a `mutual` block defeats structural
    recursion, since each helper recurses on a certificate it receives
    as an argument rather than on its own matched subterm. -/

/-- Joint second-batch block soundness: `lift` reuses the old layer,
    `cons2` threads through both statement layers, the five new shapes
    elaborate inline. Every hypothesis is used. -/
theorem seq2_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (q : CertSeq2 D V)
    (h : certSeq2Gueltig D V l Γ Λ Λ' q) :
    ∃ _ : Block D V l Γ Λ Λ', True := by
  revert h
  match q with
  | .lift r =>
    intro h
    obtain ⟨r', _⟩ := seq_sound D V l Γ Λ Λ' r h
    exact ⟨r', trivial⟩
  | .cons2 s Λm rest =>
    intro h
    simp only [certSeq2Gueltig] at h
    obtain ⟨hs, hrest⟩ := h
    obtain ⟨s', _⟩ := stmt2_sound D V l Γ Λ Λm s hs
    obtain ⟨r', _⟩ := seq2_sound D V l Γ Λm Λ' rest hrest
    exact ⟨Block.cons s' r', trivial⟩
  | .bindCallInd f n lo hi Λc hp rest =>
    intro h
    simp only [certSeq2Gueltig] at h
    obtain ⟨hsig, hΛc, hpar, hgr, he, hrest⟩ := h
    subst hΛc
    obtain ⟨r', _⟩ :=
      seq2_sound D V l (.int lo hi :: Γ) (nachSig D (D.sigNr n) Λ) Λ' rest hrest
    exact ⟨Block.bindCallInd (Expr.fnref f n hsig)
      (by rw [hpar]; exact Args.nil) he hp hgr r', trivial⟩
  | .gleit op a b lo hi rest =>
    intro h
    simp only [certSeq2Gueltig] at h
    cases ha : certFlTyp D Γ Λ a with
    | none => exact absurd ha h.1
    | some _ =>
      cases hb : certFlTyp D Γ Λ b with
      | none => exact absurd hb h.2.1
      | some _ =>
        obtain ⟨ea, _⟩ := certFl_sound a _ _ ha
        obtain ⟨eb, _⟩ := certFl_sound b _ _ hb
        obtain ⟨r', _⟩ :=
          seq2_sound D V l (.fl lo hi :: Γ) Λ Λ' rest h.2.2
        exact ⟨Block.gleit op ea eb lo hi r', trivial⟩
  | .gleitLit q lo hi rest =>
    intro h
    simp only [certSeq2Gueltig] at h
    obtain ⟨r', _⟩ := seq2_sound D V l (.fl lo hi :: Γ) Λ Λ' rest h
    exact ⟨Block.gleitLit q lo hi r', trivial⟩
  | .gleitVon e lo hi rest =>
    intro h
    simp only [certSeq2Gueltig] at h
    obtain ⟨hne, hrest⟩ := h
    cases he : certRange D Γ Λ e with
    | none => exact absurd he hne
    | some p =>
      obtain ⟨l1, h1⟩ := p
      obtain ⟨ee, _⟩ := zeugnis_sound e l1 h1 he
      obtain ⟨r', _⟩ := seq2_sound D V l (.fl lo hi :: Γ) Λ Λ' rest hrest
      exact ⟨Block.gleitVon ee lo hi r', trivial⟩
  | .gleitNarrow e lo hi sonst rest =>
    intro h
    simp only [certSeq2Gueltig] at h
    obtain ⟨hne, hsonst, hrest⟩ := h
    cases hf : certFlTyp D Γ Λ e with
    | none => exact absurd hf hne
    | some q =>
      obtain ⟨l1, h1⟩ := q
      obtain ⟨ee, _⟩ := certFl_sound e l1 h1 hf
      obtain ⟨es, _⟩ := end_sound D V l Γ Λ sonst hsonst
      obtain ⟨r', _⟩ := seq2_sound D V l (.fl lo hi :: Γ) Λ Λ' rest hrest
      exact ⟨Block.gleitNarrow ee lo hi es r', trivial⟩

/-! ## Block soundness, one lemma per constructor

    Single-constructor corollaries of `seq2_sound`: each states the
    elaboration of one new shape and proves it by applying the joint
    lemma to the certificate the hypotheses form. -/

/-- `bindCallInd` soundness (nullary callees, the R-2 fragment). -/
theorem bindCallInd_sound (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ Λ' : List (Res D)) (f : D.Fn) (n : Nat) (lo hi : Int)
    (Λc : List (Res D)) (hp : RufPasst D V (D.sigNr n) Λc)
    (rest : CertSeq2 D V)
    (h : certSeq2Gueltig D V l Γ Λ Λ'
      (.bindCallInd f n lo hi Λc hp rest)) :
    ∃ _ : Block D V l Γ Λ Λ', True :=
  seq2_sound D V l Γ Λ Λ' (.bindCallInd f n lo hi Λc hp rest) h

/-- `gleit` soundness. -/
theorem gleit_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (op : GleitOp) (a b : CertFl D) (lo hi : Int × Int)
    (rest : CertSeq2 D V)
    (h : certSeq2Gueltig D V l Γ Λ Λ' (.gleit op a b lo hi rest)) :
    ∃ _ : Block D V l Γ Λ Λ', True :=
  seq2_sound D V l Γ Λ Λ' (.gleit op a b lo hi rest) h

/-- `gleitLit` soundness. -/
theorem gleitLit_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (q lo hi : Int × Int) (rest : CertSeq2 D V)
    (h : certSeq2Gueltig D V l Γ Λ Λ' (.gleitLit q lo hi rest)) :
    ∃ _ : Block D V l Γ Λ Λ', True :=
  seq2_sound D V l Γ Λ Λ' (.gleitLit q lo hi rest) h

/-- `gleitVon` soundness. -/
theorem gleitVon_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (e : CertExpr D) (lo hi : Int × Int)
    (rest : CertSeq2 D V)
    (h : certSeq2Gueltig D V l Γ Λ Λ' (.gleitVon e lo hi rest)) :
    ∃ _ : Block D V l Γ Λ Λ', True :=
  seq2_sound D V l Γ Λ Λ' (.gleitVon e lo hi rest) h

/-- `gleitNarrow` soundness. -/
theorem gleitNarrow_sound (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ Λ' : List (Res D)) (e : CertFl D) (lo hi : Int × Int)
    (sonst : CertEnd D V) (rest : CertSeq2 D V)
    (h : certSeq2Gueltig D V l Γ Λ Λ'
      (.gleitNarrow e lo hi sonst rest)) :
    ∃ _ : Block D V l Γ Λ Λ', True :=
  seq2_sound D V l Γ Λ Λ' (.gleitNarrow e lo hi sonst rest) h

/-! ## Non-falling blocks: `lift` plus new-statement cons

    A program body (`Endblock`) may start with a new-statement shape, so
    `CertEnd2` pairs a `lift` of every old body print with a `cons2E` for
    the four new statements. -/

/-- Second-batch body prints: reuse (`lift`) plus new-statement cons. -/
inductive CertEnd2 (D : Deklaration) (V : Vertrag D) where
  | liftE (e : CertEnd D V)
  | cons2E (s : CertStmt2 D V) (Λm : List (Res D)) (rest : CertEnd2 D V)

/-- Second-batch body validity: the old layer delegates, `cons2E`
    threads through the carried middle. -/
def certEnd2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) : CertEnd2 D V → Prop
  | .liftE e => certEndGueltig D V l Γ Λ e
  | .cons2E s Λm rest =>
    certStmt2Gueltig D V l Γ Λ Λm s ∧ certEnd2Gueltig D V l Γ Λm rest

/-- Second-batch body validity as `Decidable`, by structural recursion. -/
def decEnd2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (e : CertEnd2 D V) :
    Decidable (certEnd2Gueltig D V l Γ Λ e) :=
  match e with
  | .liftE c => inferInstanceAs (Decidable (certEndGueltig D V l Γ Λ c))
  | .cons2E s Λm rest =>
    haveI := decStmt2Gueltig D V l Γ Λ Λm s
    haveI := decEnd2Gueltig D V l Γ Λm rest
    inferInstanceAs (Decidable (certStmt2Gueltig D V l Γ Λ Λm s ∧
      certEnd2Gueltig D V l Γ Λm rest))

instance instDecEnd2 (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (e : CertEnd2 D V) :
    Decidable (certEnd2Gueltig D V l Γ Λ e) :=
  decEnd2Gueltig D V l Γ Λ e

/-- Second-batch body soundness: a valid body print elaborates to an
    accepted `Endblock`. Every hypothesis is used. -/
theorem end2_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (e : CertEnd2 D V)
    (h : certEnd2Gueltig D V l Γ Λ e) :
    ∃ _ : Endblock D V l Γ Λ, True := by
  revert h
  match e with
  | .liftE c =>
    intro h
    obtain ⟨c', _⟩ := end_sound D V l Γ Λ c h
    exact ⟨c', trivial⟩
  | .cons2E s Λm rest =>
    intro h
    simp only [certEnd2Gueltig] at h
    obtain ⟨hs, hrest⟩ := h
    obtain ⟨s', _⟩ := stmt2_sound D V l Γ Λ Λm s hs
    obtain ⟨r', _⟩ := end2_sound D V l Γ Λm rest hrest
    exact ⟨Endblock.cons s' r', trivial⟩

/-- Second-batch body checker: `true` iff the body print recomputes. -/
def certEnd2Ok (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (c : CertEnd2 D V) : Bool :=
  decide (certEnd2Gueltig D V l Γ Λ c)

/-- Certificate soundness, second batch: a valid body print IMPLIES the
    judgement -- there EXISTS an accepted `Endblock`. Every premise is
    used: the place (`D V l Γ Λ`), the print (`c`), the acceptance (`h`). -/
theorem zeugnisStmt2_sound (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ : List (Res D)) (c : CertEnd2 D V)
    (h : certEnd2Ok D V l Γ Λ c = true) :
    ∃ _ : Endblock D V l Γ Λ, True :=
  end2_sound D V l Γ Λ c (of_decide_eq_true h)

/-! ## Boolean checkers: what the transfer printer must satisfy -/

/-- Second-batch statement checker: `true` iff the print recomputes. -/
def certStmt2Ok (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (s : CertStmt2 D V) : Bool :=
  decide (certStmt2Gueltig D V l Γ Λ Λ' s)

/-- Second-batch block checker: `true` iff the print recomputes. -/
def certSeq2Ok (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (q : CertSeq2 D V) : Bool :=
  decide (certSeq2Gueltig D V l Γ Λ Λ' q)

/-! ## Witnesses: one per soundness lemma (rule 13)

    Each `NAME_zeuge` instantiates ALL premises of its lemma JOINTLY on
    the reference fixture (`refD`, `einzahlen`'s contract, one written
    table `konto`) plus the non-degenerate run (`MB`: reached from
    `RufStartF`, slot `0 → 100`). -/

/-- Inhabitation witness for `assignDurch_sound`: the write through the
    table-`0` pointer, index and cap from the int fragment. -/
theorem assignDurch_sound_zeuge :
    ∃ (s : CertStmt2 refD (vertragVon refD refEin)),
      certStmt2Ok refD _ false [.int 0 10]
        [Res.held (D := refD) ()] [Res.held (D := refD) ()] s = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨.assignDurch () () 0 true (.wide 0 1 (.lit 0)) (.wide 0 100 (.lit 100)),
    by decide, MB, refB_erreicht, refB_schreibt⟩

/-- Inhabitation witness for `callInd_sound`: the indirect call of the
    nullary `lies` through signature `1`. -/
theorem callInd_sound_zeuge :
    ∃ (s : CertStmt2 refD (vertragVon refD refEin)),
      certStmt2Ok refD _ false [.int 0 10]
        [Res.held (D := refD) ()] [Res.held (D := refD) ()] s = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨.callInd refLies 1 [Res.held (D := refD) ()] refHpLiesAt,
    by decide, MB, refB_erreicht, refB_schreibt⟩

/-- Inhabitation witness for `onTag_sound`: the caseless `sum` with its
    single empty arm. -/
theorem onTag_sound_zeuge :
    ∃ (s : CertStmt2 refD (vertragVon refD refEin)),
      certStmt2Ok refD _ false [.int 0 10]
        [Res.held (D := refD) ()] [Res.held (D := refD) ()] s = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨.onTag [none] 0 none (.cons none .nil .nil),
    by decide, MB, refB_erreicht, refB_schreibt⟩

/-- Inhabitation witness for `onGrund_sound`: the single reason with its
    empty arm. -/
theorem onGrund_sound_zeuge :
    ∃ (s : CertStmt2 refD (vertragVon refD refEin)),
      certStmt2Ok refD _ false [.int 0 10]
        [Res.held (D := refD) ()] [Res.held (D := refD) ()] s = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨.onGrund 1 0 (.cons .nil .nil),
    by decide, MB, refB_erreicht, refB_schreibt⟩

/-- Inhabitation witness for `bindCallInd_sound`: the indirect
    nullary call of `lies` binding its `.int 0 100` result. -/
theorem bindCallInd_sound_zeuge :
    ∃ (q : CertSeq2 refD (vertragVon refD refEin)),
      certSeq2Ok refD _ false [.int 0 10]
        [Res.held (D := refD) ()] [Res.held (D := refD) ()] q = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨.bindCallInd refLies 1 0 100 [Res.held (D := refD) ()] refHpLiesAt
    (.lift .nil), by decide, MB, refB_erreicht, refB_schreibt⟩

/-- Inhabitation witness for `gleit_sound`: the float addition over two
    variable reads in float bounds. -/
theorem gleit_sound_zeuge :
    ∃ (q : CertSeq2 refD (vertragVon refD refEin)),
      certSeq2Ok refD _ false [.fl (0, 0) (1, 1)]
        [Res.held (D := refD) ()] [Res.held (D := refD) ()] q = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨.gleit .add (.varFl 0) (.varFl 0) (0, 0) (1, 1) (.lift .nil),
    by decide, MB, refB_erreicht, refB_schreibt⟩

/-- Inhabitation witness for `gleitLit_sound`: the float literal step. -/
theorem gleitLit_sound_zeuge :
    ∃ (q : CertSeq2 refD (vertragVon refD refEin)),
      certSeq2Ok refD _ false []
        [Res.held (D := refD) ()] [Res.held (D := refD) ()] q = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨.gleitLit (0, 0) (0, 0) (1, 1) (.lift .nil),
    by decide, MB, refB_erreicht, refB_schreibt⟩

/-- Inhabitation witness for `gleitVon_sound`: the int-to-float step
    over the literal `7`. -/
theorem gleitVon_sound_zeuge :
    ∃ (q : CertSeq2 refD (vertragVon refD refEin)),
      certSeq2Ok refD _ false []
        [Res.held (D := refD) ()] [Res.held (D := refD) ()] q = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨.gleitVon (.lit 7) (0, 0) (1, 1) (.lift .nil),
    by decide, MB, refB_erreicht, refB_schreibt⟩

/-- Inhabitation witness for `gleitNarrow_sound`: narrowing a float
    variable read, falling back to the bare return. -/
theorem gleitNarrow_sound_zeuge :
    ∃ (q : CertSeq2 refD (vertragVon refD refEin)),
      certSeq2Ok refD _ false [.fl (0, 0) (1, 1)]
        [Res.held (D := refD) ()] [Res.held (D := refD) ()] q = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨.gleitNarrow (.varFl 0) (0, 0) (1, 1) .ret (.lift .nil),
    by decide, MB, refB_erreicht, refB_schreibt⟩

/-- Inhabitation witness for `zeugnisStmt2_sound`: a body that writes
    through the table-`0` pointer and then runs the `einzahlen` print. -/
theorem zeugnisStmt2_sound_zeuge :
    ∃ (c : CertEnd2 refD (vertragVon refD refEin)),
      certEnd2Ok refD (vertragVon refD refEin) false [.int 0 10]
        [Res.held (D := refD) ()] c = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨.cons2E (.assignDurch () () 0 true (.wide 0 1 (.lit 0))
    (.wide 0 100 (.lit 100))) [Res.held (D := refD) ()]
    (.liftE refCertEin), by decide, MB, refB_erreicht, refB_schreibt⟩

/-! ### Rejection probes: forged prints are provably invalid -/

/-- FORGED capability: a read-only pointer cannot carry a write -- the
    `rw = true` check fails, so the print is provably not valid. -/
example : ¬ certStmt2Gueltig refD (vertragVon refD refEin) false
    [.int 0 10] [Res.held (D := refD) ()] [Res.held (D := refD) ()]
    (.assignDurch () () 0 false (.wide 0 1 (.lit 0))
      (.wide 0 100 (.lit 100))) := by
  decide

/-- FORGED reason: reason `1` of one does not exist. -/
example : ¬ certStmt2Gueltig refD (vertragVon refD refEin) false
    [.int 0 10] [Res.held (D := refD) ()] [Res.held (D := refD) ()]
    (.onGrund 1 1 (.cons .nil .nil)) := by
  decide

/-- FORGED payload: the caseless `sum` carries no `zahl` payload. -/
example : ¬ certStmt2Gueltig refD (vertragVon refD refEin) false
    [.int 0 10] [Res.held (D := refD) ()] [Res.held (D := refD) ()]
    (.onTag [none] 0 (some (.lit 0)) (.cons none .nil .nil)) := by
  decide

/-! ## CUTS: what is not proved, constructor by constructor

    MEASURED (from the `Stmt`/`Block`/`Endblock` types in `Syntax.lean`
    against the covered cases of `ZeugnisStmt.lean`): the tree has
    27 + 17 + 6 = 50 constructors, not 49 -- `ZeugnisStmt.lean` books
    "38 of 49" (21 + 11 + 6) and its `CUTS` already lists every booked
    shape, so one `Stmt` constructor was added after that count was
    written. The missing twelve are:
    - `Stmt`: assignDurch, onTag, onGrund, callInd, axiomCall,
      transition (6).
    - `Block`: bindCallInd, bindAxiom, gleit, gleitLit, gleitVon,
      gleitNarrow (6).
    - `Endblock`: none missing (6 of 6).
    COVERED HERE (9 of 12), each with a validity arm, a `Decidable`
    arm, a per-constructor soundness lemma and a rule-13 witness:
    - `Stmt`: assignDurch (pointer rebuilt from the recomputed `tabNr`
      equation, `rw = true` recomputed), callInd (nullary, the R-2
      fragment: `sig` equation recomputed, `RufPasst` carried as proof),
      onTag (`fall` scrutinee pinned to `.sum cs` by `fall_typed`, arms
      by `arms2_sound`), onGrund (reason literal, arms by
      `grundArms2_sound`).
    - `Block`: bindCallInd (nullary through a signature number),
      gleit/gleitVon/gleitNarrow (operands from the `CertFl`/`CertExpr`
      rows), gleitLit (literal data the model does not constrain).
    - Calls WITH arguments stay in the R-2 fragment (nullary only);
      the with-arguments shape is the `CertBlock5`/`Block5Args`
      precedent of `Zeugnis.lean`, not re-proved here.
    NOT COVERED, with the reason each stays out:
    - `axiomCall`, `bindAxiom`: the foreign-write frames (`hw`/`hg`)
      and guard frames (`hd`/`hgd`) quantify over the arbitrary
      carrier types (`∀ t : D.Tab`, `∀ g : D.Glob`), so no table
      recomputes them -- the R-3 indexed-certificate shape, not plain
      data. And NO rule-13 witness exists on the reference fixture:
      `refD.Ax` is `Empty`, so no `axiomCall` certificate is even
      well-typed there. A lane with axioms in its fixture certifies
      the nullary fragment (one `aparams = []` equation plus the four
      carried frame proofs) and builds the witness there.
    - `transition`: the mirror equation `D.spiegel r = some m` needs
      `DecidableEq D.Reg`, which the declaration does not supply (there
      is `decTab`/`decGlob`/`decLock`/`decMarke`, no `decReg`). And
      `refD.Reg` is `Empty`, so no witness exists on the fixture
      either. Same lane as above, once `decReg` exists.
    - Expression shapes beyond the wired rows (`altGlob`/`altSlot`,
      quantifier bodies over non-`bool` binders) stay booked exactly
      where `Zeugnis.lean` books them; statements over them are
      uncovered with them.
    RUST SIDE (`crates/gabbro-check/src/zeugnis.rs`): the census
    `erhebe`/`block` already counts every surface statement form,
    including the origins of the nine new shapes (pointer writes under
    `assignment`, indirect calls under `call`, tagged matches under
    `match (tagged)`, reason matches under `match (tagged)`, float
    steps under `let`). Nothing was uncounted, so no print change was
    needed -- only per-form tests. `certemit.rs` still prints
    EXPRESSION certificates only; the statement print format stays
    designed in `ZeugnisStmt.lean`'s CUTS for the transfer phase.
    TERM IDENTITY (task question): it is proved NOWHERE -- neither
    `Zeugnis.lean`/`ZeugnisStmt.lean` nor `certemit.rs` links the
    printed certificate to the checked term. `certemit.rs` states it
    outright ("printer-prints-what-was-checked is trust base there").
    The smallest statement closing it for one expression would be:
    `theorem print_elab (e : CheckedExpr) : elab (print e) = e` -- the
    printer applied to the CHECKED term re-elaborates to that same
    term. It needs (a) the printer to take the checked (typed) term,
    not the raw AST, and (b) `elab` to be a computational function
    returning `Option`, with `= some e` proved by `rfl` over the
    validity predicates -- the direction lane 136's report already
    names (its soundness yields `∃`, proved with choice inside, so the
    witness term is not computational). One expression form suffices
    to fix the shape; per-constructor instances follow the T1 rows.
-/

#print axioms fall_typed
#print axioms arms2_sound
#print axioms grundArms2_sound
#print axioms assignDurch_sound
#print axioms callInd_sound
#print axioms onTag_sound
#print axioms onGrund_sound
#print axioms stmt2_sound
#print axioms seq2_sound
#print axioms bindCallInd_sound
#print axioms gleit_sound
#print axioms gleitLit_sound
#print axioms gleitVon_sound
#print axioms gleitNarrow_sound
#print axioms end2_sound
#print axioms zeugnisStmt2_sound
#print axioms assignDurch_sound_zeuge
#print axioms callInd_sound_zeuge
#print axioms onTag_sound_zeuge
#print axioms onGrund_sound_zeuge
#print axioms bindCallInd_sound_zeuge
#print axioms gleit_sound_zeuge
#print axioms gleitLit_sound_zeuge
#print axioms gleitVon_sound_zeuge
#print axioms gleitNarrow_sound_zeuge
#print axioms zeugnisStmt2_sound_zeuge

end Gabbro.Grammatik
