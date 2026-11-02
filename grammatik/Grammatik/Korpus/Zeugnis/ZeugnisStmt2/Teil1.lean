module
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt2.Teil1Basis
import all Grammatik.Korpus.Zeugnis.ZeugnisStmt2.Teil1Basis

public import Grammatik.Korpus.Zeugnis.ZeugnisStmt

@[expose] public section



namespace Gabbro.Grammatik
/-! ## Statement validity: every side condition recomputed -/

/-- Second-batch statement validity. `assignDurch` recomputes the table
    number equation (via `decTab`), the generated index shape, the field
    type equation, the write fact and the guard; `callInd` the signature
    equation, the nullary shape and the reason freedom (the R-2 fragment,
    `RufPasst` carried as proof); `onTag` the case index, the payload
    check and the arm list; `onGrund` the reason bound and the arm list. -/
def certStmt2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : CertStmt2 D V → Prop
  | .assignThru t f n rw i e =>
    rw = true ∧ D.capTab (D.tableSpace t) n = some t ∧
      certRange D Γ Λ i = some (0, D.count t - 1) ∧
      certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.typ t f) ∧
      V.schreibt t = true ∧ darf D t Λ ∧ Λ = Λ'
  | .callInd f n Λc _ =>
    D.passt f n = true ∧ Λ = Λc ∧ (D.sigNr n).params = [] ∧
      (D.sigNr n).gruende = 0 ∧ nachSig D (D.sigNr n) Λ = Λ'
  | .onTag cs i p arms =>
    i < cs.length ∧ certCut3PayloadOk D Γ Λ cs[i]? p = true ∧
      certArms2Gueltig D V l Γ Λ Λ' arms ∧ Λ = Λ'
  | .onWhy n r arms =>
    r < n ∧ certGrundArms2Gueltig D V l Γ Λ Λ' arms ∧ Λ = Λ'

/-- Second-batch validity as `Decidable`, by structural recursion. -/
def decStmt2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (s : CertStmt2 D V) :
    Decidable (certStmt2Gueltig D V l Γ Λ Λ' s) :=
  match s with
  | .assignThru t f n rw i e =>
    inferInstanceAs (Decidable (rw = true ∧ D.capTab (D.tableSpace t) n = some t ∧
      certRange D Γ Λ i = some (0, D.count t - 1) ∧
      certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.typ t f) ∧
      V.schreibt t = true ∧ darf D t Λ ∧ Λ = Λ'))
  | .callInd f n Λc _ =>
    inferInstanceAs (Decidable (D.passt f n = true ∧ Λ = Λc ∧
      (D.sigNr n).params = [] ∧ (D.sigNr n).gruende = 0 ∧
      nachSig D (D.sigNr n) Λ = Λ'))
  | .onTag cs i p arms =>
    haveI := decArms2Gueltig D V l Γ Λ Λ' arms
    inferInstanceAs (Decidable (i < cs.length ∧
      certCut3PayloadOk D Γ Λ cs[i]? p = true ∧
      certArms2Gueltig D V l Γ Λ Λ' arms ∧ Λ = Λ'))
  | .onWhy n r arms =>
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
      (.assignThru t f n rw i e)) :
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
    exact ⟨Stmt.assignThru (Expr.ptrOf t n htab (true, true)) t htab f ei ee' hw hL,
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
    (Λ Λ' : List (Res D)) (cs : List (Option Ty)) (i : Nat)
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
    (h : certStmt2Gueltig D V l Γ Λ Λ' (.onWhy n r arms)) :
    ∃ _ : Stmt D V l Γ Λ Λ', True := by
  simp only [certStmt2Gueltig] at h
  obtain ⟨hlt, harms, hout⟩ := h
  subst hout
  obtain ⟨as, _⟩ := grundArms2_sound D V l Γ Λ Λ arms harms
  exact ⟨Stmt.onWhy (Expr.why n ⟨r, hlt⟩) as, trivial⟩

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
  | float (op : GleitOp) (a b : CertFl D) (lo hi : Int × Int) (rest : CertSeq2 D V)
  | floatLit (q lo hi : Int × Int) (rest : CertSeq2 D V)
  | floatOf (e : CertExpr D) (lo hi : Int × Int) (rest : CertSeq2 D V)
  | floatNarrow (e : CertFl D) (lo hi : Int × Int) (sonst : CertEnd D V)
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
    D.passt f n = true ∧ Λ = Λc ∧ (D.sigNr n).params = [] ∧
      (D.sigNr n).gruende = 0 ∧ (D.sigNr n).erg = some (.int lo hi) ∧
      certSeq2Gueltig D V l (.int lo hi :: Γ) (nachSig D (D.sigNr n) Λ) Λ' rest
  | .float _ a b lo hi rest =>
    certFlTyp D Γ Λ a ≠ none ∧ certFlTyp D Γ Λ b ≠ none ∧
      certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
  | .floatLit _ lo hi rest =>
    certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
  | .floatOf e lo hi rest =>
    certRange D Γ Λ e ≠ none ∧
      certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
  | .floatNarrow e lo hi sonst rest =>
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
    inferInstanceAs (Decidable (D.passt f n = true ∧ Λ = Λc ∧
      (D.sigNr n).params = [] ∧ (D.sigNr n).gruende = 0 ∧
      (D.sigNr n).erg = some (.int lo hi) ∧
      certSeq2Gueltig D V l (.int lo hi :: Γ) (nachSig D (D.sigNr n) Λ) Λ' rest))
  | .float _ a b lo hi rest =>
    haveI := decSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable (certFlTyp D Γ Λ a ≠ none ∧
      certFlTyp D Γ Λ b ≠ none ∧
      certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest))
  | .floatLit _ lo hi rest =>
    haveI := decSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
    inferInstanceAs
      (Decidable (certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest))
  | .floatOf e lo hi rest =>
    haveI := decSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable (certRange D Γ Λ e ≠ none ∧
      certSeq2Gueltig D V l (.fl lo hi :: Γ) Λ Λ' rest))
  | .floatNarrow e lo hi sonst rest =>
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
  | .assignThru t f n rw i e =>
    intro h
    exact assignDurch_sound D V l Γ Λ Λ' t f n rw i e h
  | .callInd f n Λc hp =>
    intro h
    exact callInd_sound D V l Γ Λ Λ' f n Λc hp h
  | .onTag cs i p arms =>
    intro h
    exact onTag_sound D V l Γ Λ Λ' cs i p arms h
  | .onWhy n r arms =>
    intro h
    exact onGrund_sound D V l Γ Λ Λ' n r arms h

/-! ## Joint second-batch block soundness: structural, all cases inline

    The five new shapes elaborate here (not in the per-constructor
    lemmas below, which are single-constructor corollaries of this
    function): splitting them into a `mutual` block defeats structural
    recursion, since each helper recurses on a certificate it receives
    as an argument rather than on its own matched subterm. -/

end Gabbro.Grammatik
