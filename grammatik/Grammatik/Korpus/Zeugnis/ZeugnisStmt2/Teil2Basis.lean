module

public import Grammatik.Korpus.Zeugnis.ZeugnisStmt
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt2.Teil1

@[expose] public section

namespace Gabbro.Grammatik

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
  | .float op a b lo hi rest =>
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
        exact ⟨Block.float op ea eb lo hi r', trivial⟩
  | .floatLit q lo hi rest =>
    intro h
    simp only [certSeq2Gueltig] at h
    obtain ⟨r', _⟩ := seq2_sound D V l (.fl lo hi :: Γ) Λ Λ' rest h
    exact ⟨Block.floatLit q lo hi r', trivial⟩
  | .floatOf e lo hi rest =>
    intro h
    simp only [certSeq2Gueltig] at h
    obtain ⟨hne, hrest⟩ := h
    cases he : certRange D Γ Λ e with
    | none => exact absurd he hne
    | some p =>
      obtain ⟨l1, h1⟩ := p
      obtain ⟨ee, _⟩ := zeugnis_sound e l1 h1 he
      obtain ⟨r', _⟩ := seq2_sound D V l (.fl lo hi :: Γ) Λ Λ' rest hrest
      exact ⟨Block.floatOf ee lo hi r', trivial⟩
  | .floatNarrow e lo hi sonst rest =>
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
      exact ⟨Block.floatNarrow ee lo hi es r', trivial⟩

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
    (h : certSeq2Gueltig D V l Γ Λ Λ' (.float op a b lo hi rest)) :
    ∃ _ : Block D V l Γ Λ Λ', True :=
  seq2_sound D V l Γ Λ Λ' (.float op a b lo hi rest) h

/-- `gleitLit` soundness. -/
theorem gleitLit_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (q lo hi : Int × Int) (rest : CertSeq2 D V)
    (h : certSeq2Gueltig D V l Γ Λ Λ' (.floatLit q lo hi rest)) :
    ∃ _ : Block D V l Γ Λ Λ', True :=
  seq2_sound D V l Γ Λ Λ' (.floatLit q lo hi rest) h

/-- `gleitVon` soundness. -/
theorem gleitVon_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (e : CertExpr D) (lo hi : Int × Int)
    (rest : CertSeq2 D V)
    (h : certSeq2Gueltig D V l Γ Λ Λ' (.floatOf e lo hi rest)) :
    ∃ _ : Block D V l Γ Λ Λ', True :=
  seq2_sound D V l Γ Λ Λ' (.floatOf e lo hi rest) h

/-- `gleitNarrow` soundness. -/
theorem gleitNarrow_sound (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ Λ' : List (Res D)) (e : CertFl D) (lo hi : Int × Int)
    (sonst : CertEnd D V) (rest : CertSeq2 D V)
    (h : certSeq2Gueltig D V l Γ Λ Λ'
      (.floatNarrow e lo hi sonst rest)) :
    ∃ _ : Block D V l Γ Λ Λ', True :=
  seq2_sound D V l Γ Λ Λ' (.floatNarrow e lo hi sonst rest) h

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


end Gabbro.Grammatik
