module

public import Grammatik.Korpus.Zeugnis.ZeugnisStmt
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt2.Teil1

@[expose] public section

namespace Gabbro.Grammatik

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
  ⟨.assignThru () () 0 true (.wide 0 1 (.lit 0)) (.wide 0 100 (.lit 100)),
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
  ⟨.onWhy 1 0 (.cons .nil .nil),
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
  ⟨.float .add (.varFl 0) (.varFl 0) (0, 0) (1, 1) (.lift .nil),
    by decide, MB, refB_erreicht, refB_schreibt⟩

/-- Inhabitation witness for `gleitLit_sound`: the float literal step. -/
theorem gleitLit_sound_zeuge :
    ∃ (q : CertSeq2 refD (vertragVon refD refEin)),
      certSeq2Ok refD _ false []
        [Res.held (D := refD) ()] [Res.held (D := refD) ()] q = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨.floatLit (0, 0) (0, 0) (1, 1) (.lift .nil),
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
  ⟨.floatOf (.lit 7) (0, 0) (1, 1) (.lift .nil),
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
  ⟨.floatNarrow (.varFl 0) (0, 0) (1, 1) .ret (.lift .nil),
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
  ⟨.cons2E (.assignThru () () 0 true (.wide 0 1 (.lit 0))
    (.wide 0 100 (.lit 100))) [Res.held (D := refD) ()]
    (.liftE refCertEin), by decide, MB, refB_erreicht, refB_schreibt⟩

/-! ### Rejection probes: forged prints are provably invalid -/

/-- FORGED capability: a read-only pointer cannot carry a write -- the
    `rw = true` check fails, so the print is provably not valid. -/
example : ¬ certStmt2Gueltig refD (vertragVon refD refEin) false
    [.int 0 10] [Res.held (D := refD) ()] [Res.held (D := refD) ()]
    (.assignThru () () 0 false (.wide 0 1 (.lit 0))
      (.wide 0 100 (.lit 100))) := by
  decide

/-- FORGED reason: reason `1` of one does not exist. -/
example : ¬ certStmt2Gueltig refD (vertragVon refD refEin) false
    [.int 0 10] [Res.held (D := refD) ()] [Res.held (D := refD) ()]
    (.onWhy 1 1 (.cons .nil .nil)) := by
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
end Gabbro.Grammatik
