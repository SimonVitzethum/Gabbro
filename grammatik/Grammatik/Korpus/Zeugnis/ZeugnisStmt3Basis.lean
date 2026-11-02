/-
  File:     Grammatik/ZeugnisStmt3.lean
  Subject:  Certificate soundness for the AXIOM/REGISTER statement/block
             constructors (lane 150: the lane-146 gap).

  Extends `ZeugnisStmt.lean`/`ZeugnisStmt2.lean` with the three shapes that
  had no rule-13 witness on `refD` (`Ax`/`Reg` are `Empty` there):
  `Stmt.axiomCall` (nullary, the four frame proofs carried like the
  `RufPasst` of `callInd`), `Stmt.transition` (mirror equation recomputed
  under a carried `DecidableEq D.Reg` instance -- the declaration has no
  `decReg` field and shared files stay untouched), and `Block.bindAxiom`
  (nullary with a pinned `.int` result, the `bindCall` precedent).
  Witnesses build on the `ReferenzAR` fixture (`arD`/`arP`/`arO`/`arSp0`
  and the reached memory-writing run `arMB`).
-/
module
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt
public import Grammatik.Korpus.Referenz.ReferenzAR
@[expose] public section


namespace Gabbro.Grammatik

/-- The two remaining `Stmt` shapes as plain data. `axiomCall` names the
    axiom and carries the holdings plus the four frame proofs (the
    foreign-write frames `hw`/`hg` and guard frames `hd`/`hgd` quantify
    over the arbitrary carrier types, so no table recomputes them -- the
    R-3 shape, carried as proof like the `RufPasst` of `callInd`);
    `transition` names both registers and the bit data (the mirror
    equation recomputes). -/
inductive CertStmt3 (D : Deklaration) (V : Vertrag D) where
  | axiomCall (a : D.Ax) (Λc : List (Res D))
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λc)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λc)
  | transition (r m : D.Reg) (maske bits : Int)

/-! ## Statement validity: every recomputable side condition -/

/-- Third-batch statement validity. `axiomCall` recomputes the holdings
    equation, the nullary shape and the no-result equation (the four
    frames travel as proof); `transition` the writable class, the mirror
    equation and the readable class. -/
def certStmt3Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : CertStmt3 D V → Prop
  | .axiomCall a Λc _ _ _ _ =>
    Λ = Λc ∧ D.aparams a = [] ∧ D.aerg a = none ∧ Λ = Λ'
  | .transition r m _ _ =>
    (D.rklasse r).schreibbar = true ∧ D.spiegel r = some m ∧
      (D.rklasse m).lesbar = true ∧ Λ = Λ'

/-- Third-batch validity as `Decidable`. The mirror equation needs
    `DecidableEq D.Reg`, carried as a separate instance argument (the
    declaration has no `decReg` field). -/
def decStmt3Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) [DecidableEq D.Reg] (s : CertStmt3 D V) :
    Decidable (certStmt3Gueltig D V l Γ Λ Λ' s) :=
  match s with
  | .axiomCall a Λc _ _ _ _ =>
    inferInstanceAs (Decidable (Λ = Λc ∧ D.aparams a = [] ∧
      D.aerg a = none ∧ Λ = Λ'))
  | .transition r m _ _ =>
    inferInstanceAs (Decidable ((D.rklasse r).schreibbar = true ∧
      D.spiegel r = some m ∧ (D.rklasse m).lesbar = true ∧ Λ = Λ'))

instance instDecStmt3 (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) [DecidableEq D.Reg] (s : CertStmt3 D V) :
    Decidable (certStmt3Gueltig D V l Γ Λ Λ' s) :=
  decStmt3Gueltig D V l Γ Λ Λ' s

/-! ## Soundness, one lemma per statement constructor -/

/-- `axiomCall` soundness (nullary axioms): the parameter equation
    rebuilds the empty argument list, the result equation and the four
    carried frame proofs feed the call. Every hypothesis is used. -/
theorem axiomCall_sound (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ Λ' : List (Res D)) (a : D.Ax) (Λc : List (Res D))
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λc)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λc)
    (h : certStmt3Gueltig D V l Γ Λ Λ'
      (.axiomCall a Λc hw hg hd hgd)) :
    ∃ _ : Stmt D V l Γ Λ Λ', True := by
  simp only [certStmt3Gueltig] at h
  obtain ⟨hΛc, hpar, herg, hout⟩ := h
  subst hΛc
  subst hout
  exact ⟨Stmt.axiomCall a (by rw [hpar]; exact Args.nil) herg hw hg hd hgd,
    trivial⟩

/-- `transition` soundness: the recomputed class facts and mirror
    equation feed the device step. Every hypothesis is used. -/
theorem transition_sound (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ Λ' : List (Res D)) (r m : D.Reg) (maske bits : Int)
    (h : certStmt3Gueltig D V l Γ Λ Λ' (.transition r m maske bits)) :
    ∃ _ : Stmt D V l Γ Λ Λ', True := by
  simp only [certStmt3Gueltig] at h
  obtain ⟨hk, hm, hl, hout⟩ := h
  subst hout
  exact ⟨Stmt.transition r hk m hm hl maske bits, trivial⟩

/-- Joint third-batch statement soundness: dispatch to the two
    per-constructor lemmas. -/
theorem stmt3_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (s : CertStmt3 D V)
    (h : certStmt3Gueltig D V l Γ Λ Λ' s) :
    ∃ _ : Stmt D V l Γ Λ Λ', True := by
  revert h
  match s with
  | .axiomCall a Λc hw hg hd hgd =>
    intro h
    exact axiomCall_sound D V l Γ Λ Λ' a Λc hw hg hd hgd h
  | .transition r m maske bits =>
    intro h
    exact transition_sound D V l Γ Λ Λ' r m maske bits h

/-! ## Block certificates: `bindAxiom` plus new-statement cons

    `CertSeq` (in `ZeugnisStmt.lean`) is a closed inductive and cannot be
    extended from here; `CertSeq3` therefore carries the new shape with
    `CertSeq3` tails and a `lift` arm that reuses every old block print
    (validity and soundness delegate), plus `cons3` for the two new
    statements inside blocks. -/

/-- The remaining `Block` shape as plain data: `bindAxiom` over a nullary
    axiom with a pinned `.int` result (the `bindCall` precedent: the
    claimed range names the bound type, the result equation recomputes),
    the four frames carried as proof. -/
inductive CertSeq3 (D : Deklaration) (V : Vertrag D) where
  | lift (q : CertSeq D V)
  | cons3 (s : CertStmt3 D V) (Λm : List (Res D)) (rest : CertSeq3 D V)
  | bindAxiom (a : D.Ax) (lo hi : Int) (Λc : List (Res D))
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λc)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λc)
    (rest : CertSeq3 D V)

/-- Third-batch block validity. `bindAxiom` recomputes the holdings
    equation, the nullary shape and the claimed result type; the tail
    runs under the bound variable. -/
def certSeq3Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : CertSeq3 D V → Prop
  | .lift q => certSeqGueltig D V l Γ Λ Λ' q
  | .cons3 s Λm rest =>
    certStmt3Gueltig D V l Γ Λ Λm s ∧ certSeq3Gueltig D V l Γ Λm Λ' rest
  | .bindAxiom a lo hi Λc _ _ _ _ rest =>
    Λ = Λc ∧ D.aparams a = [] ∧ D.aerg a = some (.int lo hi) ∧
      certSeq3Gueltig D V l (.int lo hi :: Γ) Λ Λ' rest

/-- Third-batch block validity as `Decidable`, by structural recursion. -/
def decSeq3Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) [DecidableEq D.Reg] (q : CertSeq3 D V) :
    Decidable (certSeq3Gueltig D V l Γ Λ Λ' q) :=
  match q with
  | .lift r =>
    inferInstanceAs (Decidable (certSeqGueltig D V l Γ Λ Λ' r))
  | .cons3 s Λm rest =>
    haveI := decStmt3Gueltig D V l Γ Λ Λm s
    haveI := decSeq3Gueltig D V l Γ Λm Λ' rest
    inferInstanceAs (Decidable (certStmt3Gueltig D V l Γ Λ Λm s ∧
      certSeq3Gueltig D V l Γ Λm Λ' rest))
  | .bindAxiom a lo hi Λc _ _ _ _ rest =>
    haveI := decSeq3Gueltig D V l (.int lo hi :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable (Λ = Λc ∧ D.aparams a = [] ∧
      D.aerg a = some (.int lo hi) ∧
      certSeq3Gueltig D V l (.int lo hi :: Γ) Λ Λ' rest))

instance instDecSeq3 (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) [DecidableEq D.Reg] (q : CertSeq3 D V) :
    Decidable (certSeq3Gueltig D V l Γ Λ Λ' q) :=
  decSeq3Gueltig D V l Γ Λ Λ' q

/-- Joint third-batch block soundness: `lift` reuses the old layer,
    `cons3` threads through both statement layers, `bindAxiom`
    elaborates inline. Every hypothesis is used. -/
theorem seq3_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (q : CertSeq3 D V)
    (h : certSeq3Gueltig D V l Γ Λ Λ' q) :
    ∃ _ : Block D V l Γ Λ Λ', True := by
  revert h
  match q with
  | .lift r =>
    intro h
    obtain ⟨r', _⟩ := seq_sound D V l Γ Λ Λ' r h
    exact ⟨r', trivial⟩
  | .cons3 s Λm rest =>
    intro h
    simp only [certSeq3Gueltig] at h
    obtain ⟨hs, hrest⟩ := h
    obtain ⟨s', _⟩ := stmt3_sound D V l Γ Λ Λm s hs
    obtain ⟨r', _⟩ := seq3_sound D V l Γ Λm Λ' rest hrest
    exact ⟨Block.cons s' r', trivial⟩
  | .bindAxiom a lo hi Λc hw hg hd hgd rest =>
    intro h
    simp only [certSeq3Gueltig] at h
    obtain ⟨hΛc, hpar, he, hrest⟩ := h
    subst hΛc
    obtain ⟨r', _⟩ :=
      seq3_sound D V l (.int lo hi :: Γ) Λ Λ' rest hrest
    exact ⟨Block.bindAxiom a (by rw [hpar]; exact Args.nil) he hw hg hd hgd r',
      trivial⟩

end Gabbro.Grammatik
