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
import Grammatik.ZeugnisStmt
import Grammatik.ReferenzAR

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

/-- `bindAxiom` soundness (nullary axioms with an `.int` result). -/
theorem bindAxiom_sound (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ Λ' : List (Res D)) (a : D.Ax) (lo hi : Int)
    (Λc : List (Res D))
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λc)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λc)
    (rest : CertSeq3 D V)
    (h : certSeq3Gueltig D V l Γ Λ Λ'
      (.bindAxiom a lo hi Λc hw hg hd hgd rest)) :
    ∃ _ : Block D V l Γ Λ Λ', True :=
  seq3_sound D V l Γ Λ Λ' (.bindAxiom a lo hi Λc hw hg hd hgd rest) h

/-! ## Body certificates, checkers, the top theorem -/

/-- Third-batch body prints: reuse (`liftE`) plus new-statement cons. -/
inductive CertEnd3 (D : Deklaration) (V : Vertrag D) where
  | liftE (e : CertEnd D V)
  | cons3E (s : CertStmt3 D V) (Λm : List (Res D)) (rest : CertEnd3 D V)

/-- Third-batch body validity: the old layer delegates, `cons3E`
    threads through the carried middle. -/
def certEnd3Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) : CertEnd3 D V → Prop
  | .liftE e => certEndGueltig D V l Γ Λ e
  | .cons3E s Λm rest =>
    certStmt3Gueltig D V l Γ Λ Λm s ∧ certEnd3Gueltig D V l Γ Λm rest

/-- Third-batch body validity as `Decidable`, by structural recursion. -/
def decEnd3Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) [DecidableEq D.Reg] (e : CertEnd3 D V) :
    Decidable (certEnd3Gueltig D V l Γ Λ e) :=
  match e with
  | .liftE c => inferInstanceAs (Decidable (certEndGueltig D V l Γ Λ c))
  | .cons3E s Λm rest =>
    haveI := decStmt3Gueltig D V l Γ Λ Λm s
    haveI := decEnd3Gueltig D V l Γ Λm rest
    inferInstanceAs (Decidable (certStmt3Gueltig D V l Γ Λ Λm s ∧
      certEnd3Gueltig D V l Γ Λm rest))

instance instDecEnd3 (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) [DecidableEq D.Reg] (e : CertEnd3 D V) :
    Decidable (certEnd3Gueltig D V l Γ Λ e) :=
  decEnd3Gueltig D V l Γ Λ e

/-- Third-batch body soundness: a valid body print elaborates to an
    accepted `Endblock`. Every hypothesis is used. -/
theorem end3_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (e : CertEnd3 D V)
    (h : certEnd3Gueltig D V l Γ Λ e) :
    ∃ _ : Endblock D V l Γ Λ, True := by
  revert h
  match e with
  | .liftE c =>
    intro h
    obtain ⟨c', _⟩ := end_sound D V l Γ Λ c h
    exact ⟨c', trivial⟩
  | .cons3E s Λm rest =>
    intro h
    simp only [certEnd3Gueltig] at h
    obtain ⟨hs, hrest⟩ := h
    obtain ⟨s', _⟩ := stmt3_sound D V l Γ Λ Λm s hs
    obtain ⟨r', _⟩ := end3_sound D V l Γ Λm rest hrest
    exact ⟨Endblock.cons s' r', trivial⟩

/-- Third-batch statement checker: `true` iff the print recomputes. -/
def certStmt3Ok (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) [DecidableEq D.Reg] (s : CertStmt3 D V) : Bool :=
  decide (certStmt3Gueltig D V l Γ Λ Λ' s)

/-- Third-batch block checker: `true` iff the print recomputes. -/
def certSeq3Ok (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) [DecidableEq D.Reg] (q : CertSeq3 D V) : Bool :=
  decide (certSeq3Gueltig D V l Γ Λ Λ' q)

/-- Third-batch body checker: `true` iff the body print recomputes. -/
def certEnd3Ok (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) [DecidableEq D.Reg] (c : CertEnd3 D V) : Bool :=
  decide (certEnd3Gueltig D V l Γ Λ c)

/-- Certificate soundness, third batch: a valid body print IMPLIES the
    judgement -- there EXISTS an accepted `Endblock`. Every premise is
    used: the place (`D V l Γ Λ`), the print (`c`), the acceptance (`h`). -/
theorem zeugnisStmt3_sound (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ : List (Res D)) [DecidableEq D.Reg] (c : CertEnd3 D V)
    (h : certEnd3Ok D V l Γ Λ c = true) :
    ∃ _ : Endblock D V l Γ Λ, True :=
  end3_sound D V l Γ Λ c (of_decide_eq_true h)

/-! ## Witnesses: one per soundness lemma (rule 13)

    Each `NAME_zeuge` instantiates ALL premises of its lemma JOINTLY on
    the axiom/register fixture (`arD`, `main`'s contract, the lock
    holdings) plus the non-degenerate run (`arMB`: reached from
    `RufStartF`, slot `0 → 100` through the `ruf0` axiom call). -/

/-- Inhabitation witness for `axiomCall_sound`: the nullary `ruf0` call
    with its four frame proofs. -/
theorem axiomCall_sound_zeuge :
    ∃ (s : CertStmt3 arD (vertragVon arD ())),
      certStmt3Ok arD _ false [] arL arL s = true ∧
      ∃ (M : RufMaschineF arD),
        RufErreichbarF arP arO 0 (RufStartF arP arSp0 arInit) M ∧
        M.speicher.slots () 0 () ≠ arSp0.slots () 0 () :=
  ⟨.axiomCall .ruf0 arL arHw0 arHg0 arHd0 arHgd0,
    by decide, arMB, arB_erreicht, arB_schreibt⟩

/-- Inhabitation witness for `bindAxiom_sound`: the nullary `ruf1` call
    binding its `.int 0 10` result. -/
theorem bindAxiom_sound_zeuge :
    ∃ (q : CertSeq3 arD (vertragVon arD ())),
      certSeq3Ok arD _ false [] arL arL q = true ∧
      ∃ (M : RufMaschineF arD),
        RufErreichbarF arP arO 0 (RufStartF arP arSp0 arInit) M ∧
        M.speicher.slots () 0 () ≠ arSp0.slots () 0 () :=
  ⟨.bindAxiom .ruf1 0 10 arL arHw1 arHg1 arHd1 arHgd1 (.lift .nil),
    by decide, arMB, arB_erreicht, arB_schreibt⟩

/-- Inhabitation witness for `transition_sound`: the `w`-from-`r`
    mirror step. -/
theorem transition_sound_zeuge :
    ∃ (s : CertStmt3 arD (vertragVon arD ())),
      certStmt3Ok arD _ false [] arL arL s = true ∧
      ∃ (M : RufMaschineF arD),
        RufErreichbarF arP arO 0 (RufStartF arP arSp0 arInit) M ∧
        M.speicher.slots () 0 () ≠ arSp0.slots () 0 () :=
  ⟨.transition .w .r 255 0,
    by decide, arMB, arB_erreicht, arB_schreibt⟩

/-- Inhabitation witness for `zeugnisStmt3_sound`: a body that calls
    `ruf0` and then returns. -/
theorem zeugnisStmt3_sound_zeuge :
    ∃ (c : CertEnd3 arD (vertragVon arD ())),
      certEnd3Ok arD (vertragVon arD ()) false [] arL c = true ∧
      ∃ (M : RufMaschineF arD),
        RufErreichbarF arP arO 0 (RufStartF arP arSp0 arInit) M ∧
        M.speicher.slots () 0 () ≠ arSp0.slots () 0 () :=
  ⟨.cons3E (.axiomCall .ruf0 arL arHw0 arHg0 arHd0 arHgd0) arL (.liftE .ret),
    by decide, arMB, arB_erreicht, arB_schreibt⟩

/-! ### Rejection probes: forged prints are provably invalid -/

/-- FORGED result: `ruf1` answers, so it is no `axiomCall`. -/
example : ¬ certStmt3Gueltig arD (vertragVon arD ()) false []
    arL arL (.axiomCall .ruf1 arL arHw1 arHg1 arHd1 arHgd1) := by
  decide

/-- FORGED mirror: `r` mirrors nothing and is not writable. -/
example : ¬ certStmt3Gueltig arD (vertragVon arD ()) false []
    arL arL (.transition .r .w 255 0) := by
  decide

/-! ## CUTS: what is not proved, constructor by constructor

    COVERED HERE (3 of 3 -- the lane-146 remainder), each with a validity
    arm, a `Decidable` arm, a per-constructor soundness lemma and a
    rule-13 witness on the new `ReferenzAR` fixture:
    - `Stmt.axiomCall` (nullary: `aparams = []` recomputed, `aerg = none`
      recomputed, the four frame proofs `hw`/`hg`/`hd`/`hgd` carried like
      the `RufPasst` of `callInd` -- they quantify over the arbitrary
      carrier types, so no table recomputes them);
    - `Block.bindAxiom` (nullary with a pinned `.int` result, the
      `bindCall` precedent: `aerg = some (.int lo hi)` recomputed);
    - `Stmt.transition` (writable class, mirror equation and readable
      class recomputed under the carried `DecidableEq D.Reg` instance).
    NOT COVERED, with the reason each stays out:
    - Calls WITH arguments (axiom or indirect): the with-arguments shape
      is the existing `CertBlock5`/`Block5Args` precedent of
      `Zeugnis.lean`, not re-proved here (same boundary as
      `ZeugnisStmt2.lean`).
    - `transition` over a non-`.int` register type: the validity pins no
      value shape (the device step carries only `maske`/`bits` data and
      the model does not constrain them), so there is nothing to
      recompute beyond the two classes and the mirror equation.
    - Expression shapes beyond the wired rows stay booked exactly where
      `Zeugnis.lean` books them; statements over them are uncovered
      with them.
-/

#print axioms axiomCall_sound
#print axioms transition_sound
#print axioms stmt3_sound
#print axioms seq3_sound
#print axioms bindAxiom_sound
#print axioms end3_sound
#print axioms zeugnisStmt3_sound
#print axioms axiomCall_sound_zeuge
#print axioms bindAxiom_sound_zeuge
#print axioms transition_sound_zeuge
#print axioms zeugnisStmt3_sound_zeuge

end Gabbro.Grammatik
