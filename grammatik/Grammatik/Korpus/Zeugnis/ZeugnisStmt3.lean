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
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt3Basis
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt
public import Grammatik.Korpus.Referenz.ReferenzAR
@[expose] public section


namespace Gabbro.Grammatik

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
