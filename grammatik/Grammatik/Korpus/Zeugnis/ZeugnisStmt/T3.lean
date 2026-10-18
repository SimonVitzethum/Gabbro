/- Part 3 of 3 of `ZeugnisStmt` (split by instrumente/teile/lean-teilen.py; the umbrella `ZeugnisStmt.lean` imports all parts). -/
import Grammatik.Korpus.Zeugnis.ZeugnisStmt.T2

namespace Gabbro.Grammatik

/-! ## Boolean checkers: what the Rust printer must satisfy

    The transfer-phase printer emits one `CertStmt`/`CertSeq`/`CertEnd`
    term per statement/block plus the claimed resource flow; Lean runs the
    checker below (`decide`) and `zeugnisStmt_sound` turns acceptance into
    the judgement. `certemit.rs` prints nothing for statements today --
    section CUTS names the print format the Rust side must emit. -/

/-- Condition checker: `true` iff the condition print recomputes. -/
def certCondOk (D : Deklaration) (Γ : Ctx) (Λ : List (Res D))
    (c : CertCond D) : Bool :=
  decide (certCondGueltig D Γ Λ c)

/-- Statement checker: `true` iff the statement print recomputes. -/
def certStmtOk (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (s : CertStmt D V) : Bool :=
  decide (certStmtGueltig D V l Γ Λ Λ' s)

/-- Block checker: `true` iff the block print recomputes. -/
def certSeqOk (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (q : CertSeq D V) : Bool :=
  decide (certSeqGueltig D V l Γ Λ Λ' q)

/-- Non-falling-block checker: `true` iff the body print recomputes. -/
def certEndOk (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (c : CertEnd D V) : Bool :=
  decide (certEndGueltig D V l Γ Λ c)

/-- Certificate soundness for statements: a valid body print IMPLIES the
    judgement -- there EXISTS an accepted `Endblock`. Every premise is
    used: the place (`D V l Γ Λ`), the print (`c`), the acceptance (`h`). -/
theorem zeugnisStmt_sound (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ : List (Res D)) (c : CertEnd D V)
    (h : certEndOk D V l Γ Λ c = true) :
    ∃ _ : Endblock D V l Γ Λ, True :=
  end_sound D V l Γ Λ c (of_decide_eq_true h)

/-! ## Witness: the certificate of `einzahlen` (rule 13)

    `refCertEin` is the printed certificate of `refP`'s `einzahlen` body
    (`refRumpfEin`: write the cap, call `lies`, return): the index `0`
    widened to the generated `0 .. 1`, the cap `100` widened to the field
    `0 .. 100`, the nullary call with its carried `RufPasst`, the bare
    return. Validity closes by `decide`; soundness elaborates it to a
    well-typed `Endblock` at EXACTLY `refRumpfEin`'s type
    (`Endblock refD (vertragVon refD refEin) false [.int 0 10] [held]`).
    The run is non-degenerate: table `konto` is written (`refSchrittBF`
    via `execStmt`) and `MB` is reached with moved memory
    (`refB_erreicht`, `refB_schreibt`). -/

/-- The printed certificate of the `einzahlen` body. -/
def refCertEin : CertEnd refD (vertragVon refD refEin) :=
  .cons (.assignSlot () () (.wide 0 1 (.lit 0)) (.wide 0 100 (.lit 100)))
    [Res.held (D := refD) ()]
    (.cons (.call refLies [Res.held (D := refD) ()] refHpLiesAt)
      [Res.held (D := refD) ()]
      .ret)

/-- The print is valid, by `decide`. -/
example : certEndOk refD (vertragVon refD refEin) false [.int 0 10]
    [Res.held (D := refD) ()] refCertEin = true := by decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock refD (vertragVon refD refEin) false [.int 0 10]
    [Res.held (D := refD) ()], True :=
  zeugnisStmt_sound refD _ false _ _ refCertEin (by decide)

/-- Inhabitation witness for `zeugnisStmt_sound` (rule 13): ALL premises
    instantiated JOINTLY -- place, print, acceptance -- plus the
    non-degenerate run (one table written, four reached steps, memory
    moved). Every conjunct is used. -/
theorem zeugnisStmt_sound_zeuge :
    ∃ (c : CertEnd refD (vertragVon refD refEin)),
      certEndOk refD (vertragVon refD refEin) false [.int 0 10]
        [Res.held (D := refD) ()] c = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨refCertEin, by decide, MB, refB_erreicht, refB_schreibt⟩

/-! ### Rejection probes: forged prints are provably invalid -/

/-- FORGED guard: the same write with empty hands -- `darf` fails,
    so the print is provably not valid. -/
example : ¬ certStmtGueltig refD (vertragVon refD refEin) false [.int 0 10]
    [] []
    (.assignSlot () () (.wide 0 1 (.lit 0))
      (.wide 0 100 (.lit 100))) := by
  decide

/-- FORGED index: a bare `3` is not of index type `0 .. 1`. -/
example : certStmtOk refD (vertragVon refD refEin) false [.int 0 10]
    [Res.held (D := refD) ()] [Res.held (D := refD) ()]
    (.assignSlot () () (.lit 3) (.wide 0 100 (.lit 100))) = false := by
  decide

/-! ## CUTS: what is not proved, constructor by constructor

    COVERED (38 of 49 `Stmt`/`Block`/`Endblock` constructors, each with a
    validity arm, a `Decidable` arm, and a soundness case above):
    - `Stmt`: assignSlot, assignVar, assignGlob, schreibBytes, uebergang,
      ite, onOption (see R-1), call (see R-2), locks, breaking, traverse,
      retry, forever, publish, regSchreib, advances, retires, ret,
      retWert, retGrund, leave, next (21 of 26).
    - `Block`: nil, cons, bind, bindCall (see R-2), bindCallElse,
      regLies, regLiesElse, awaits, exchange, narrow, pruefung (11 of 17).
    - `Endblock`: ret, retWert, retGrund, leave, next, cons, bind (6 of 6).
    - `CertCond` (the bool scrutinees): wahr, falsch, var, lt, le, eq,
      und, oder, nicht (9 of 9 over the int fragment).
    R-1 `onOption` covers `some`-introducer scrutinees only (the index
      certificate recomputes `0 .. n - 1` and elaborates via `Expr.some`).
      Option scrutinees from variables, globals, or slots need the CUT-3
      option rows wired to a pinned `.opt n` type (`cut3_sound` leaves the
      type existential) -- booked.
    R-2 `call`/`bindCall` cover NULLARY callees only (`params = []`,
      `gruende = 0` recomputed). Calls with arguments need per-argument
      certificates against the callee's parameter types (the `Block5Args`
      precedent of `Zeugnis.lean`) -- booked.
    R-3 `RufPasst` travels AS PROOF with the carried resource list `Λc`
      (validity equates it with `Λ`). It quantifies over arbitrary carrier
      types, so no table recomputes it -- the `CertBlock.call` precedent
      of `Zeugnis.lean`, not a gap in the checking.
    NOT COVERED, with the reason each stays out:
    - `assignDurch`, `callInd`, `bindCallInd`: pointer/function-pointer
      scrutinees carry no range, so the range table has nothing to
      recompute. Needs the CUT-4 remainder rows (`CertCut4`) wired to
      pinned `.ptr`/`.fnptr` types -- booked.
    - `onTag`: sum scrutinees need the `fall` row plus one certificate
      per case (`Arms` list elaboration with case-list correspondence).
    - `onGrund`: reason scrutinees need the `grund` row plus `n`
      certificates (`GrundArms` list elaboration with length `n`).
    - `axiomCall`, `bindAxiom`: the foreign-write frame (`hw`/`hg`) and
      guard frame (`hd`/`hgd`) quantify over arbitrary carrier types.
      They travel as proofs only in an indexed certificate (the `RufPasst`
      shape); in plain data they are booked, not faked.
    - `transition`: needs `D.spiegel r = some m`, undecidable without
      `DecidableEq D.Reg` (the declaration does not supply one).
    - `gleit`, `gleitLit`, `gleitVon`, `gleitNarrow`: float payloads need
      the CUT-3 float rows (`CertFl`) wired to block context extension.
    - Expression shapes beyond the int fragment (`altGlob`/`altSlot`,
      `durch`, `ptrOf`, `fnref`, quantifier bodies) stay booked exactly
      where `Zeugnis.lean` books them; statements over them are uncovered
      with them.
    RUST SIDE (`crates/gabbro-check/src/certemit.rs`, `zeugnis.rs`): prints
    EXPRESSION certificates only -- nothing for statements today. The
    transfer-phase printer must emit, per statement/block: the `CertStmt`/
    `CertSeq`/`CertEnd` term in `CertExpr` print syntax (one line per
    node, children first, as `side_conditions` does), the claimed
    resource flow (`Λ` before, `Λ`/`Λm`/output after, as names), and the
    recomputed side lines (`darf`/`gdarf` holds, `V.schreibt` holds, rank
    order holds, index shape exact, balance `Perm`). `RufPasst` and the
    reason-count facts travel as checked references, not re-derivations.
-/

#print axioms cond_sound
#print axioms stmt_sound
#print axioms seq_sound
#print axioms end_sound
#print axioms rankOk_true
#print axioms zeugnisStmt_sound
#print axioms zeugnisStmt_sound_zeuge


end Gabbro.Grammatik
