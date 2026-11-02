/-
  File:     Grammatik/ZeugnisStmt104b.lean
  Subject:  TRANSFER certificates for `beispiele/0104-referenz.gab` (lane 155).

  The `CertEnd104` layer below extends `CertEnd2` (`ZeugnisStmt2.lean`) with
  exactly what the reference program needs beyond it: calls with arguments
  (`consCall`: the count recomputes, the `RufPasst` and the elaborated
  `Args` travel as proof, the `CertBlock5`/`Block5Args` precedent of
  `Zeugnis.lean` at body level) and a return through a pointer (`retDurch`:
  the table-number equation, the generated index shape, the field-type
  equation and the guard recompute, the pointer travels as proof, the
  `durch` precedent of `cut4_sound`). Old shapes reuse through `lift2`
  (whole old bodies), `cons1`/`cons2` (single old steps) and `bind`/the two
  terminals. Section 4 pastes the verbatim printer output for both bodies
  of `beispiele/0104-referenz.gab` (proofs filled beside the printed `?hp`),
  each accepted by `decide` and pushed through `zeugnisStmt104b_sound`.
-/
module
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt104bBasis
import all Grammatik.Korpus.Zeugnis.ZeugnisStmt104bBasis
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt2
public import Grammatik.Korpus.Programme.Export104
@[expose] public section


namespace Gabbro.Grammatik
/-! ## Witnesses: one per new shape (rule 13)

    Each `NAME_zeuge` instantiates ALL premises of its lemma JOINTLY on
    the reference fixture (`refD`, one written table `konto`) plus the
    non-degenerate run (`MB`: reached from `RufStartF`, slot `0 → 100`).
    The call witness runs the nullary `lies` (the count shape at `0`);
    the pointer-return witness reads the field through table `0`. -/

/-- The call witness print: the nullary `lies` call with its carried
    `RufPasst`, then the bare return. -/
def witCall104 : CertEnd104 refD (vertragVon refD refEin) :=
  (.consCall refLies 0 [Res.held (D := refD) ()] refHpLiesAt
    (.lift2 (.liftE .ret)))

/-- The proofs behind the call witness print: the empty argument list. -/
def witCallArgs104 :
    End104Args refD (vertragVon refD refEin) [.int 0 10]
      [Res.held (D := refD) ()] witCall104 :=
  (.consCall _ _ _ _ Args.nil (.lift2 _))

/-- The pointer-return witness print: the field read through table `0`. -/
def witDurch104 : CertEnd104 refD (vertragVon refD refLies) :=
  (.retDurch () () 0 (.wide 0 1 (.lit 0)))

/-- The proof behind the pointer-return witness print: the table-`0`
    pointer. -/
def witDurchArgs104 :
    End104Args refD (vertragVon refD refLies) []
      [Res.held (D := refD) ()] witDurch104 :=
  (.retDurch _ _ _ _ (Expr.ptrOf () 0 rfl (true, true)))

/-- Inhabitation witness for `end104_sound` (the call shape): ALL premises
    instantiated JOINTLY -- print, proofs, acceptance -- plus the
    non-degenerate run. -/
theorem end104_sound_zeuge :
    ∃ (c : CertEnd104 refD (vertragVon refD refEin))
      (a : End104Args refD _ [.int 0 10] [Res.held (D := refD) ()] c),
      certEnd104Ok refD _ false [.int 0 10] [Res.held (D := refD) ()] c = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨witCall104, witCallArgs104, by decide, MB, refB_erreicht, refB_schreibt⟩

/-- Inhabitation witness for `end104_sound` (the pointer-return shape). -/
theorem end104_retDurch_zeuge :
    ∃ (c : CertEnd104 refD (vertragVon refD refLies))
      (a : End104Args refD _ [] [Res.held (D := refD) ()] c),
      certEnd104Ok refD _ false [] [Res.held (D := refD) ()] c = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨witDurch104, witDurchArgs104, by decide, MB, refB_erreicht, refB_schreibt⟩

/-- Inhabitation witness for `zeugnisStmt104b_sound`: the call shape
    through the top theorem. -/
theorem zeugnisStmt104b_sound_zeuge :
    ∃ (c : CertEnd104 refD (vertragVon refD refEin))
      (a : End104Args refD _ [.int 0 10] [Res.held (D := refD) ()] c),
      certEnd104Ok refD _ false [.int 0 10] [Res.held (D := refD) ()] c = true ∧
      ∃ (M : RufMaschineF refD),
        RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) M ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () :=
  ⟨witCall104, witCallArgs104, by decide, MB, refB_erreicht, refB_schreibt⟩

/-! ## The 104 transfer: verbatim printer output, checked and pushed through

    The two `cert104_*` below are verbatim output of
    `gabbro certificate beispiele/0104-referenz.gab` (section S, lane 155;
    pinned in `crates/gabbro-check/tests/certstmt.rs` as
    `reference_104_prints`), elaborated against the `lean-g` export it was
    printed for (`Export104.lean`: `gD`, `gCtx_*`, `gL_*`). Surface names
    qualify to the export's constructors; the printed `?hp` fills with the
    export's `gHp_einzahlen_lies` (the `Args` list beside it passes the
    pointer the export passes: a fresh read-only `ptrOf`, since the
    caller's `rw` pointer is no `.ptr (.table 0 (true, false))`); the pointer behind
    `retDurch` is the parameter itself. Each `example` runs the Lean
    checker (`certEnd104Ok ... = true` by `decide`); each soundness
    corollary applies `zeugnisStmt104b_sound`. Contexts list the head
    first: `gCtx_einzahlen = [.ptr (.table 0 (true, true)), .index 2, .int 0 10]`, so the
    index variable `i` reads as `(.var 1)` and recomputes `(0, 1)`. -/

/-- Verbatim printer output for `einzahlen`: the pointer write with the
    index variable, the `lies(k, i)` call, the bare return. -/
def cert104_einzahlen :
    CertEnd104 G104_referenz.gD
      (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) :=
  (.cons2
    (.assignThru G104_referenz.GTab.Konto G104_referenz.GKontoFeld.stand
      0 true (.var 1) (.wide 0 100 (.lit 100)))
    [Res.held (D := G104_referenz.gD) G104_referenz.GLock.M]
    (.consCall G104_referenz.GFn.lies 2
      [Res.held (D := G104_referenz.gD) G104_referenz.GLock.M]
      G104_referenz.gHp_einzahlen_lies (.lift2 (.liftE .ret))))

/-- The proofs behind the `einzahlen` print: the two call arguments. -/
def args104_einzahlen :
    End104Args G104_referenz.gD
      (vertragVon G104_referenz.gD G104_referenz.g_einzahlen)
      G104_referenz.gCtx_einzahlen G104_referenz.gL_einzahlen
      cert104_einzahlen :=
  (.cons2 _ _
    (.consCall _ _ _ G104_referenz.gHp_einzahlen_lies
      (.cons (Expr.ptrOf G104_referenz.GTab.Konto 0 rfl (true, false))
        (.cons (Expr.var (.there .here)) .nil))
      (.lift2 _)))

/-- The print is valid, by `decide`. -/
example : certEnd104Ok G104_referenz.gD
    (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) false
    G104_referenz.gCtx_einzahlen G104_referenz.gL_einzahlen
    cert104_einzahlen = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock G104_referenz.gD
    (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) false
    G104_referenz.gCtx_einzahlen G104_referenz.gL_einzahlen, True :=
  zeugnisStmt104b_sound _ _ false _ _ _ args104_einzahlen (by decide)

/-- Verbatim printer output for `lies`: the return through the pointer. -/
def cert104_lies :
    CertEnd104 G104_referenz.gD
      (vertragVon G104_referenz.gD G104_referenz.g_lies) :=
  (.retDurch G104_referenz.GTab.Konto G104_referenz.GKontoFeld.stand
    0 (.var 1))

/-- The proof behind the `lies` print: the pointer parameter itself. -/
def args104_lies :
    End104Args G104_referenz.gD
      (vertragVon G104_referenz.gD G104_referenz.g_lies)
      G104_referenz.gCtx_lies G104_referenz.gL_lies cert104_lies :=
  (.retDurch _ _ _ _ (Expr.var .here))

/-- The print is valid, by `decide`. -/
example : certEnd104Ok G104_referenz.gD
    (vertragVon G104_referenz.gD G104_referenz.g_lies) false
    G104_referenz.gCtx_lies G104_referenz.gL_lies cert104_lies = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock G104_referenz.gD
    (vertragVon G104_referenz.gD G104_referenz.g_lies) false
    G104_referenz.gCtx_lies G104_referenz.gL_lies, True :=
  zeugnisStmt104b_sound _ _ false _ _ _ args104_lies (by decide)

/-! ### Rejection probes: forged prints are provably invalid -/

/-- FORGED count: `lies` takes two arguments, not one. -/
example : ¬ certEnd104Gueltig refD (vertragVon refD refEin) false
    [.int 0 10] [Res.held (D := refD) ()]
    (.consCall refLies 1 [Res.held (D := refD) ()] refHpLiesAt
      (.lift2 (.liftE .ret))) := by
  decide

/-- FORGED index: a bare `3` is not of index type `0 .. 1`. -/
example : ¬ certEnd104Gueltig refD (vertragVon refD refLies) false []
    [Res.held (D := refD) ()] (.retDurch () () 0 (.lit 3)) := by
  decide

/-- FORGED table number: there is no table `5`. -/
example : ¬ certEnd104Gueltig refD (vertragVon refD refLies) false []
    [Res.held (D := refD) ()]
    (.retDurch () () 5 (.wide 0 1 (.lit 0))) := by
  decide

end Gabbro.Grammatik

/-! ## CUTS: what is not proved

    - The file holds two hand-written shapes (`consCall`, `retDurch`, each
      with a validity arm, a `Decidable` arm, a soundness case and a
      rule-13 witness on the reference fixture) plus reuse arms (`lift2`,
      `cons1`, `cons2`, `bind`, `ret`, `retWert`) that delegate to the
      witnessed layers of `ZeugnisStmt.lean`/`ZeugnisStmt2.lean`. No new
      mathematics beyond the two shapes.
    - Calls through a function pointer (`callInd` with arguments), the
      `bindCallElse` error branch, and `bind`-shaped axiom/pointer calls
      have no arm: the count shape is the `CertBlock5` precedent, but no
      `Endblock`-level arm carries it here. Bodies needing them refuse in
      the printer (`CS001`).
    - `if` branches reuse `CertSeq` only: a call, a pointer write or a
      pointer return inside a branch refuses in the printer (`CS001`),
      even though the terminal layer could carry it. The 104 bodies need
      no branch, so the arm stays unwritten.
    - A `return` through a pointer in the MIDDLE of a body (a `durch`
      read bound by `let`) has no arm: only the terminal `retDurch`
      exists. The printer refuses it (`CS002`).
    - Call arguments print nothing: each must name a bare parameter place
      (checked in the printer), and the elaborated `Args` travel as proof
      (`End104Args`), filled at paste beside `?hp`. The `RufPasst` fills
      the same way. Which `Args` the surface call elaborates to is
      trust base at paste (the `ZeugnisStmt2.lean` term-identity booking):
      the `einzahlen` paste passes a fresh read-only `ptrOf`, not the
      caller's `rw` pointer, exactly as the `lean-g` export does.
    - Term identity (`print (elab x) = x`) is proved NOWHERE -- the
      `ZeugnisStmt2.lean` CUTS booking. The §4 terms are linked to their
      bodies by construction of the printer, pinned in
      `crates/gabbro-check/tests/certstmt.rs` (`reference_104_prints`).
    - Resource flow erases to `[]`: the pasted checks run over the held
      lock the export holds, so `darf` recomputes non-vacuously here
      (unlike the lock-free demo of `ZeugnisStmt104.lean`).
-/

#print axioms Gabbro.Grammatik.end104_sound
#print axioms Gabbro.Grammatik.zeugnisStmt104b_sound
#print axioms Gabbro.Grammatik.end104_sound_zeuge
#print axioms Gabbro.Grammatik.end104_retDurch_zeuge
#print axioms Gabbro.Grammatik.zeugnisStmt104b_sound_zeuge
#print axioms Gabbro.Grammatik.witCall104
#print axioms Gabbro.Grammatik.witCallArgs104
#print axioms Gabbro.Grammatik.witDurch104
#print axioms Gabbro.Grammatik.witDurchArgs104
#print axioms Gabbro.Grammatik.cert104_einzahlen
#print axioms Gabbro.Grammatik.args104_einzahlen
#print axioms Gabbro.Grammatik.cert104_lies
#print axioms Gabbro.Grammatik.args104_lies
