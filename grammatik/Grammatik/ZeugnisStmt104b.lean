/-
  File:     Grammatik/ZeugnisStmt104b.lean
  Subject:  TRANSFER certificates for `beispiele/104-referenz.gab` (lane 155).

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
  of `beispiele/104-referenz.gab` (proofs filled beside the printed `?hp`),
  each accepted by `decide` and pushed through `zeugnisStmt104b_sound`.
-/
import Grammatik.ZeugnisStmt2
import Grammatik.Export104

namespace Gabbro.Grammatik

/-- Body prints with calls-with-arguments and pointer returns: reuse
    (`lift2`), single old steps (`cons1` for `CertStmt`, `cons2` for
    `CertStmt2`), integer bindings (`bind`), calls with arguments
    (`consCall`: callee, argument count, carried resources, carried
    `RufPasst`), plain terminals (`ret`, `retWert`) and the pointer return
    (`retDurch`: table, field, table number, index certificate). -/
inductive CertEnd104 (D : Deklaration) (V : Vertrag D) where
  | lift2 (e : CertEnd2 D V)
  | cons1 (s : CertStmt D V) (Λm : List (Res D)) (rest : CertEnd104 D V)
  | cons2 (s : CertStmt2 D V) (Λm : List (Res D)) (rest : CertEnd104 D V)
  | bind (e : CertExpr D) (lo hi : Int) (rest : CertEnd104 D V)
  | consCall (f : D.Fn) (nargs : Nat) (Λc : List (Res D))
    (hp : RufPasst D V (D.signatur f) Λc) (rest : CertEnd104 D V)
  | ret
  | retWert (e : CertExpr D) (lo hi : Int)
  | retDurch (t : D.Tab) (f : D.Feld t) (n : Nat) (i : CertExpr D)

/-! ## Validity: every recomputable side condition

    `consCall` recomputes the argument-count shape, the reason freedom and
    the holdings equation (the `RufPasst` travels as proof, the `Block5Args`
    precedent); `retDurch` the table-number equation, the generated index
    shape, the field-type equation against the result type, and the guard
    (the pointer travels as proof, the `durch` precedent of `cut4_sound`).
    Everything else delegates to the two older layers. -/

/-- Body validity: the old layers delegate, `consCall`/`retDurch` recompute
    their equations, `bind` extends by the recomputed range. -/
def certEnd104Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) : CertEnd104 D V → Prop
  | .lift2 e => certEnd2Gueltig D V l Γ Λ e
  | .cons1 s Λm rest =>
    certStmtGueltig D V l Γ Λ Λm s ∧ certEnd104Gueltig D V l Γ Λm rest
  | .cons2 s Λm rest =>
    certStmt2Gueltig D V l Γ Λ Λm s ∧ certEnd104Gueltig D V l Γ Λm rest
  | .bind e lo hi rest =>
    certRange D Γ Λ e = some (lo, hi) ∧
      certEnd104Gueltig D V l (.int lo hi :: Γ) Λ rest
  | .consCall f nargs Λc _ rest =>
    (D.params f).length = nargs ∧ D.gruende f = 0 ∧ Λ = Λc ∧
      certEnd104Gueltig D V l Γ (nach D f Λ) rest
  | .ret => V.erg = none ∧ Λ.Perm V.ende
  | .retWert e lo hi =>
    V.erg = some (.int lo hi) ∧ certRange D Γ Λ e = some (lo, hi) ∧
      Λ.Perm V.ende
  | .retDurch t f n i =>
    D.tabNr n = some t ∧ certRange D Γ Λ i = some (0, D.count t - 1) ∧
      V.erg = some (D.typ t f) ∧ darf D t Λ ∧ Λ.Perm V.ende

/-- Body validity as `Decidable`, by structural recursion. -/
def decEnd104Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (e : CertEnd104 D V) :
    Decidable (certEnd104Gueltig D V l Γ Λ e) :=
  match e with
  | .lift2 c => inferInstanceAs (Decidable (certEnd2Gueltig D V l Γ Λ c))
  | .cons1 s Λm rest =>
    haveI := decStmtGueltig D V l Γ Λ Λm s
    haveI := decEnd104Gueltig D V l Γ Λm rest
    inferInstanceAs (Decidable (certStmtGueltig D V l Γ Λ Λm s ∧
      certEnd104Gueltig D V l Γ Λm rest))
  | .cons2 s Λm rest =>
    haveI := decStmt2Gueltig D V l Γ Λ Λm s
    haveI := decEnd104Gueltig D V l Γ Λm rest
    inferInstanceAs (Decidable (certStmt2Gueltig D V l Γ Λ Λm s ∧
      certEnd104Gueltig D V l Γ Λm rest))
  | .bind e lo hi rest =>
    haveI := decEnd104Gueltig D V l (.int lo hi :: Γ) Λ rest
    inferInstanceAs (Decidable (certRange D Γ Λ e = some (lo, hi) ∧
      certEnd104Gueltig D V l (.int lo hi :: Γ) Λ rest))
  | .consCall f nargs Λc _ rest =>
    haveI := decEnd104Gueltig D V l Γ (nach D f Λ) rest
    inferInstanceAs (Decidable ((D.params f).length = nargs ∧
      D.gruende f = 0 ∧ Λ = Λc ∧
      certEnd104Gueltig D V l Γ (nach D f Λ) rest))
  | .ret => inferInstanceAs (Decidable (V.erg = none ∧ Λ.Perm V.ende))
  | .retWert e lo hi =>
    inferInstanceAs (Decidable (V.erg = some (.int lo hi) ∧
      certRange D Γ Λ e = some (lo, hi) ∧ Λ.Perm V.ende))
  | .retDurch t f n i =>
    inferInstanceAs (Decidable (D.tabNr n = some t ∧
      certRange D Γ Λ i = some (0, D.count t - 1) ∧
      V.erg = some (D.typ t f) ∧ darf D t Λ ∧ Λ.Perm V.ende))

instance instDecEnd104 (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (e : CertEnd104 D V) :
    Decidable (certEnd104Gueltig D V l Γ Λ e) :=
  decEnd104Gueltig D V l Γ Λ e

/-! ## The carried proofs: argument lists and pointers

    `CertEnd104` carries counts and equations only. Each call's argument
    list (an `Args` at arbitrary parameter types, which `CertExpr` cannot
    print) and each pointer return's pointer travel beside the print as the
    explicit `End104Args` hypothesis of `end104_sound` below -- the
    `Block5Args`/`Cut4Ptr` precedent, not faked with invented terms. -/

/-- The proofs each body print needs: the argument list behind every
    `consCall` (at the resources the call fires in), the pointer behind
    every `retDurch`. -/
inductive End104Args (D : Deklaration) (V : Vertrag D) :
    (Γ : Ctx) → (Λ : List (Res D)) → CertEnd104 D V → Type where
  | lift2 (e : CertEnd2 D V) : End104Args D V Γ Λ (.lift2 e)
  | cons1 (s : CertStmt D V) (Λm : List (Res D)) {rest : CertEnd104 D V}
    (tail : End104Args D V Γ Λm rest) :
    End104Args D V Γ Λ (.cons1 s Λm rest)
  | cons2 (s : CertStmt2 D V) (Λm : List (Res D)) {rest : CertEnd104 D V}
    (tail : End104Args D V Γ Λm rest) :
    End104Args D V Γ Λ (.cons2 s Λm rest)
  | bind104 (e : CertExpr D) (lo hi : Int) {rest : CertEnd104 D V}
    (tail : End104Args D V (.int lo hi :: Γ) Λ rest) :
    End104Args D V Γ Λ (.bind e lo hi rest)
  | consCall (f : D.Fn) (nargs : Nat) (Λc : List (Res D))
    (hp : RufPasst D V (D.signatur f) Λc)
    (args : Args D Γ Λ (D.params f)) {rest : CertEnd104 D V}
    (tail : End104Args D V Γ (nach D f Λ) rest) :
    End104Args D V Γ Λ (.consCall f nargs Λc hp rest)
  | ret : End104Args D V Γ Λ .ret
  | retWert (e : CertExpr D) (lo hi : Int) :
    End104Args D V Γ Λ (.retWert e lo hi)
  | retDurch (t : D.Tab) (f : D.Feld t) (n : Nat) (i : CertExpr D)
    {rw : Bool} (p : Expr D Γ Λ (.ptr n rw)) :
    End104Args D V Γ Λ (.retDurch t f n i)

/-- Body soundness: a valid body print IMPLIES the judgement behind the
    carried proofs -- there EXISTS an accepted `Endblock`. `lift2` reuses
    the older layer, `cons1`/`cons2` thread through both statement layers,
    `bind` extends by the recomputed range, `consCall` forwards the carried
    `RufPasst` with the supplied arguments, `retDurch` rebuilds the pointer
    read. Every premise is used: the place (`D V l Γ Λ`), the print (`e`),
    the proofs (`a`), the acceptance (`h`). -/
theorem end104_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (e : CertEnd104 D V) (a : End104Args D V Γ Λ e)
    (h : certEnd104Gueltig D V l Γ Λ e) :
    ∃ _ : Endblock D V l Γ Λ, True := by
  revert h
  induction a with
  | lift2 c =>
    intro h
    obtain ⟨c', _⟩ := end2_sound D V l _ _ c h
    exact ⟨c', trivial⟩
  | cons1 s Λm tail ih =>
    intro h
    simp only [certEnd104Gueltig] at h
    obtain ⟨hs, hrest⟩ := h
    obtain ⟨s', _⟩ := stmt_sound D V l _ _ _ s hs
    obtain ⟨r', _⟩ := ih hrest
    exact ⟨Endblock.cons s' r', trivial⟩
  | cons2 s Λm tail ih =>
    intro h
    simp only [certEnd104Gueltig] at h
    obtain ⟨hs, hrest⟩ := h
    obtain ⟨s', _⟩ := stmt2_sound D V l _ _ _ s hs
    obtain ⟨r', _⟩ := ih hrest
    exact ⟨Endblock.cons s' r', trivial⟩
  | bind104 e lo hi tail ih =>
    intro h
    simp only [certEnd104Gueltig] at h
    obtain ⟨he, hrest⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi he
    obtain ⟨r', _⟩ := ih hrest
    exact ⟨Endblock.bind ee r', trivial⟩
  | consCall f nargs Λc hp args tail ih =>
    intro h
    simp only [certEnd104Gueltig] at h
    obtain ⟨_, hgr, hΛc, hrest⟩ := h
    subst hΛc
    obtain ⟨blk, _⟩ := ih hrest
    exact ⟨Endblock.cons (Stmt.call f args hp hgr) blk, trivial⟩
  | ret =>
    intro h
    simp only [certEnd104Gueltig] at h
    obtain ⟨he, hΛ⟩ := h
    exact ⟨Endblock.ret (by rw [he]; exact ErgExpr.keine) hΛ, trivial⟩
  | retWert e lo hi =>
    intro h
    simp only [certEnd104Gueltig] at h
    obtain ⟨he, hrng, hΛ⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi hrng
    exact ⟨Endblock.ret (by rw [he]; exact ErgExpr.wert ee) hΛ, trivial⟩
  | retDurch t f n i p =>
    intro h
    simp only [certEnd104Gueltig] at h
    obtain ⟨htab, hii, herg, hL, hperm⟩ := h
    obtain ⟨ei, _⟩ := zeugnis_sound i 0 (D.count t - 1) hii
    exact ⟨Endblock.ret
      (by rw [herg]; exact ErgExpr.wert (Expr.durch p t htab f ei hL))
      hperm, trivial⟩

/-- Body checker: `true` iff the body print recomputes. -/
def certEnd104Ok (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (c : CertEnd104 D V) : Bool :=
  decide (certEnd104Gueltig D V l Γ Λ c)

/-- Certificate soundness: a valid body print IMPLIES the judgement --
    there EXISTS an accepted `Endblock`. Every premise is used: the place
    (`D V l Γ Λ`), the print (`c`), the proofs (`a`), the acceptance (`h`). -/
theorem zeugnisStmt104b_sound (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ : List (Res D)) (c : CertEnd104 D V)
    (a : End104Args D V Γ Λ c) (h : certEnd104Ok D V l Γ Λ c = true) :
    ∃ _ : Endblock D V l Γ Λ, True :=
  end104_sound D V l Γ Λ c a (of_decide_eq_true h)

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
  (.retDurch _ _ _ _ (Expr.ptrOf () 0 rfl true))

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
    `gabbro certificate beispiele/104-referenz.gab` (section S, lane 155;
    pinned in `crates/gabbro-check/tests/certstmt.rs` as
    `reference_104_prints`), elaborated against the `lean-g` export it was
    printed for (`Export104.lean`: `gD`, `gCtx_*`, `gL_*`). Surface names
    qualify to the export's constructors; the printed `?hp` fills with the
    export's `gHp_einzahlen_lies` (the `Args` list beside it passes the
    pointer the export passes: a fresh read-only `ptrOf`, since the
    caller's `rw` pointer is no `.ptr 0 false`); the pointer behind
    `retDurch` is the parameter itself. Each `example` runs the Lean
    checker (`certEnd104Ok ... = true` by `decide`); each soundness
    corollary applies `zeugnisStmt104b_sound`. Contexts list the head
    first: `gCtx_einzahlen = [.ptr 0 true, .index 2, .int 0 10]`, so the
    index variable `i` reads as `(.var 1)` and recomputes `(0, 1)`. -/

/-- Verbatim printer output for `einzahlen`: the pointer write with the
    index variable, the `lies(k, i)` call, the bare return. -/
def cert104_einzahlen :
    CertEnd104 G104_referenz.gD
      (vertragVon G104_referenz.gD G104_referenz.g_einzahlen) :=
  (.cons2
    (.assignDurch G104_referenz.GTab.Konto G104_referenz.GKontoFeld.stand
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
      (.cons (Expr.ptrOf G104_referenz.GTab.Konto 0 rfl false)
        (.cons (Expr.var (.dort .hier)) .nil))
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
  (.retDurch _ _ _ _ (Expr.var .hier))

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
