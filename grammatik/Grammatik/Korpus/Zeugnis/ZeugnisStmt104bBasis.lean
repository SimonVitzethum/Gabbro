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
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt2
public import Grammatik.Korpus.Programme.Export104
@[expose] public section


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
    D.capTab (D.tableSpace t) n = some t ∧ certRange D Γ Λ i = some (0, D.count t - 1) ∧
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
    inferInstanceAs (Decidable (D.capTab (D.tableSpace t) n = some t ∧
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
    {rw : Bool} (p : Expr D Γ Λ (.ptr (.table n (true, rw) (D.tableSpace t)))) :
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
    exact ⟨Endblock.ret (by rw [he]; exact ErgExpr.empty) hΛ, trivial⟩
  | retWert e lo hi =>
    intro h
    simp only [certEnd104Gueltig] at h
    obtain ⟨he, hrng, hΛ⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi hrng
    exact ⟨Endblock.ret (by rw [he]; exact ErgExpr.val ee) hΛ, trivial⟩
  | retDurch t f n i p =>
    intro h
    simp only [certEnd104Gueltig] at h
    obtain ⟨htab, hii, herg, hL, hperm⟩ := h
    obtain ⟨ei, _⟩ := zeugnis_sound i 0 (D.count t - 1) hii
    exact ⟨Endblock.ret
      (by rw [herg]; exact ErgExpr.val (Expr.thru p t htab f ei hL))
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


end Gabbro.Grammatik
