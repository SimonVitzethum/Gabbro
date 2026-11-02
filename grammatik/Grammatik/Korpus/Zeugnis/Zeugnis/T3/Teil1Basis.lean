module

public import Grammatik.Korpus.Zeugnis.Zeugnis.T2
meta import Grammatik.Korpus.Zeugnis.Zeugnis.T2

@[expose] public section



namespace Gabbro.Grammatik

/-- The place read: `T.slots[i].f` with `i` widened to the generated index
    type `0 .. 10`, under the held guard -- printed as the field `(0, 10)`. -/
example : GueltigAbleitung TestD [] [Res.held ()]
    (.slot () () (.wide 0 10 (.lit 3))) 0 10 := by decide

/-- FORGED index: a bare `3` is not of index type `0 .. 10` -- without the
    widening the slot has no range. -/
example : ¬ GueltigAbleitung TestD [] [Res.held ()]
    (.slot () () (.lit 3)) 0 10 := by decide

/-- FORGED guard: the widened index is right, but the hands are empty. -/
example : ¬ GueltigAbleitung TestD [] []
    (.slot () () (.wide 0 10 (.lit 3))) 0 10 := by decide

/-- End to end: a valid print YIELDS an accepted derivation. -/
example : ∃ _ : Expr TestD [] [] (.int 3 3), True :=
  zeugnis_sound (D := TestD) (Γ := []) (Λ := []) (.add (.lit 1) (.lit 2)) 3 3 (by decide)

/-- End to end over a read: a valid variable print yields its derivation. -/
example : ∃ _ : Expr TestD [.int 3 3] [] (.int 3 3), True :=
  zeugnis_sound (D := TestD) (.var 0) 3 3 (by decide)

/-! ## Blocks: straight-line statements over int bindings (CUT-5)

    `CertBlock` is the printed certificate for a `Block`: `bind` extends the
    context by the RECOMPUTED range, `call` covers nullary callees (the
    `params = []` and `gruende = 0` checks recomputed; `RufPasst` travels as
    proof -- see the CUT-5 remainder above), `ret`/`retWert` check the result
    shape and recompute the linear balance `Λ.Perm V.ende`. -/

inductive CertBlock (D : Deklaration) (V : Vertrag D) :
    Ctx → List (Res D) → List (Res D) → Type where
  | nil : CertBlock D V Γ Λ Λ
  | bind (e : CertExpr D) (lo hi : Int) (rest : CertBlock D V (.int lo hi :: Γ) Λ Λ') :
      CertBlock D V Γ Λ Λ'
  | call (f : D.Fn) (hp : RufPasst D V (D.signatur f) Λ)
      (rest : CertBlock D V Γ (nach D f Λ) Λ') : CertBlock D V Γ Λ Λ'
  | ret : CertBlock D V Γ Λ Λ
  | retWert (e : CertExpr D) (lo hi : Int) : CertBlock D V Γ Λ Λ

/-- Block validity: the structural checks the table recomputes -- sub-ranges,
    the nullary-call shape, the result shape, the linear balance. Decidable
    wherever the world is concrete (see `decGueltigBlock` below), so block
    acceptance and rejection both close by `decide`. -/
def certBlockGueltig (D : Deklaration) (V : Vertrag D) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : CertBlock D V Γ Λ Λ' → Prop
  | .nil => True
  | .bind e lo hi rest =>
    certRange D Γ Λ e = some (lo, hi) ∧ certBlockGueltig D V (.int lo hi :: Γ) Λ Λ' rest
  | .call f _ rest =>
    D.params f = [] ∧ D.gruende f = 0 ∧ certBlockGueltig D V Γ (nach D f Λ) Λ' rest
  | .ret => V.erg = none ∧ Λ.Perm V.ende
  | .retWert e lo hi =>
    V.erg = some (.int lo hi) ∧ certRange D Γ Λ e = some (lo, hi) ∧ Λ.Perm V.ende

/-- The validity predicate as `Decidable`, by structural recursion: each arm
    restates its equation, so typeclass search closes it from the pieces
    (`haveI` carries the tail). -/
instance decGueltigBlock (D : Deklaration) (V : Vertrag D) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (b : CertBlock D V Γ Λ Λ') :
    Decidable (certBlockGueltig D V Γ Λ Λ' b) :=
  match b with
  | .nil => inferInstanceAs (Decidable True)
  | .bind e lo hi rest =>
    haveI := decGueltigBlock D V (.int lo hi :: Γ) Λ Λ' rest
    inferInstanceAs
      (Decidable (certRange D Γ Λ e = some (lo, hi) ∧
        certBlockGueltig D V (.int lo hi :: Γ) Λ Λ' rest))
  | .call f _ rest =>
    haveI := decGueltigBlock D V Γ (nach D f Λ) Λ' rest
    inferInstanceAs
      (Decidable (D.params f = [] ∧ D.gruende f = 0 ∧
        certBlockGueltig D V Γ (nach D f Λ) Λ' rest))
  | .ret => inferInstanceAs (Decidable (V.erg = none ∧ Λ.Perm V.ende))
  | .retWert e lo hi =>
    inferInstanceAs
      (Decidable (V.erg = some (.int lo hi) ∧ certRange D Γ Λ e = some (lo, hi) ∧
        Λ.Perm V.ende))

/-- Block soundness: a valid block certificate IMPLIES the judgment -- there
    EXISTS an accepted `Block`. `bind` elaborates the bound expression through
    `zeugnis_sound` and extends the context; `call` forwards the carried
    `RufPasst` with the recomputed nullary shape; `ret`/`retWert` close the
    block with the recomputed balance. -/
theorem block_sound {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (b : CertBlock D V Γ Λ Λ') :
    certBlockGueltig D V Γ Λ Λ' b → ∃ _ : Block D V l Γ Λ Λ', True := by
  induction b with
  | nil => intro _; exact ⟨Block.nil, trivial⟩
  | bind e lo hi rest ih =>
    intro h
    simp only [certBlockGueltig] at h
    obtain ⟨he, hr⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi he
    obtain ⟨blk, _⟩ := ih hr
    exact ⟨Block.bind ee blk, trivial⟩
  | call f hp rest ih =>
    intro h
    simp only [certBlockGueltig] at h
    obtain ⟨hpar, hgr, hr⟩ := h
    obtain ⟨blk, _⟩ := ih hr
    exact ⟨Block.cons (Stmt.call f (by rw [hpar]; exact Args.nil) hp hgr) blk, trivial⟩
  | ret =>
    intro h
    simp only [certBlockGueltig] at h
    obtain ⟨he, hΛ⟩ := h
    exact ⟨Block.cons (Stmt.ret (by rw [he]; exact ErgExpr.empty) hΛ) Block.nil, trivial⟩
  | retWert e lo hi =>
    intro h
    simp only [certBlockGueltig] at h
    obtain ⟨he, hrng, hΛ⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi hrng
    exact ⟨Block.cons (Stmt.ret (by rw [he]; exact ErgExpr.val ee) hΛ) Block.nil, trivial⟩

/-! ### CUT-5 probes: bind, call, return -/

/-- A binding that ends the block without returning: `nil` is unconditionally
    valid -- the checks live in the statements, not in the sequencing. -/
example : certBlockGueltig TestD TestV [] [] []
    (.bind (.lit 1) 1 1 .nil) := by decide

/-- `return` with empty hands: the procedure contract holds nothing, so the
    empty balance is exact. -/
example : certBlockGueltig TestD TestV [] [] [] (.ret) := by decide

/-- BROKEN balance: a held lock with nowhere to return it -- provably no
    certificate. This is the linear failure, loud. -/
example : ¬ certBlockGueltig TestD TestV [] [Res.held ()] [Res.held ()] (.ret) := by decide

/-- `let x = 1; return x`: the binding recomputes `(1, 1)`, the return reads
    variable `0` at `(1, 1)` against a matching contract. -/
example : certBlockGueltig TestD TestVw [] [] []
    (.bind (.lit 1) 1 1 (.retWert (.var 0) 1 1)) := by decide +kernel

/-- MISMATCHED return: `x` is `(1, 1)`, claimed as `(2, 2)`. -/
example : ¬ certBlockGueltig TestD TestVw [] [] []
    (.bind (.lit 1) 1 1 (.retWert (.var 0) 2 2)) := by decide +kernel

/-- MISMATCHED binding: `1` claimed as `(9, 9)` -- the tail never gets its
    context, because the head already fails. -/
example : ¬ certBlockGueltig TestD TestVw [] [] []
    (.bind (.lit 1) 9 9 (.retWert (.var 0) 1 1)) := by decide

/-- The nullary call, then `return`: params empty and no reasons, so the
    table accepts and the balance holds behind it. -/
example : certBlockGueltig TestD TestV [] [] [] (.call false TestHp .ret) := by decide

/-- A call WITH a param is no nullary call: `RufPasst` goes through, but the
    `params = []` check fails -- the certificate is honestly rejected. -/
example : ¬ certBlockGueltig TestD TestV [] [] []
    (.call true TestHp1 .ret) := by decide

/-- End to end: a valid block print YIELDS an accepted block. -/
example : ∃ _ : Block TestD TestV false [] [] [], True :=
  block_sound (.call false TestHp .ret) (by decide)

#eval certRange TestD [] [] (.mul (.lit 2) (.lit 3))
#eval certRange TestD [] [] (.div (.lit 5) (.lit 0))
#eval certRange TestD [] [] (.sdiv (.lit 7) (.lit 2))
#eval certRange TestD [] [] (.bor 3 (.lit 6) (.lit 3))
#eval certRange TestD [.int 3 3] [] (.var 0)
#eval certRange TestD [] [Res.held ()] (.glob ())

#print axioms zeugnis_sound
#print axioms block_sound


end Gabbro.Grammatik
