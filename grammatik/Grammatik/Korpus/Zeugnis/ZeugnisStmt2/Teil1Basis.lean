module

public import Grammatik.Korpus.Zeugnis.ZeugnisStmt

@[expose] public section



namespace Gabbro.Grammatik

/-- Case-list certificates for `Stmt.onTag`: one `CertSeq` per `sum` case,
    the case pinned in the constructor (the `Arms` correspondence). -/
inductive CertArms2 (D : Deklaration) (V : Vertrag D) : List (Option Ty) → Type where
  | nil : CertArms2 D V []
  | cons (c : Option Ty) (b : CertSeq D V) {cs : List (Option Ty)}
    (rest : CertArms2 D V cs) : CertArms2 D V (c :: cs)

/-- Reason-list certificates for `Stmt.onGrund`: one `CertSeq` per reason
    (the `GrundArms` correspondence, length `n`). -/
inductive CertGrundArms2 (D : Deklaration) (V : Vertrag D) : Nat → Type where
  | nil : CertGrundArms2 D V 0
  | cons (b : CertSeq D V) {n : Nat} (rest : CertGrundArms2 D V n) :
    CertGrundArms2 D V (n + 1)

/-- The four remaining `Stmt` shapes as plain data. `assignDurch` names the
    table number (the `tabNr` equation recomputes, the pointer is rebuilt
    from it); `callInd` names the callee and its signature number (the
    `sig` equation recomputes, nullary only, the R-2 fragment, `RufPasst`
    travels as proof); `onTag`/`onGrund` carry the scrutinee shapes the
    CUT-3 rows already print (`fall` payload check, `r < n`). -/
inductive CertStmt2 (D : Deklaration) (V : Vertrag D) where
  | assignThru (t : D.Tab) (f : D.Feld t) (n : Nat) (rw : Bool) (i e : CertExpr D)
  | callInd (f : D.Fn) (n : Nat) (Λc : List (Res D)) (hp : RufPasst D V (D.sigNr n) Λc)
  | onTag (cs : List (Option Ty)) (i : Nat) (p : Option (CertExpr D))
    (arms : CertArms2 D V cs)
  | onWhy (n r : Nat) (arms : CertGrundArms2 D V n)

/-! ## Arm validity: every side condition recomputed -/

/-- Case-list validity: each arm recomputes at its pinned case context
    (`ArmCtx`), the resource flow shared across arms. -/
def certArms2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : {cs : List (Option Ty)} →
    CertArms2 D V cs → Prop
  | [], .nil => Λ = Λ'
  | _ :: _, .cons c b rest =>
    certSeqGueltig D V l (ArmCtx Γ c) Λ Λ' b ∧ certArms2Gueltig D V l Γ Λ Λ' rest

/-- Reason-list validity: each of the `n` arms recomputes at the shared
    flow (reasons bind nothing, like `GrundArms.cons`). -/
def certGrundArms2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : {n : Nat} → CertGrundArms2 D V n → Prop
  | 0, .nil => Λ = Λ'
  | _ + 1, .cons b rest =>
    certSeqGueltig D V l Γ Λ Λ' b ∧ certGrundArms2Gueltig D V l Γ Λ Λ' rest

/-- Arm validity as `Decidable`, by structural recursion. -/
def decArms2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) {cs : List (Option Ty)}
    (a : CertArms2 D V cs) : Decidable (certArms2Gueltig D V l Γ Λ Λ' a) :=
  match a with
  | .nil => inferInstanceAs (Decidable (Λ = Λ'))
  | .cons c b rest =>
    haveI := decSeqGueltig D V l (ArmCtx Γ c) Λ Λ' b
    haveI := decArms2Gueltig D V l Γ Λ Λ' rest
    inferInstanceAs (Decidable (certSeqGueltig D V l (ArmCtx Γ c) Λ Λ' b ∧
      certArms2Gueltig D V l Γ Λ Λ' rest))

instance instDecArms2 (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) {cs : List (Option Ty)}
    (a : CertArms2 D V cs) : Decidable (certArms2Gueltig D V l Γ Λ Λ' a) :=
  decArms2Gueltig D V l Γ Λ Λ' a

/-- Reason-list validity as `Decidable`, by structural recursion. -/
def decGrundArms2Gueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) {n : Nat}
    (a : CertGrundArms2 D V n) :
    Decidable (certGrundArms2Gueltig D V l Γ Λ Λ' a) :=
  match a with
  | .nil => inferInstanceAs (Decidable (Λ = Λ'))
  | .cons b rest =>
    haveI := decSeqGueltig D V l Γ Λ Λ' b
    haveI := decGrundArms2Gueltig D V l Γ Λ Λ' rest
    inferInstanceAs (Decidable (certSeqGueltig D V l Γ Λ Λ' b ∧
      certGrundArms2Gueltig D V l Γ Λ Λ' rest))

instance instDecGrundArms2 (D : Deklaration) (V : Vertrag D) (l : Bool)
    (Γ : Ctx) (Λ Λ' : List (Res D)) {n : Nat}
    (a : CertGrundArms2 D V n) :
    Decidable (certGrundArms2Gueltig D V l Γ Λ Λ' a) :=
  decGrundArms2Gueltig D V l Γ Λ Λ' a

/-- Case-list soundness: a valid arm print elaborates to `Arms`. Every
    hypothesis is used: the head arm via `seq_sound`, the tail via the
    induction. -/
theorem arms2_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) {cs : List (Option Ty)}
    (a : CertArms2 D V cs) (h : certArms2Gueltig D V l Γ Λ Λ' a) :
    ∃ _ : Arms D V l Γ Λ Λ' cs, True := by
  revert h
  match a with
  | .nil =>
    intro h
    simp only [certArms2Gueltig] at h
    subst h
    exact ⟨Arms.nil, trivial⟩
  | .cons c b rest =>
    intro h
    simp only [certArms2Gueltig] at h
    obtain ⟨hb, hrest⟩ := h
    obtain ⟨b', _⟩ := seq_sound D V l (ArmCtx Γ c) Λ Λ' b hb
    obtain ⟨r', _⟩ := arms2_sound D V l Γ Λ Λ' rest hrest
    exact ⟨Arms.cons b' r', trivial⟩

/-- Reason-list soundness: a valid reason print elaborates to `GrundArms`. -/
theorem grundArms2_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) {n : Nat}
    (a : CertGrundArms2 D V n) (h : certGrundArms2Gueltig D V l Γ Λ Λ' a) :
    ∃ _ : GrundArms D V l Γ Λ Λ' n, True := by
  revert h
  match a with
  | .nil =>
    intro h
    simp only [certGrundArms2Gueltig] at h
    subst h
    exact ⟨GrundArms.nil, trivial⟩
  | .cons b rest =>
    intro h
    simp only [certGrundArms2Gueltig] at h
    obtain ⟨hb, hrest⟩ := h
    obtain ⟨b', _⟩ := seq_sound D V l Γ Λ Λ' b hb
    obtain ⟨r', _⟩ := grundArms2_sound D V l Γ Λ Λ' rest hrest
    exact ⟨GrundArms.cons b' r', trivial⟩

/-! ## Typed scrutinees: the CUT-3 rows pinned to their types

    `cut3_sound` elaborates to an existential type; `Stmt.onTag` needs the
    scrutinee at EXACTLY `.sum cs`. The `fall` case below mirrors that
    proof with the type pinned (same payload equations, same
    `certCut3PayloadOk` check). -/

/-- A valid `fall` print elaborates to a `sum` scrutinee at exactly `cs`.
    Every hypothesis is used: the payload equations via `zeugnis_sound`,
    the length fact for the `Fin`, the check for the payload shape. -/
theorem fall_typed (D : Deklaration) (Γ : Ctx) (Λ : List (Res D))
    (cs : List (Option Ty)) (i : Nat)
    (p : Option (CertExpr D))
    (h : i < cs.length ∧ certCut3PayloadOk D Γ Λ cs[i]? p = true) :
    ∃ _ : Expr D Γ Λ (.sum cs), True := by
  obtain ⟨hi, hp⟩ := h
  cases hq : cs[i]? with
  | none =>
    have hle : cs.length ≤ i := (List.getElem?_eq_none_iff).mp hq
    omega
  | some slot =>
    rw [hq] at hp
    obtain ⟨h', hget⟩ := (List.getElem?_eq_some_iff).mp hq
    have hget' : cs.get ⟨i, hi⟩ = slot := by
      rw [List.get_eq_getElem]
      exact hget
    cases slot with
    | none =>
      cases p with
      | none =>
        simp only [certCut3PayloadOk] at hp
        exact ⟨Expr.case cs ⟨i, hi⟩ (hget'.symm ▸ NutzlastExpr.empty),
          trivial⟩
      | some _ =>
        simp only [certCut3PayloadOk, Bool.false_eq_true] at hp
    | some q =>
      obtain ⟨lo, hi2⟩ := q
      cases p with
      | none =>
        simp only [certCut3PayloadOk, Bool.false_eq_true] at hp
      | some e =>
        simp only [certCut3PayloadOk] at hp
        have he : certRange D Γ Λ e = some (lo, hi2) := of_decide_eq_true hp
        obtain ⟨ee, _⟩ := zeugnis_sound e lo hi2 he
        exact ⟨Expr.case cs ⟨i, hi⟩ (hget'.symm ▸ NutzlastExpr.val ee),
          trivial⟩

end Gabbro.Grammatik
