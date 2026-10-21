/-
  File:     Grammatik/ZeugnisStmt.lean
  Subject:  Certificate soundness for STATEMENTS (T1 of PLAN-TRANSLATION-VALIDATION.md).

  Extends `Zeugnis.lean` (expressions) to statements: `CertCond`/`CertStmt`/
  `CertSeq`/`CertEnd` are plain-data certificates, the `*Gueltig` predicates
  recompute every side condition (`darf`, `V.schreibt`, rank order, index
  shapes, linear balance), and `zeugnisStmt_sound` elaborates a valid
  certificate to a well-typed `Endblock` (the run statement).
  The Rust printer (`certemit.rs`) covers expressions only; the statement
  print format is designed in the docstrings below for the transfer phase.
-/
import Grammatik.Korpus.Zeugnis.Zeugnis
import Grammatik.Korpus.Referenz.ReferenzB

namespace Gabbro.Grammatik

/-- Boolean conditions as plain data: the `ite`/`retry`/`forever`/`pruefung`
    scrutinees over the int fragment (`CertExpr`) plus variable reads. -/
inductive CertCond (D : Deklaration) where
  | tru
  | fls
  | var (k : Nat)
  | lt (a b : CertExpr D)
  | le (a b : CertExpr D)
  | eq (a b : CertExpr D)
  | and (a b : CertCond D)
  | or (a b : CertCond D)
  | not (a : CertCond D)

/-- The `bool` range of the `k`-th variable of `Γ`, if it is bool-typed. -/
def ctxBoolTyp : Ctx → Nat → Option Unit
  | .bool :: _, 0 => some ()
  | _ :: _, 0 => none
  | _ :: Γ, k + 1 => ctxBoolTyp Γ k
  | [], _ => none

/-- Condition validity, recomputed: comparisons need int ranges on both
    sides, variables a `bool` entry, connectives valid parts. -/
def certCondGueltig (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) :
    CertCond D → Prop
  | .tru => True
  | .fls => True
  | .var k => ctxBoolTyp Γ k ≠ none
  | .lt a b => certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none
  | .le a b => certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none
  | .eq a b => certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none
  | .and a b => certCondGueltig D Γ Λ a ∧ certCondGueltig D Γ Λ b
  | .or a b => certCondGueltig D Γ Λ a ∧ certCondGueltig D Γ Λ b
  | .not a => certCondGueltig D Γ Λ a

/-- What `ctxBoolTyp` promises: a `some` names a `bool` variable. -/
theorem ctxBoolTyp_var (Γ : Ctx) (k : Nat) (h : ctxBoolTyp Γ k = some ()) :
    ∃ _ : Var Γ .bool, True := by
  induction Γ generalizing k with
  | nil =>
    cases k <;> simp [ctxBoolTyp] at h
  | cons τ Γ ih =>
    cases k with
    | zero =>
      cases τ with
      | bool =>
        simp [ctxBoolTyp] at h
        exact ⟨.here, trivial⟩
      | int => simp [ctxBoolTyp] at h
      | opt => simp [ctxBoolTyp] at h
      | sum => simp [ctxBoolTyp] at h
      | why => simp [ctxBoolTyp] at h
      | never => simp [ctxBoolTyp] at h
      | fl => simp [ctxBoolTyp] at h
      | fnptr => simp [ctxBoolTyp] at h
      | ptr => simp [ctxBoolTyp] at h
    | succ k =>
      simp [ctxBoolTyp] at h
      obtain ⟨x, _⟩ := ih k h
      exact ⟨.there x, trivial⟩

/-- Condition validity as `Decidable`, by structural recursion. -/
def decCondGueltig (D : Deklaration) (Γ : Ctx) (Λ : List (Res D))
    (c : CertCond D) : Decidable (certCondGueltig D Γ Λ c) :=
  match c with
  | .tru => inferInstanceAs (Decidable True)
  | .fls => inferInstanceAs (Decidable True)
  | .var k => inferInstanceAs (Decidable (ctxBoolTyp Γ k ≠ none))
  | .lt a b =>
    inferInstanceAs
      (Decidable (certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none))
  | .le a b =>
    inferInstanceAs
      (Decidable (certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none))
  | .eq a b =>
    inferInstanceAs
      (Decidable (certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none))
  | .and a b =>
    haveI := decCondGueltig D Γ Λ a
    haveI := decCondGueltig D Γ Λ b
    inferInstanceAs
      (Decidable (certCondGueltig D Γ Λ a ∧ certCondGueltig D Γ Λ b))
  | .or a b =>
    haveI := decCondGueltig D Γ Λ a
    haveI := decCondGueltig D Γ Λ b
    inferInstanceAs
      (Decidable (certCondGueltig D Γ Λ a ∧ certCondGueltig D Γ Λ b))
  | .not a =>
    haveI := decCondGueltig D Γ Λ a
    inferInstanceAs (Decidable (certCondGueltig D Γ Λ a))

instance instDecCond (D : Deklaration) (Γ : Ctx) (Λ : List (Res D))
    (c : CertCond D) : Decidable (certCondGueltig D Γ Λ c) :=
  decCondGueltig D Γ Λ c

/-- Condition soundness: a valid condition print elaborates to a `bool`
    expression. Every hypothesis is used: range facts via `zeugnis_sound`,
    variable facts via `ctxBoolTyp_var`, tails via the induction. -/
theorem cond_sound {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (c : CertCond D) (h : certCondGueltig D Γ Λ c) :
    ∃ _ : Expr D Γ Λ .bool, True := by
  induction c with
  | tru => exact ⟨Expr.tru, trivial⟩
  | fls => exact ⟨Expr.fls, trivial⟩
  | var k =>
    simp only [certCondGueltig] at h
    cases hk : ctxBoolTyp Γ k with
    | none => exact absurd hk h
    | some u =>
      cases u with
      | unit =>
        simp only [hk] at h
        obtain ⟨x, _⟩ := ctxBoolTyp_var Γ k hk
        exact ⟨Expr.var x, trivial⟩
  | lt a b =>
    simp only [certCondGueltig] at h
    obtain ⟨ha, hb⟩ := h
    cases ra : certRange D Γ Λ a with
    | none => exact absurd ra ha
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases rb : certRange D Γ Λ b with
      | none => exact absurd rb hb
      | some q =>
        obtain ⟨l2, h2⟩ := q
        obtain ⟨ea, _⟩ := zeugnis_sound a l1 h1 ra
        obtain ⟨eb, _⟩ := zeugnis_sound b l2 h2 rb
        exact ⟨Expr.lt ea eb, trivial⟩
  | le a b =>
    simp only [certCondGueltig] at h
    obtain ⟨ha, hb⟩ := h
    cases ra : certRange D Γ Λ a with
    | none => exact absurd ra ha
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases rb : certRange D Γ Λ b with
      | none => exact absurd rb hb
      | some q =>
        obtain ⟨l2, h2⟩ := q
        obtain ⟨ea, _⟩ := zeugnis_sound a l1 h1 ra
        obtain ⟨eb, _⟩ := zeugnis_sound b l2 h2 rb
        exact ⟨Expr.le ea eb, trivial⟩
  | eq a b =>
    simp only [certCondGueltig] at h
    obtain ⟨ha, hb⟩ := h
    cases ra : certRange D Γ Λ a with
    | none => exact absurd ra ha
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases rb : certRange D Γ Λ b with
      | none => exact absurd rb hb
      | some q =>
        obtain ⟨l2, h2⟩ := q
        obtain ⟨ea, _⟩ := zeugnis_sound a l1 h1 ra
        obtain ⟨eb, _⟩ := zeugnis_sound b l2 h2 rb
        exact ⟨Expr.eq ea eb, trivial⟩
  | and a b iha ihb =>
    simp only [certCondGueltig] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨ea, _⟩ := iha ha
    obtain ⟨eb, _⟩ := ihb hb
    exact ⟨Expr.and ea eb, trivial⟩
  | or a b iha ihb =>
    simp only [certCondGueltig] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨ea, _⟩ := iha ha
    obtain ⟨eb, _⟩ := ihb hb
    exact ⟨Expr.or ea eb, trivial⟩
  | not a ih =>
    simp only [certCondGueltig] at h
    obtain ⟨ea, _⟩ := ih h
    exact ⟨Expr.not ea, trivial⟩

/-! ## Statement certificates: plain data over the int fragment

    `CertStmt` mirrors one `Stmt`, `CertSeq` one `Block`, `CertEnd` one
    `Endblock`. Index, field and result ranges travel as DATA (`lo`/`hi`,
    `von`/`nach`); every side condition the table can recompute
    (`certRange` facts, `darf`/`gdarf`, `V.schreibt`, rank order, index
    shapes, linear balance) is a validity equation, never a carried proof.
    The one exception is `RufPasst`: it quantifies over arbitrary carrier
    types, so no range table can recompute it -- it travels AS PROOF with
    the resource list it speaks about (`Λc`), and validity equates that
    list with the context one (the `CertBlock.call` precedent of
    `Zeugnis.lean`). -/

mutual
/-- One statement as plain data. The `lo`/`hi` on `assignVar` name the
    claimed variable type; on `schreibBytes` the claimed index range; the
    `RufPasst` of `call` travels as proof over the carried `Λc`. -/
inductive CertStmt (D : Deklaration) (V : Vertrag D) where
  | assignSlot (t : D.Tab) (f : D.Feld t) (i e : CertExpr D)
  | assignVar (k : Nat) (lo hi : Int) (e : CertExpr D)
  | assignGlob (g : D.Glob) (e : CertExpr D)
  | putBytes (t : D.Tab) (f : D.Feld t) (n : Nat) (lo hi : Int)
      (i e : CertExpr D)
  | call (f : D.Fn) (Λc : List (Res D)) (hp : RufPasst D V (D.signatur f) Λc)
  | ite (c : CertCond D) (t e : CertSeq D V)
  | onOption (e : CertExpr D) (n : Int) (p a : CertSeq D V)
  | locks (L : D.Lock) (body : CertSeq D V)
  | breaking (i : D.Inv) (body : CertSeq D V)
  | shift (t : D.Tab) (f : D.Feld t) (lo hi von nach : Int)
      (i : CertExpr D)
  | publish (g : D.Glob) (e : CertExpr D) (payload : List D.Glob)
  | regWrite (r : D.Reg) (e : CertExpr D)
  | advances (m : D.Marke) (a : Nat)
  | retires (m : D.Marke) (s : Nat) (a : D.Annahme)
  | traverse (t : D.Tab) (inv : CertCond D) (body : CertSeq D V)
  | retry (n : Nat) (bis : CertCond D) (body ueber : CertSeq D V)
  | forever (a : D.Annahme) (inv : CertCond D) (body : CertSeq D V)
  | ret
  | retWert (e : CertExpr D) (lo hi : Int)
  | retWhy (r : Nat)
  | leave
  | next

/-- One block as plain data: `cons` carries the intermediate resource
    list `Λm` (checker-known data), `bind` the claimed range. -/
inductive CertSeq (D : Deklaration) (V : Vertrag D) where
  | nil
  | cons (s : CertStmt D V) (Λm : List (Res D)) (rest : CertSeq D V)
  | bind (e : CertExpr D) (lo hi : Int) (rest : CertSeq D V)
  | bindCall (f : D.Fn) (lo hi : Int) (Λc : List (Res D))
      (hp : RufPasst D V (D.signatur f) Λc) (rest : CertSeq D V)
  | bindCallElse (f : D.Fn) (lo hi : Int) (Λc : List (Res D))
      (hp : RufPasst D V (D.signatur f) Λc) (err : CertEnd D V)
      (rest : CertSeq D V)
  | regRead (r : D.Reg) (lo hi : Int) (rest : CertSeq D V)
  | regReadElse (r : D.Reg) (zusage : CertCond D) (sonst : CertEnd D V)
      (rest : CertSeq D V)
  | awaits (g : D.Glob) (payload : List D.Glob) (lo hi : Int)
      (rest : CertSeq D V)
  | exchange (g : D.Glob) (lo hi : Int) (neu : CertExpr D)
      (rest : CertSeq D V)
  | narrow (e : CertExpr D) (lo hi lo' hi' : Int) (sonst : CertEnd D V)
      (rest : CertSeq D V)
  | check (c : CertCond D) (sonst : CertEnd D V) (rest : CertSeq D V)

/-- One non-falling block as plain data (the body a program carries). -/
inductive CertEnd (D : Deklaration) (V : Vertrag D) where
  | ret
  | retWert (e : CertExpr D) (lo hi : Int)
  | retWhy (r : Nat)
  | leave
  | next
  | cons (s : CertStmt D V) (Λm : List (Res D)) (rest : CertEnd D V)
  | bind (e : CertExpr D) (lo hi : Int) (rest : CertEnd D V)
end
/-! ## Rank order as a Boolean

    `Stmt.locks` needs `∀ M, Res.held M ∈ Λ → D.rang M < D.rang L`, which
    quantifies over the arbitrary `D.Lock`. Only the locks named in `Λ`
    can fire the premise, so the table folds over the finite list instead. -/

/-- Rank side of `locks`, recomputed: every held entry of `Λ` is below `L`. -/
def rankOk (D : Deklaration) (L : D.Lock) (Λ : List (Res D)) : Bool :=
  Λ.all fun r => match r with
    | .held M => decide (D.rang M < D.rang L)
    | .marke _ _ => true

/-- What `rankOk` promises: a `true` fold discharges the `locks` premise. -/
theorem rankOk_true {D : Deklaration} {L : D.Lock} {Λ : List (Res D)}
    (h : rankOk D L Λ = true) :
    ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L := by
  intro M hm
  have hall : ∀ r ∈ Λ, (match r with
      | .held M => decide (D.rang M < D.rang L)
      | .marke _ _ => true) = true := List.all_eq_true.mp h
  have hr := hall (Res.held M) hm
  simp only at hr
  exact of_decide_eq_true hr

/-! ## Validity: every side condition recomputed -/

mutual
/-- Statement validity: index shape, field-type equation, guard and write
    facts, rank order, call shape, result shape, linear balance. -/
def certStmtGueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : CertStmt D V → Prop
  | .assignSlot t f i e =>
    certRange D Γ Λ i = some (0, D.count t - 1) ∧
      certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.typ t f) ∧
      V.schreibt t = true ∧ darf D t Λ ∧ Λ = Λ'
  | .assignVar k lo hi e =>
    ctxTyp Γ k = some (lo, hi) ∧ certRange D Γ Λ e = some (lo, hi) ∧
      Λ = Λ'
  | .assignGlob g e =>
    certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.gtyp g) ∧
      V.gschreibt g = true ∧ gdarf D g Λ ∧ Λ = Λ'
  | .putBytes t f n lo hi i e =>
    D.typ t f = .int 0 255 ∧ certRange D Γ Λ i = some (lo, hi) ∧
      0 ≤ lo ∧ hi + (n : Int) ≤ D.count t ∧
      certRange D Γ Λ e = some (0, 256 ^ n - 1) ∧
      V.schreibt t = true ∧ darf D t Λ ∧ Λ = Λ'
  | .call f Λc _ =>
    Λ = Λc ∧ D.params f = [] ∧ D.gruende f = 0 ∧ nach D f Λ = Λ'
  | .ite c t e =>
    certCondGueltig D Γ Λ c ∧ certSeqGueltig D V l Γ Λ Λ' t ∧
      certSeqGueltig D V l Γ Λ Λ' e ∧ Λ = Λ'
  | .onOption e n p a =>
    certRange D Γ Λ e = some (0, n - 1) ∧
      certSeqGueltig D V l (.index n :: Γ) Λ Λ' p ∧
      certSeqGueltig D V l Γ Λ Λ' a ∧ Λ = Λ'
  | .locks L body =>
    rankOk D L Λ = true ∧
      certSeqGueltig D V l Γ (Res.held L :: Λ) (Res.held L :: Λ) body ∧
      Λ = Λ'
  | .breaking i body => certSeqGueltig D V l Γ Λ Λ' body
  | .shift t f lo hi von nach i =>
    intVonTyp (D.typ t f) = some (lo, hi) ∧
      certRange D Γ Λ i = some (0, D.count t - 1) ∧
      lo ≤ nach ∧ nach ≤ hi ∧ D.erlaubt t f von nach = true ∧
      V.schreibt t = true ∧ darf D t Λ ∧ Λ = Λ'
  | .publish g e payload =>
    payload = D.nutzlast g ∧ certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.gtyp g) ∧
      V.gschreibt g = true ∧ gdarf D g Λ ∧ Λ = Λ'
  | .regWrite r e =>
    (D.rklasse r).schreibbar = true ∧ certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.rtyp r) ∧ Λ = Λ'
  | .advances m a =>
    Res.marke m a ∈ Λ ∧ a + 1 < D.stufen m ∧
      (Λ.erase (Res.marke m a)) ++ [Res.marke m (a + 1)] = Λ'
  | .retires m s a =>
    Res.marke m s ∈ Λ ∧ Λ.erase (Res.marke m s) = Λ'
  | .traverse t inv body =>
    certCondGueltig D Γ Λ inv ∧
      certSeqGueltig D V true (.index (D.count t) :: Γ) Λ Λ body ∧
      Λ = Λ'
  | .retry n bis body ueber =>
    certCondGueltig D Γ Λ bis ∧ certSeqGueltig D V true Γ Λ Λ body ∧
      certSeqGueltig D V l Γ Λ Λ ueber ∧ Λ = Λ'
  | .forever a inv body =>
    certCondGueltig D Γ Λ inv ∧ certSeqGueltig D V true Γ Λ Λ body ∧
      Λ = Λ'
  | .ret => V.erg = none ∧ Λ.Perm V.ende ∧ Λ = Λ'
  | .retWert e lo hi =>
    V.erg = some (.int lo hi) ∧ certRange D Γ Λ e = some (lo, hi) ∧
      Λ.Perm V.ende ∧ Λ = Λ'
  | .retWhy r => r < V.gruende ∧ Λ.Perm V.ende ∧ Λ = Λ'
  | .leave => l = true ∧ Λ = Λ'
  | .next => l = true ∧ Λ = Λ'

/-- Block validity: `nil` closes the balance by equation, `cons` threads
    through the carried middle, `bind` extends by the recomputed range. -/
def certSeqGueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) : CertSeq D V → Prop
  | .nil => Λ = Λ'
  | .cons s Λm rest =>
    certStmtGueltig D V l Γ Λ Λm s ∧ certSeqGueltig D V l Γ Λm Λ' rest
  | .bind e lo hi rest =>
    certRange D Γ Λ e = some (lo, hi) ∧
      certSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest
  | .bindCall f lo hi Λc _ rest =>
    D.params f = [] ∧ D.gruende f = 0 ∧ D.erg f = some (.int lo hi) ∧
      Λ = Λc ∧
      certSeqGueltig D V l (.int lo hi :: Γ) (nach D f Λ) Λ' rest
  | .bindCallElse f lo hi Λc _ err rest =>
    D.params f = [] ∧ 0 < D.gruende f ∧ D.erg f = some (.int lo hi) ∧
      Λ = Λc ∧
      certEndGueltig D V l (.why (D.gruende f) :: Γ) (nach D f Λ) err ∧
      certSeqGueltig D V l (.int lo hi :: Γ) (nach D f Λ) Λ' rest
  | .regRead r lo hi rest =>
    (D.rklasse r).lesbar = true ∧ intVonTyp (D.rtyp r) = some (lo, hi) ∧
      certSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest
  | .regReadElse r zusage sonst rest =>
    (D.rklasse r).lesbar = true ∧
      certCondGueltig D (D.rtyp r :: Γ) Λ zusage ∧
      certEndGueltig D V l Γ Λ sonst ∧
      certSeqGueltig D V l (D.rtyp r :: Γ) Λ Λ' rest
  | .awaits g payload lo hi rest =>
    payload = D.nutzlast g ∧ gdarf D g Λ ∧ D.atomar g = true ∧
      intVonTyp (D.gtyp g) = some (lo, hi) ∧
      certSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest
  | .exchange g lo hi neu rest =>
    intVonTyp (D.gtyp g) = some (lo, hi) ∧
      certRange D (.int lo hi :: Γ) Λ neu = some (lo, hi) ∧
      V.gschreibt g = true ∧ gdarf D g Λ ∧
      certSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest
  | .narrow e lo hi lo' hi' sonst rest =>
    certRange D Γ Λ e = some (lo, hi) ∧
      certEndGueltig D V l Γ Λ sonst ∧
      certSeqGueltig D V l (.int lo' hi' :: Γ) Λ Λ' rest
  | .check c sonst rest =>
    certCondGueltig D Γ Λ c ∧ certEndGueltig D V l Γ Λ sonst ∧
      certSeqGueltig D V l Γ Λ Λ' rest

/-- Non-falling-block validity: terminal closings plus the same
    threading as blocks (the middle, never an output: `Endblock` ends). -/
def certEndGueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) : CertEnd D V → Prop
  | .ret => V.erg = none ∧ Λ.Perm V.ende
  | .retWert e lo hi =>
    V.erg = some (.int lo hi) ∧ certRange D Γ Λ e = some (lo, hi) ∧
      Λ.Perm V.ende
  | .retWhy r => r < V.gruende ∧ Λ.Perm V.ende
  | .leave => l = true
  | .next => l = true
  | .cons s Λm rest =>
    certStmtGueltig D V l Γ Λ Λm s ∧ certEndGueltig D V l Γ Λm rest
  | .bind e lo hi rest =>
    certRange D Γ Λ e = some (lo, hi) ∧
      certEndGueltig D V l (.int lo hi :: Γ) Λ rest
end
/-! ## Validity as `Decidable`, by structural recursion -/


end Gabbro.Grammatik
