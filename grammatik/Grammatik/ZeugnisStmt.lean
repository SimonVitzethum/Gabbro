/-
  File:     Grammatik/ZeugnisStmt.lean
  Subject:  Certificate soundness for STATEMENTS (T1 of PLAN-UEBERSETZUNGSVALIDIERUNG.md).

  Extends `Zeugnis.lean` (expressions) to statements: `CertCond`/`CertStmt`/
  `CertSeq`/`CertEnd` are plain-data certificates, the `*Gueltig` predicates
  recompute every side condition (`darf`, `V.schreibt`, rank order, index
  shapes, linear balance), and `zeugnisStmt_sound` elaborates a valid
  certificate to a well-typed `Endblock` (the run statement).
  The Rust printer (`certemit.rs`) covers expressions only; the statement
  print format is designed in the docstrings below for the transfer phase.
-/
import Grammatik.Zeugnis
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

/-- Boolean conditions as plain data: the `ite`/`retry`/`forever`/`pruefung`
    scrutinees over the int fragment (`CertExpr`) plus variable reads. -/
inductive CertCond (D : Deklaration) where
  | wahr
  | falsch
  | var (k : Nat)
  | lt (a b : CertExpr D)
  | le (a b : CertExpr D)
  | eq (a b : CertExpr D)
  | und (a b : CertCond D)
  | oder (a b : CertCond D)
  | nicht (a : CertCond D)

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
  | .wahr => True
  | .falsch => True
  | .var k => ctxBoolTyp Γ k ≠ none
  | .lt a b => certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none
  | .le a b => certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none
  | .eq a b => certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none
  | .und a b => certCondGueltig D Γ Λ a ∧ certCondGueltig D Γ Λ b
  | .oder a b => certCondGueltig D Γ Λ a ∧ certCondGueltig D Γ Λ b
  | .nicht a => certCondGueltig D Γ Λ a

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
        exact ⟨.hier, trivial⟩
      | int => simp [ctxBoolTyp] at h
      | opt => simp [ctxBoolTyp] at h
      | sum => simp [ctxBoolTyp] at h
      | grund => simp [ctxBoolTyp] at h
      | never => simp [ctxBoolTyp] at h
      | fl => simp [ctxBoolTyp] at h
      | fnptr => simp [ctxBoolTyp] at h
      | ptr => simp [ctxBoolTyp] at h
    | succ k =>
      simp [ctxBoolTyp] at h
      obtain ⟨x, _⟩ := ih k h
      exact ⟨.dort x, trivial⟩

/-- Condition validity as `Decidable`, by structural recursion. -/
def decCondGueltig (D : Deklaration) (Γ : Ctx) (Λ : List (Res D))
    (c : CertCond D) : Decidable (certCondGueltig D Γ Λ c) :=
  match c with
  | .wahr => inferInstanceAs (Decidable True)
  | .falsch => inferInstanceAs (Decidable True)
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
  | .und a b =>
    haveI := decCondGueltig D Γ Λ a
    haveI := decCondGueltig D Γ Λ b
    inferInstanceAs
      (Decidable (certCondGueltig D Γ Λ a ∧ certCondGueltig D Γ Λ b))
  | .oder a b =>
    haveI := decCondGueltig D Γ Λ a
    haveI := decCondGueltig D Γ Λ b
    inferInstanceAs
      (Decidable (certCondGueltig D Γ Λ a ∧ certCondGueltig D Γ Λ b))
  | .nicht a =>
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
  | wahr => exact ⟨Expr.wahr, trivial⟩
  | falsch => exact ⟨Expr.falsch, trivial⟩
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
  | und a b iha ihb =>
    simp only [certCondGueltig] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨ea, _⟩ := iha ha
    obtain ⟨eb, _⟩ := ihb hb
    exact ⟨Expr.und ea eb, trivial⟩
  | oder a b iha ihb =>
    simp only [certCondGueltig] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨ea, _⟩ := iha ha
    obtain ⟨eb, _⟩ := ihb hb
    exact ⟨Expr.oder ea eb, trivial⟩
  | nicht a ih =>
    simp only [certCondGueltig] at h
    obtain ⟨ea, _⟩ := ih h
    exact ⟨Expr.nicht ea, trivial⟩

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
  | schreibBytes (t : D.Tab) (f : D.Feld t) (n : Nat) (lo hi : Int)
      (i e : CertExpr D)
  | call (f : D.Fn) (Λc : List (Res D)) (hp : RufPasst D V (D.signatur f) Λc)
  | ite (c : CertCond D) (t e : CertSeq D V)
  | onOption (e : CertExpr D) (n : Int) (p a : CertSeq D V)
  | locks (L : D.Lock) (body : CertSeq D V)
  | breaking (i : D.Inv) (body : CertSeq D V)
  | uebergang (t : D.Tab) (f : D.Feld t) (lo hi von nach : Int)
      (i : CertExpr D)
  | publish (g : D.Glob) (e : CertExpr D) (payload : List D.Glob)
  | regSchreib (r : D.Reg) (e : CertExpr D)
  | advances (m : D.Marke) (a : Nat)
  | retires (m : D.Marke) (s : Nat) (a : D.Annahme)
  | traverse (t : D.Tab) (inv : CertCond D) (body : CertSeq D V)
  | retry (n : Nat) (bis : CertCond D) (body ueber : CertSeq D V)
  | forever (a : D.Annahme) (inv : CertCond D) (body : CertSeq D V)
  | ret
  | retWert (e : CertExpr D) (lo hi : Int)
  | retGrund (r : Nat)
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
  | regLies (r : D.Reg) (lo hi : Int) (rest : CertSeq D V)
  | regLiesElse (r : D.Reg) (zusage : CertCond D) (sonst : CertEnd D V)
      (rest : CertSeq D V)
  | awaits (g : D.Glob) (payload : List D.Glob) (lo hi : Int)
      (rest : CertSeq D V)
  | exchange (g : D.Glob) (lo hi : Int) (neu : CertExpr D)
      (rest : CertSeq D V)
  | narrow (e : CertExpr D) (lo hi lo' hi' : Int) (sonst : CertEnd D V)
      (rest : CertSeq D V)
  | pruefung (c : CertCond D) (sonst : CertEnd D V) (rest : CertSeq D V)

/-- One non-falling block as plain data (the body a program carries). -/
inductive CertEnd (D : Deklaration) (V : Vertrag D) where
  | ret
  | retWert (e : CertExpr D) (lo hi : Int)
  | retGrund (r : Nat)
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
  | .schreibBytes t f n lo hi i e =>
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
  | .uebergang t f lo hi von nach i =>
    intVonTyp (D.typ t f) = some (lo, hi) ∧
      certRange D Γ Λ i = some (0, D.count t - 1) ∧
      lo ≤ nach ∧ nach ≤ hi ∧ D.erlaubt t f von nach = true ∧
      V.schreibt t = true ∧ darf D t Λ ∧ Λ = Λ'
  | .publish g e payload =>
    payload = D.nutzlast g ∧ certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.gtyp g) ∧
      V.gschreibt g = true ∧ gdarf D g Λ ∧ Λ = Λ'
  | .regSchreib r e =>
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
  | .retGrund r => r < V.gruende ∧ Λ.Perm V.ende ∧ Λ = Λ'
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
      certEndGueltig D V l (.grund (D.gruende f) :: Γ) (nach D f Λ) err ∧
      certSeqGueltig D V l (.int lo hi :: Γ) (nach D f Λ) Λ' rest
  | .regLies r lo hi rest =>
    (D.rklasse r).lesbar = true ∧ intVonTyp (D.rtyp r) = some (lo, hi) ∧
      certSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest
  | .regLiesElse r zusage sonst rest =>
    (D.rklasse r).lesbar = true ∧
      certCondGueltig D (D.rtyp r :: Γ) Λ zusage ∧
      certEndGueltig D V l Γ Λ sonst ∧
      certSeqGueltig D V l (D.rtyp r :: Γ) Λ Λ' rest
  | .awaits g payload lo hi rest =>
    payload = D.nutzlast g ∧ gdarf D g Λ ∧
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
  | .pruefung c sonst rest =>
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
  | .retGrund r => r < V.gruende ∧ Λ.Perm V.ende
  | .leave => l = true
  | .next => l = true
  | .cons s Λm rest =>
    certStmtGueltig D V l Γ Λ Λm s ∧ certEndGueltig D V l Γ Λm rest
  | .bind e lo hi rest =>
    certRange D Γ Λ e = some (lo, hi) ∧
      certEndGueltig D V l (.int lo hi :: Γ) Λ rest
end

/-! ## Validity as `Decidable`, by structural recursion -/

mutual
def decStmtGueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (s : CertStmt D V) :
    Decidable (certStmtGueltig D V l Γ Λ Λ' s) :=
  match s with
  | .assignSlot t f i e =>
    inferInstanceAs (Decidable (certRange D Γ Λ i = some (0, D.count t - 1) ∧
      certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.typ t f) ∧
      V.schreibt t = true ∧ darf D t Λ ∧ Λ = Λ'))
  | .assignVar k lo hi e =>
    inferInstanceAs (Decidable (ctxTyp Γ k = some (lo, hi) ∧
      certRange D Γ Λ e = some (lo, hi) ∧ Λ = Λ'))
  | .assignGlob g e =>
    inferInstanceAs (Decidable (certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.gtyp g) ∧
      V.gschreibt g = true ∧ gdarf D g Λ ∧ Λ = Λ'))
  | .schreibBytes t f n lo hi i e =>
    inferInstanceAs (Decidable (D.typ t f = .int 0 255 ∧
      certRange D Γ Λ i = some (lo, hi) ∧ 0 ≤ lo ∧
      hi + (n : Int) ≤ D.count t ∧
      certRange D Γ Λ e = some (0, 256 ^ n - 1) ∧
      V.schreibt t = true ∧ darf D t Λ ∧ Λ = Λ'))
  | .call f Λc _ =>
    inferInstanceAs (Decidable (Λ = Λc ∧ D.params f = [] ∧
      D.gruende f = 0 ∧ nach D f Λ = Λ'))
  | .ite c t e =>
    haveI := decCondGueltig D Γ Λ c
    haveI := decSeqGueltig D V l Γ Λ Λ' t
    haveI := decSeqGueltig D V l Γ Λ Λ' e
    inferInstanceAs (Decidable (certCondGueltig D Γ Λ c ∧
      certSeqGueltig D V l Γ Λ Λ' t ∧ certSeqGueltig D V l Γ Λ Λ' e ∧
      Λ = Λ'))
  | .onOption e n p a =>
    haveI := decSeqGueltig D V l (.index n :: Γ) Λ Λ' p
    haveI := decSeqGueltig D V l Γ Λ Λ' a
    inferInstanceAs (Decidable (certRange D Γ Λ e = some (0, n - 1) ∧
      certSeqGueltig D V l (.index n :: Γ) Λ Λ' p ∧
      certSeqGueltig D V l Γ Λ Λ' a ∧ Λ = Λ'))
  | .locks L body =>
    haveI := decSeqGueltig D V l Γ (Res.held L :: Λ) (Res.held L :: Λ) body
    inferInstanceAs (Decidable (rankOk D L Λ = true ∧
      certSeqGueltig D V l Γ (Res.held L :: Λ) (Res.held L :: Λ) body ∧
      Λ = Λ'))
  | .breaking i body =>
    haveI := decSeqGueltig D V l Γ Λ Λ' body
    inferInstanceAs
      (Decidable (certSeqGueltig D V l Γ Λ Λ' body))
  | .uebergang t f lo hi von nach i =>
    inferInstanceAs (Decidable (intVonTyp (D.typ t f) = some (lo, hi) ∧
      certRange D Γ Λ i = some (0, D.count t - 1) ∧
      lo ≤ nach ∧ nach ≤ hi ∧ D.erlaubt t f von nach = true ∧
      V.schreibt t = true ∧ darf D t Λ ∧ Λ = Λ'))
  | .publish g e payload =>
    inferInstanceAs (Decidable (payload = D.nutzlast g ∧
      certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.gtyp g) ∧
      V.gschreibt g = true ∧ gdarf D g Λ ∧ Λ = Λ'))
  | .regSchreib r e =>
    inferInstanceAs (Decidable ((D.rklasse r).schreibbar = true ∧
      certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.rtyp r) ∧ Λ = Λ'))
  | .advances m a =>
    inferInstanceAs (Decidable (Res.marke m a ∈ Λ ∧ a + 1 < D.stufen m ∧
      (Λ.erase (Res.marke m a)) ++ [Res.marke m (a + 1)] = Λ'))
  | .retires m s a =>
    inferInstanceAs (Decidable (Res.marke m s ∈ Λ ∧
      Λ.erase (Res.marke m s) = Λ'))
  | .traverse t inv body =>
    haveI := decCondGueltig D Γ Λ inv
    haveI := decSeqGueltig D V true (.index (D.count t) :: Γ) Λ Λ body
    inferInstanceAs (Decidable (certCondGueltig D Γ Λ inv ∧
      certSeqGueltig D V true (.index (D.count t) :: Γ) Λ Λ body ∧
      Λ = Λ'))
  | .retry n bis body ueber =>
    haveI := decCondGueltig D Γ Λ bis
    haveI := decSeqGueltig D V true Γ Λ Λ body
    haveI := decSeqGueltig D V l Γ Λ Λ ueber
    inferInstanceAs (Decidable (certCondGueltig D Γ Λ bis ∧
      certSeqGueltig D V true Γ Λ Λ body ∧
      certSeqGueltig D V l Γ Λ Λ ueber ∧ Λ = Λ'))
  | .forever a inv body =>
    haveI := decCondGueltig D Γ Λ inv
    haveI := decSeqGueltig D V true Γ Λ Λ body
    inferInstanceAs (Decidable (certCondGueltig D Γ Λ inv ∧
      certSeqGueltig D V true Γ Λ Λ body ∧ Λ = Λ'))
  | .ret =>
    inferInstanceAs (Decidable (V.erg = none ∧ Λ.Perm V.ende ∧ Λ = Λ'))
  | .retWert e lo hi =>
    inferInstanceAs (Decidable (V.erg = some (.int lo hi) ∧
      certRange D Γ Λ e = some (lo, hi) ∧ Λ.Perm V.ende ∧ Λ = Λ'))
  | .retGrund r =>
    inferInstanceAs (Decidable (r < V.gruende ∧ Λ.Perm V.ende ∧ Λ = Λ'))
  | .leave => inferInstanceAs (Decidable (l = true ∧ Λ = Λ'))
  | .next => inferInstanceAs (Decidable (l = true ∧ Λ = Λ'))

def decSeqGueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (q : CertSeq D V) :
    Decidable (certSeqGueltig D V l Γ Λ Λ' q) :=
  match q with
  | .nil => inferInstanceAs (Decidable (Λ = Λ'))
  | .cons s Λm rest =>
    haveI := decStmtGueltig D V l Γ Λ Λm s
    haveI := decSeqGueltig D V l Γ Λm Λ' rest
    inferInstanceAs (Decidable (certStmtGueltig D V l Γ Λ Λm s ∧
      certSeqGueltig D V l Γ Λm Λ' rest))
  | .bind e lo hi rest =>
    haveI := decSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable (certRange D Γ Λ e = some (lo, hi) ∧
      certSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest))
  | .bindCall f lo hi Λc _ rest =>
    haveI := decSeqGueltig D V l (.int lo hi :: Γ) (nach D f Λ) Λ' rest
    inferInstanceAs (Decidable (D.params f = [] ∧ D.gruende f = 0 ∧
      D.erg f = some (.int lo hi) ∧ Λ = Λc ∧
      certSeqGueltig D V l (.int lo hi :: Γ) (nach D f Λ) Λ' rest))
  | .bindCallElse f lo hi Λc _ err rest =>
    haveI := decEndGueltig D V l (.grund (D.gruende f) :: Γ) (nach D f Λ) err
    haveI := decSeqGueltig D V l (.int lo hi :: Γ) (nach D f Λ) Λ' rest
    inferInstanceAs (Decidable (D.params f = [] ∧ 0 < D.gruende f ∧
      D.erg f = some (.int lo hi) ∧ Λ = Λc ∧
      certEndGueltig D V l (.grund (D.gruende f) :: Γ) (nach D f Λ) err ∧
      certSeqGueltig D V l (.int lo hi :: Γ) (nach D f Λ) Λ' rest))
  | .regLies r lo hi rest =>
    haveI := decSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable ((D.rklasse r).lesbar = true ∧
      intVonTyp (D.rtyp r) = some (lo, hi) ∧
      certSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest))
  | .regLiesElse r zusage sonst rest =>
    haveI := decCondGueltig D (D.rtyp r :: Γ) Λ zusage
    haveI := decEndGueltig D V l Γ Λ sonst
    haveI := decSeqGueltig D V l (D.rtyp r :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable ((D.rklasse r).lesbar = true ∧
      certCondGueltig D (D.rtyp r :: Γ) Λ zusage ∧
      certEndGueltig D V l Γ Λ sonst ∧
      certSeqGueltig D V l (D.rtyp r :: Γ) Λ Λ' rest))
  | .awaits g payload lo hi rest =>
    haveI := decSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable (payload = D.nutzlast g ∧ gdarf D g Λ ∧
      intVonTyp (D.gtyp g) = some (lo, hi) ∧
      certSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest))
  | .exchange g lo hi neu rest =>
    haveI := decSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable (intVonTyp (D.gtyp g) = some (lo, hi) ∧
      certRange D (.int lo hi :: Γ) Λ neu = some (lo, hi) ∧
      V.gschreibt g = true ∧ gdarf D g Λ ∧
      certSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest))
  | .narrow e lo hi lo' hi' sonst rest =>
    haveI := decEndGueltig D V l Γ Λ sonst
    haveI := decSeqGueltig D V l (.int lo' hi' :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable (certRange D Γ Λ e = some (lo, hi) ∧
      certEndGueltig D V l Γ Λ sonst ∧
      certSeqGueltig D V l (.int lo' hi' :: Γ) Λ Λ' rest))
  | .pruefung c sonst rest =>
    haveI := decCondGueltig D Γ Λ c
    haveI := decEndGueltig D V l Γ Λ sonst
    haveI := decSeqGueltig D V l Γ Λ Λ' rest
    inferInstanceAs (Decidable (certCondGueltig D Γ Λ c ∧
      certEndGueltig D V l Γ Λ sonst ∧
      certSeqGueltig D V l Γ Λ Λ' rest))

def decEndGueltig (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (e : CertEnd D V) :
    Decidable (certEndGueltig D V l Γ Λ e) :=
  match e with
  | .ret => inferInstanceAs (Decidable (V.erg = none ∧ Λ.Perm V.ende))
  | .retWert e lo hi =>
    inferInstanceAs (Decidable (V.erg = some (.int lo hi) ∧
      certRange D Γ Λ e = some (lo, hi) ∧ Λ.Perm V.ende))
  | .retGrund r =>
    inferInstanceAs (Decidable (r < V.gruende ∧ Λ.Perm V.ende))
  | .leave => inferInstanceAs (Decidable (l = true))
  | .next => inferInstanceAs (Decidable (l = true))
  | .cons s Λm rest =>
    haveI := decStmtGueltig D V l Γ Λ Λm s
    haveI := decEndGueltig D V l Γ Λm rest
    inferInstanceAs (Decidable (certStmtGueltig D V l Γ Λ Λm s ∧
      certEndGueltig D V l Γ Λm rest))
  | .bind e lo hi rest =>
    haveI := decEndGueltig D V l (.int lo hi :: Γ) Λ rest
    inferInstanceAs (Decidable (certRange D Γ Λ e = some (lo, hi) ∧
      certEndGueltig D V l (.int lo hi :: Γ) Λ rest))
end

instance instDecStmt (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (s : CertStmt D V) :
    Decidable (certStmtGueltig D V l Γ Λ Λ' s) :=
  decStmtGueltig D V l Γ Λ Λ' s

instance instDecSeq (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (q : CertSeq D V) :
    Decidable (certSeqGueltig D V l Γ Λ Λ' q) :=
  decSeqGueltig D V l Γ Λ Λ' q

instance instDecEnd (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (e : CertEnd D V) :
    Decidable (certEndGueltig D V l Γ Λ e) :=
  decEndGueltig D V l Γ Λ e

/-! ## Soundness: a valid certificate elaborates to the judgement -/

mutual
/-- Statement soundness: a valid `CertStmt` denotes a well-typed `Stmt`.
    Every recomputed fact feeds its constructor; the carried `RufPasst`
    feeds the call. -/
theorem stmt_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (s : CertStmt D V)
    (h : certStmtGueltig D V l Γ Λ Λ' s) :
    ∃ _ : Stmt D V l Γ Λ Λ', True := by
  revert h
  match s with
  | .assignSlot t f i e =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hi, hne, htyp, hw, hL, hout⟩ := h
    subst hout
    obtain ⟨ei, _⟩ := zeugnis_sound i 0 (D.count t - 1) hi
    cases he : certRange D Γ Λ e with
    | none => exact absurd he hne
    | some p =>
      obtain ⟨lo, hi'⟩ := p
      have hft : intVonTyp (D.typ t f) = some (lo, hi') := by
        rw [← he]
        exact htyp.symm
      have hτ : D.typ t f = .int lo hi' := intVonTyp_eq hft
      obtain ⟨ee, _⟩ := zeugnis_sound e lo hi' he
      have ee' : Expr D Γ Λ (D.typ t f) := by rw [hτ]; exact ee
      exact ⟨Stmt.assignSlot t f ei ee' hw hL, trivial⟩
  | .assignVar k lo hi e =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hctx, hrng, hout⟩ := h
    subst hout
    obtain ⟨x, _⟩ := ctxTyp_var Γ k lo hi hctx
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi hrng
    exact ⟨Stmt.assignVar x ee, trivial⟩
  | .assignGlob g e =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hne, htyp, hw, hL, hout⟩ := h
    subst hout
    cases he : certRange D Γ Λ e with
    | none => exact absurd he hne
    | some p =>
      obtain ⟨lo, hi⟩ := p
      have hgt : intVonTyp (D.gtyp g) = some (lo, hi) := by
        rw [← he]
        exact htyp.symm
      have hτ : D.gtyp g = .int lo hi := intVonTyp_eq hgt
      obtain ⟨ee, _⟩ := zeugnis_sound e lo hi he
      have ee' : Expr D Γ Λ (D.gtyp g) := by rw [hτ]; exact ee
      exact ⟨Stmt.assignGlob g ee' hw hL, trivial⟩
  | .schreibBytes t f n lo hi i e =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hft, hii, hlo, hhi, hee, hw, hL, hout⟩ := h
    subst hout
    obtain ⟨ei, _⟩ := zeugnis_sound i lo hi hii
    obtain ⟨ee, _⟩ := zeugnis_sound e 0 (256 ^ n - 1) hee
    exact ⟨Stmt.schreibBytes t f hft n ei hlo hhi ee hw hL, trivial⟩
  | .call f Λc hp =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hΛc, hpar, hgr, hnach⟩ := h
    subst hΛc
    subst hnach
    exact ⟨Stmt.call f (by rw [hpar]; exact Args.nil) hp hgr, trivial⟩
  | .ite c t e =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hc, ht, he, hout⟩ := h
    subst hout
    obtain ⟨ec, _⟩ := cond_sound c hc
    obtain ⟨bt, _⟩ := seq_sound D V l Γ Λ Λ t ht
    obtain ⟨be, _⟩ := seq_sound D V l Γ Λ Λ e he
    exact ⟨Stmt.ite ec bt be, trivial⟩
  | .onOption e n p a =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨he, hp, ha, hout⟩ := h
    subst hout
    obtain ⟨ee, _⟩ := zeugnis_sound e 0 (n - 1) he
    obtain ⟨bp, _⟩ := seq_sound D V l (.index n :: Γ) Λ Λ p hp
    obtain ⟨ba, _⟩ := seq_sound D V l Γ Λ Λ a ha
    exact ⟨Stmt.onOption (Expr.some ee) bp ba, trivial⟩
  | .locks L body =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hrank, hbody, hout⟩ := h
    subst hout
    have hr := rankOk_true hrank
    obtain ⟨bb, _⟩ :=
      seq_sound D V l Γ (Res.held L :: Λ) (Res.held L :: Λ) body hbody
    exact ⟨Stmt.locks L hr bb, trivial⟩
  | .breaking i body =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨bb, _⟩ := seq_sound D V l Γ Λ Λ' body h
    exact ⟨Stmt.breaking i bb, trivial⟩
  | .uebergang t f lo hi von nach i =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hft, hii, hlo, hhi, he, hw, hL, hout⟩ := h
    subst hout
    have hτ : D.typ t f = .int lo hi := intVonTyp_eq hft
    obtain ⟨ei, _⟩ := zeugnis_sound i 0 (D.count t - 1) hii
    exact ⟨Stmt.uebergang t f hτ ei von nach ⟨hlo, hhi⟩ he hw hL, trivial⟩
  | .publish g e payload =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hp, hne, htyp, hw, hL, hout⟩ := h
    subst hout
    cases he : certRange D Γ Λ e with
    | none => exact absurd he hne
    | some p =>
      obtain ⟨lo, hi⟩ := p
      have hgt : intVonTyp (D.gtyp g) = some (lo, hi) := by
        rw [← he]
        exact htyp.symm
      have hτ : D.gtyp g = .int lo hi := intVonTyp_eq hgt
      obtain ⟨ee, _⟩ := zeugnis_sound e lo hi he
      have ee' : Expr D Γ Λ (D.gtyp g) := by rw [hτ]; exact ee
      exact ⟨Stmt.publish g ee' payload hp hw hL, trivial⟩
  | .regSchreib r e =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hk, hne, htyp, hout⟩ := h
    subst hout
    cases he : certRange D Γ Λ e with
    | none => exact absurd he hne
    | some p =>
      obtain ⟨lo, hi⟩ := p
      have hrt : intVonTyp (D.rtyp r) = some (lo, hi) := by
        rw [← he]
        exact htyp.symm
      have hτ : D.rtyp r = .int lo hi := intVonTyp_eq hrt
      obtain ⟨ee, _⟩ := zeugnis_sound e lo hi he
      have ee' : Expr D Γ Λ (D.rtyp r) := by rw [hτ]; exact ee
      exact ⟨Stmt.regSchreib r hk ee', trivial⟩
  | .advances m a =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hmem, hs, hout⟩ := h
    subst hout
    exact ⟨Stmt.advances m a hmem hs, trivial⟩
  | .retires m s a =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hmem, hout⟩ := h
    subst hout
    exact ⟨Stmt.retires m s hmem a, trivial⟩
  | .traverse t inv body =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hinv, hbody, hout⟩ := h
    subst hout
    obtain ⟨einv, _⟩ := cond_sound inv hinv
    obtain ⟨bb, _⟩ :=
      seq_sound D V true (.index (D.count t) :: Γ) Λ Λ body hbody
    exact ⟨Stmt.traverse t einv bb, trivial⟩
  | .retry n bis body ueber =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hbis, hbody, hueber, hout⟩ := h
    subst hout
    obtain ⟨ebis, _⟩ := cond_sound bis hbis
    obtain ⟨bb, _⟩ := seq_sound D V true Γ Λ Λ body hbody
    obtain ⟨bu, _⟩ := seq_sound D V l Γ Λ Λ ueber hueber
    exact ⟨Stmt.retry n ebis bb bu, trivial⟩
  | .forever a inv body =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hinv, hbody, hout⟩ := h
    subst hout
    obtain ⟨einv, _⟩ := cond_sound inv hinv
    obtain ⟨bb, _⟩ := seq_sound D V true Γ Λ Λ body hbody
    exact ⟨Stmt.forever a einv bb, trivial⟩
  | .ret =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨he, hΛ, hout⟩ := h
    subst hout
    exact ⟨Stmt.ret (by rw [he]; exact ErgExpr.keine) hΛ, trivial⟩
  | .retWert e lo hi =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨he, hrng, hΛ, hout⟩ := h
    subst hout
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi hrng
    exact ⟨Stmt.ret (by rw [he]; exact ErgExpr.wert ee) hΛ, trivial⟩
  | .retGrund r =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hlt, hΛ, hout⟩ := h
    subst hout
    exact ⟨Stmt.retGrund ⟨r, hlt⟩ hΛ, trivial⟩
  | .leave =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hl, hout⟩ := h
    subst hout
    exact ⟨Stmt.leave hl, trivial⟩
  | .next =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hl, hout⟩ := h
    subst hout
    exact ⟨Stmt.next hl, trivial⟩

/-- Block soundness: threading through the carried middle, context
    extension by the recomputed range. -/
theorem seq_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ Λ' : List (Res D)) (q : CertSeq D V)
    (h : certSeqGueltig D V l Γ Λ Λ' q) :
    ∃ _ : Block D V l Γ Λ Λ', True := by
  revert h
  match q with
  | .nil =>
    intro h
    simp only [certSeqGueltig] at h
    subst h
    exact ⟨Block.nil, trivial⟩
  | .cons s Λm rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨hs, hrest⟩ := h
    obtain ⟨s', _⟩ := stmt_sound D V l Γ Λ Λm s hs
    obtain ⟨r', _⟩ := seq_sound D V l Γ Λm Λ' rest hrest
    exact ⟨Block.cons s' r', trivial⟩
  | .bind e lo hi rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨he, hrest⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi he
    obtain ⟨r', _⟩ := seq_sound D V l (.int lo hi :: Γ) Λ Λ' rest hrest
    exact ⟨Block.bind ee r', trivial⟩
  | .bindCall f lo hi Λc hp rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨hpar, hgr, he, hΛc, hrest⟩ := h
    subst hΛc
    obtain ⟨r', _⟩ :=
      seq_sound D V l (.int lo hi :: Γ) (nach D f Λ) Λ' rest hrest
    exact ⟨Block.bindCall f (by rw [hpar]; exact Args.nil) he hp hgr r',
      trivial⟩
  | .bindCallElse f lo hi Λc hp err rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨hpar, hgr, he, hΛc, herr, hrest⟩ := h
    subst hΛc
    obtain ⟨es, _⟩ :=
      end_sound D V l (.grund (D.gruende f) :: Γ) (nach D f Λ) err herr
    obtain ⟨r', _⟩ :=
      seq_sound D V l (.int lo hi :: Γ) (nach D f Λ) Λ' rest hrest
    exact ⟨Block.bindCallElse f (by rw [hpar]; exact Args.nil) he hp hgr
      es r', trivial⟩
  | .regLies r lo hi rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨hk, htyp, hrest⟩ := h
    have hτ : D.rtyp r = .int lo hi := intVonTyp_eq htyp
    obtain ⟨r', _⟩ := seq_sound D V l (.int lo hi :: Γ) Λ Λ' rest hrest
    have r'' : Block D V l (D.rtyp r :: Γ) Λ Λ' := by rw [hτ]; exact r'
    exact ⟨Block.regLies r hk r'', trivial⟩
  | .regLiesElse r zusage sonst rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨hk, hz, hsonst, hrest⟩ := h
    obtain ⟨ez, _⟩ := cond_sound zusage hz
    obtain ⟨es, _⟩ := end_sound D V l Γ Λ sonst hsonst
    obtain ⟨r', _⟩ := seq_sound D V l (D.rtyp r :: Γ) Λ Λ' rest hrest
    exact ⟨Block.regLiesElse r hk ez es r', trivial⟩
  | .awaits g payload lo hi rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨hp, hL, htyp, hrest⟩ := h
    have hτ : D.gtyp g = .int lo hi := intVonTyp_eq htyp
    obtain ⟨r', _⟩ := seq_sound D V l (.int lo hi :: Γ) Λ Λ' rest hrest
    have r'' : Block D V l (D.gtyp g :: Γ) Λ Λ' := by rw [hτ]; exact r'
    exact ⟨Block.awaits g payload hp hL r'', trivial⟩
  | .exchange g lo hi neu rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨htyp, hneu, hw, hL, hrest⟩ := h
    have hτ : D.gtyp g = .int lo hi := intVonTyp_eq htyp
    obtain ⟨eneu, _⟩ := zeugnis_sound neu lo hi hneu
    have eneu' : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g) := by
      rw [hτ]
      exact eneu
    obtain ⟨r', _⟩ := seq_sound D V l (.int lo hi :: Γ) Λ Λ' rest hrest
    have r'' : Block D V l (D.gtyp g :: Γ) Λ Λ' := by rw [hτ]; exact r'
    exact ⟨Block.exchange g eneu' hw hL r'', trivial⟩
  | .narrow e lo hi lo' hi' sonst rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨he, hsonst, hrest⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi he
    obtain ⟨es, _⟩ := end_sound D V l Γ Λ sonst hsonst
    obtain ⟨r', _⟩ :=
      seq_sound D V l (.int lo' hi' :: Γ) Λ Λ' rest hrest
    exact ⟨Block.narrow ee lo' hi' es r', trivial⟩
  | .pruefung c sonst rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨hc, hsonst, hrest⟩ := h
    obtain ⟨ec, _⟩ := cond_sound c hc
    obtain ⟨es, _⟩ := end_sound D V l Γ Λ sonst hsonst
    obtain ⟨r', _⟩ := seq_sound D V l Γ Λ Λ' rest hrest
    exact ⟨Block.pruefung ec es r', trivial⟩

/-- Non-falling-block soundness: the body a program carries. -/
theorem end_sound (D : Deklaration) (V : Vertrag D) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (e : CertEnd D V)
    (h : certEndGueltig D V l Γ Λ e) :
    ∃ _ : Endblock D V l Γ Λ, True := by
  revert h
  match e with
  | .ret =>
    intro h
    simp only [certEndGueltig] at h
    obtain ⟨he, hΛ⟩ := h
    exact ⟨Endblock.ret (by rw [he]; exact ErgExpr.keine) hΛ, trivial⟩
  | .retWert e lo hi =>
    intro h
    simp only [certEndGueltig] at h
    obtain ⟨he, hrng, hΛ⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi hrng
    exact ⟨Endblock.ret (by rw [he]; exact ErgExpr.wert ee) hΛ, trivial⟩
  | .retGrund r =>
    intro h
    simp only [certEndGueltig] at h
    obtain ⟨hlt, hΛ⟩ := h
    exact ⟨Endblock.retGrund ⟨r, hlt⟩ hΛ, trivial⟩
  | .leave =>
    intro h
    simp only [certEndGueltig] at h
    exact ⟨Endblock.leave h, trivial⟩
  | .next =>
    intro h
    simp only [certEndGueltig] at h
    exact ⟨Endblock.next h, trivial⟩
  | .cons s Λm rest =>
    intro h
    simp only [certEndGueltig] at h
    obtain ⟨hs, hrest⟩ := h
    obtain ⟨s', _⟩ := stmt_sound D V l Γ Λ Λm s hs
    obtain ⟨r', _⟩ := end_sound D V l Γ Λm rest hrest
    exact ⟨Endblock.cons s' r', trivial⟩
  | .bind e lo hi rest =>
    intro h
    simp only [certEndGueltig] at h
    obtain ⟨he, hrest⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi he
    obtain ⟨r', _⟩ := end_sound D V l (.int lo hi :: Γ) Λ rest hrest
    exact ⟨Endblock.bind ee r', trivial⟩
end

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
