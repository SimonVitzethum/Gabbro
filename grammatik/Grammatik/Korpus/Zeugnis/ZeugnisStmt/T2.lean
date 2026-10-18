/- Part 2 of 3 of `ZeugnisStmt` (split by instrumente/teile/lean-teilen.py; the umbrella `ZeugnisStmt.lean` imports all parts). -/
import Grammatik.Korpus.Zeugnis.ZeugnisStmt.T1

namespace Gabbro.Grammatik

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
  | .putBytes t f n lo hi i e =>
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
  | .shift t f lo hi von nach i =>
    inferInstanceAs (Decidable (intVonTyp (D.typ t f) = some (lo, hi) ∧
      certRange D Γ Λ i = some (0, D.count t - 1) ∧
      lo ≤ nach ∧ nach ≤ hi ∧ D.erlaubt t f von nach = true ∧
      V.schreibt t = true ∧ darf D t Λ ∧ Λ = Λ'))
  | .publish g e payload =>
    inferInstanceAs (Decidable (payload = D.nutzlast g ∧
      certRange D Γ Λ e ≠ none ∧
      certRange D Γ Λ e = intVonTyp (D.gtyp g) ∧
      V.gschreibt g = true ∧ gdarf D g Λ ∧ Λ = Λ'))
  | .regWrite r e =>
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
  | .retWhy r =>
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
    haveI := decEndGueltig D V l (.why (D.gruende f) :: Γ) (nach D f Λ) err
    haveI := decSeqGueltig D V l (.int lo hi :: Γ) (nach D f Λ) Λ' rest
    inferInstanceAs (Decidable (D.params f = [] ∧ 0 < D.gruende f ∧
      D.erg f = some (.int lo hi) ∧ Λ = Λc ∧
      certEndGueltig D V l (.why (D.gruende f) :: Γ) (nach D f Λ) err ∧
      certSeqGueltig D V l (.int lo hi :: Γ) (nach D f Λ) Λ' rest))
  | .regRead r lo hi rest =>
    haveI := decSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest
    inferInstanceAs (Decidable ((D.rklasse r).lesbar = true ∧
      intVonTyp (D.rtyp r) = some (lo, hi) ∧
      certSeqGueltig D V l (.int lo hi :: Γ) Λ Λ' rest))
  | .regReadElse r zusage sonst rest =>
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
  | .check c sonst rest =>
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
  | .retWhy r =>
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
  | .putBytes t f n lo hi i e =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hft, hii, hlo, hhi, hee, hw, hL, hout⟩ := h
    subst hout
    obtain ⟨ei, _⟩ := zeugnis_sound i lo hi hii
    obtain ⟨ee, _⟩ := zeugnis_sound e 0 (256 ^ n - 1) hee
    exact ⟨Stmt.putBytes t f hft n ei hlo hhi ee hw hL, trivial⟩
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
  | .shift t f lo hi von nach i =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hft, hii, hlo, hhi, he, hw, hL, hout⟩ := h
    subst hout
    have hτ : D.typ t f = .int lo hi := intVonTyp_eq hft
    obtain ⟨ei, _⟩ := zeugnis_sound i 0 (D.count t - 1) hii
    exact ⟨Stmt.shift t f hτ ei von nach ⟨hlo, hhi⟩ he hw hL, trivial⟩
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
  | .regWrite r e =>
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
      exact ⟨Stmt.regWrite r hk ee', trivial⟩
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
    exact ⟨Stmt.ret (by rw [he]; exact ErgExpr.empty) hΛ, trivial⟩
  | .retWert e lo hi =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨he, hrng, hΛ, hout⟩ := h
    subst hout
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi hrng
    exact ⟨Stmt.ret (by rw [he]; exact ErgExpr.val ee) hΛ, trivial⟩
  | .retWhy r =>
    intro h
    simp only [certStmtGueltig] at h
    obtain ⟨hlt, hΛ, hout⟩ := h
    subst hout
    exact ⟨Stmt.retWhy ⟨r, hlt⟩ hΛ, trivial⟩
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
      end_sound D V l (.why (D.gruende f) :: Γ) (nach D f Λ) err herr
    obtain ⟨r', _⟩ :=
      seq_sound D V l (.int lo hi :: Γ) (nach D f Λ) Λ' rest hrest
    exact ⟨Block.bindCallElse f (by rw [hpar]; exact Args.nil) he hp hgr
      es r', trivial⟩
  | .regRead r lo hi rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨hk, htyp, hrest⟩ := h
    have hτ : D.rtyp r = .int lo hi := intVonTyp_eq htyp
    obtain ⟨r', _⟩ := seq_sound D V l (.int lo hi :: Γ) Λ Λ' rest hrest
    have r'' : Block D V l (D.rtyp r :: Γ) Λ Λ' := by rw [hτ]; exact r'
    exact ⟨Block.regRead r hk r'', trivial⟩
  | .regReadElse r zusage sonst rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨hk, hz, hsonst, hrest⟩ := h
    obtain ⟨ez, _⟩ := cond_sound zusage hz
    obtain ⟨es, _⟩ := end_sound D V l Γ Λ sonst hsonst
    obtain ⟨r', _⟩ := seq_sound D V l (D.rtyp r :: Γ) Λ Λ' rest hrest
    exact ⟨Block.regReadElse r hk ez es r', trivial⟩
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
  | .check c sonst rest =>
    intro h
    simp only [certSeqGueltig] at h
    obtain ⟨hc, hsonst, hrest⟩ := h
    obtain ⟨ec, _⟩ := cond_sound c hc
    obtain ⟨es, _⟩ := end_sound D V l Γ Λ sonst hsonst
    obtain ⟨r', _⟩ := seq_sound D V l Γ Λ Λ' rest hrest
    exact ⟨Block.check ec es r', trivial⟩

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
    exact ⟨Endblock.ret (by rw [he]; exact ErgExpr.empty) hΛ, trivial⟩
  | .retWert e lo hi =>
    intro h
    simp only [certEndGueltig] at h
    obtain ⟨he, hrng, hΛ⟩ := h
    obtain ⟨ee, _⟩ := zeugnis_sound e lo hi hrng
    exact ⟨Endblock.ret (by rw [he]; exact ErgExpr.val ee) hΛ, trivial⟩
  | .retWhy r =>
    intro h
    simp only [certEndGueltig] at h
    obtain ⟨hlt, hΛ⟩ := h
    exact ⟨Endblock.retWhy ⟨r, hlt⟩ hΛ, trivial⟩
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

end Gabbro.Grammatik
