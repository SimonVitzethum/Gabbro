module

public import Grammatik.Korpus.Zeugnis.ZeugnisStmt.T1

@[expose] public section



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
    inferInstanceAs (Decidable (payload = D.nutzlast g ∧ gdarf D g Λ ∧ D.atomar g = true ∧
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

end Gabbro.Grammatik
