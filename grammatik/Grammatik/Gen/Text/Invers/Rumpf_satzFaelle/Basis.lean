module

public import Grammatik.Gen.Text.Invers.Geraet

@[expose] public section


namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

variable {z : Spez} {V : Vertrag z.deklaration} (gNr : Nat → Nat) (tabs : List UTab) (koepfe : List UFnKopf)

/-- What the run reader does with a printed statement, a block, an end block (of size below `n`). -/
def RumpfSatz (n : Nat) : Prop :=
  (∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} (s : Stmt z.deklaration V l Γ Λ Λ') (ctx : UCtx)
      (art : Nat → UParamArt) (ss : List SAnw) (us : List UStmt),
      sizeOf s < n → SInv z V ctx Γ Λ art → delabS z V s = .ok ss → uOfSt z V gNr art s = some us →
      Λ' = Λ ∧ ss.length ≤ 2 ∧ ∃ ctx', SInv z V ctx' Γ Λ art ∧ ∀ f tail xs cE, sizeOf s < f →
        uAnwReihe tabs koepfe f ctx' tail = .ok (xs, cE) →
        uAnwReihe tabs koepfe (f + ss.length) ctx (ss ++ tail) = .ok (us ++ xs, cE)) ∧
  (∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} (b : Block z.deklaration V l Γ Λ Λ') (ctx : UCtx)
      (art : Nat → UParamArt) (f : Nat) (ss : List SAnw) (us : List UStmt),
      sizeOf b < n → sizeOf b < f → SInv z V ctx Γ Λ art → delabB z V b = .ok ss → uOfBl z V gNr art b = some us →
      Λ' = Λ ∧ ∃ cE, uAnwReihe tabs koepfe f ctx ss = .ok (us, cE)) ∧
  (∀ {l : Bool} {Γ : Ctx} {Λ : List (Res z.deklaration)} (e : Endblock z.deklaration V l Γ Λ) (ctx : UCtx)
      (art : Nat → UParamArt) (f : Nat) (es : List SAnw) (en : Option SEnde) (us : List UStmt) (r : URet),
      sizeOf e < n → sizeOf e < f → SInv z V ctx Γ Λ art → delabEnd z V e = .ok (es, en) →
      uOfEnd z V gNr art e = some (us, r) →
      ∃ cE, uAnwReihe tabs koepfe f ctx es = .ok (us, cE) ∧ uEnde cE en = .ok r ∧ ∃ v, en = some (.ret v))

end Gabbro.Grammatik.Gen.Text
