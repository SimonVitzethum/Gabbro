module
public import Grammatik.Speichermodell.Maschine.SperreSemA.Teil1Basis
import all Grammatik.Speichermodell.Maschine.SperreSemA.Teil1Basis

public import Grammatik.Speichermodell.Atomar.AtomarSem

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 4. The residue step lemmas, one per rule of G -/

section StufenA

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semHA_ende_cons {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.ende (.cons s rest)) σ ρ =
      weiterHA S O U A passes R (.ende rest) (execStmtHA S O U A passes R s σ ρ) := by
  show zErgG (execEndHA S O U A passes R (.cons s rest) σ ρ) = _
  simp only [execEndHA]
  cases execStmtHA S O U A passes R s σ ρ <;> rfl

theorem laufAHA_nil {Λ : List (Res D)} (o : Ausgang V l Γ) :
    laufA (fun σ ρ => execBlockHA S O U A passes R (.nil : Block D V l Γ Λ Λ) σ ρ) o = o := by
  cases o <;> rfl

theorem semHA_endeEntf {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.ende (.cons s rest)) σ ρ =
      semHA S O U A passes R (.dann (.cons s .nil) (.ende rest)) σ ρ := by
  rw [semHA_ende_cons, semHA_dann_cons]
  show _ = weiterHA S O U A passes R (.ende rest) (laufA _ _)
  rw [laufAHA_nil]

theorem semHA_dannLeer {Λ : List (Res D)} (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann .nil k) σ ρ = semHA S O U A passes R k σ ρ := by rfl

theorem semHA_ite {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) (b : Bool)
    (hw : wahr? (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ) = b) :
    semHA S O U A passes R (.dann (.cons (.ite c t e) rest) k) σ ρ =
      semHA S O U A passes R (.dann (if b then t else e) (.dann rest k)) (leseA A σ Λ c.orte) ρ := by
  rw [semHA_dann_cons]
  cases b <;> simp only [execStmtHA, hw] <;> rfl

theorem semHA_optSome {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (.index n))
    (hv : eval (leseA A σ Λ o.orte) o (leseA A σ Λ o.orte) ρ = Option.some v) :
    semHA S O U A passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ =
      semHA S O U A passes R (.dann p (.schrumpf (.dann rest k))) (leseA A σ Λ o.orte) (.cons v ρ) := by
  rw [semHA_dann_cons]
  simp only [execStmtHA, hv]
  rfl

theorem semHA_optNone {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (hv : eval (leseA A σ Λ o.orte) o (leseA A σ Λ o.orte) ρ = Option.none) :
    semHA S O U A passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ =
      semHA S O U A passes R (.dann a (.dann rest k)) (leseA A σ Λ o.orte) ρ := by
  rw [semHA_dann_cons]
  simp only [execStmtHA, hv]
  rfl

theorem semHA_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option Ty)}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (τ : Ty) (b : Block D V l (τ :: Γ) Λ Λ') (nutz : Nutzlast D.Fn D.passt (some τ))
    (hw : armWahlG arms (eval (leseA A σ Λ v.orte) v (leseA A σ Λ v.orte) ρ) =
      ⟨some τ, b, nutz⟩) :
    semHA S O U A passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ =
      semHA S O U A passes R (.dann b (.schrumpf (.dann rest k))) (leseA A σ Λ v.orte)
        (armEnv nutz ρ) := by
  rw [semHA_dann_cons]
  simp only [execStmtHA]
  rw [execArmsHA_wahl, hw]
  rfl

theorem semHA_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option Ty)}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast D.Fn D.passt none)
    (hw : armWahlG arms (eval (leseA A σ Λ v.orte) v (leseA A σ Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    semHA S O U A passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ =
      semHA S O U A passes R (.dann b (.dann rest k)) (leseA A σ Λ v.orte) (armEnv nutz ρ) := by
  rw [semHA_dann_cons]
  simp only [execStmtHA]
  rw [execArmsHA_wahl, hw]
  rfl

end StufenA
end Gabbro.Grammatik
