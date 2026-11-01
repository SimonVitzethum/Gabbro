module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem.T2
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem.T3.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Stufen
variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semV_nextWieder {Λ Λx : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semV O passes R (.dann (.cons (.next h) rest) (.wiederRest n bis body ueber k)) σ ρ =
      semV O passes R (.wieder n bis body ueber k) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_leaveEwig {Λ Λx : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semV O passes R (.dann (.cons (.leave h) rest) (.ewigRest a n inv body k)) σ ρ =
      semV O passes R k σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_nextEwig {Λ Λx : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semV O passes R (.dann (.cons (.next h) rest) (.ewigRest a n inv body k)) σ ρ =
      semV O passes R (.ewig a n inv body k) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_peelDann {Γ : Ctx} {Λ Λ1 Λ2 : List (Res D)}
    (rest : Block D V true Γ Λ Λ1) (b : Block D V true Γ Λ1 Λ2) (k : GRest D V true Γ Λ2)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) :
    semV O passes R (.dann (.cons (if x then .leave h else .next h) rest) (.dann b k)) σ ρ =
      semV O passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ := by
  rw [semV_dann_cons, semV_dann_cons]
  cases x <;> rfl

theorem semV_peelSchrumpf {Γ : Ctx} {Λ Λ1 : List (Res D)} {τ : Ty}
    (rest : Block D V true (τ :: Γ) Λ Λ1) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D (τ :: Γ)) (h : true = true) (x : Bool) :
    semV O passes R (.dann (.cons (if x then .leave h else .next h) rest) (.schrumpf k)) σ ρ =
      semV O passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ.tail := by
  rw [semV_dann_cons, semV_dann_cons]
  cases x <;> rfl

theorem semV_peelFrei {Γ : Ctx} {Λ Λ1 : List (Res D)} (L : D.Lock)
    (rest : Block D V true Γ Λ (Res.held L :: Λ1)) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) :
    semV O passes R (.dann (.cons (if x then .leave h else .next h) rest) (.frei L k)) σ ρ =
      semV O passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) (σ.gibt L) ρ := by
  rw [semV_dann_cons, semV_dann_cons]
  cases x <;> rfl

theorem semV_peelAbbruch {Γ : Ctx} {Λ Λ1 Λk : List (Res D)}
    (rest : Block D V true Γ Λ Λ1) (k : GRest D V true Γ Λk)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) :
    semV O passes R (.dann (.cons (if x then .leave h else .next h) rest) (.abbruch k)) σ ρ =
      semV O passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ := by
  rw [semV_dann_cons, semV_dann_cons]
  cases x <;> rfl

/-- The `else` residue after a reason answer (`.abbruch (.schrumpf k)`)
    means the end block's outcome, the reason dropped, continued by `k`. -/
theorem semV_alsBlock_schrumpf {Λ Λk : List (Res D)} {τ : Ty} (e : Endblock D V l (τ :: Γ) Λ)
    (k : GRest D V l Γ Λk) (σ : World D) (ρ : Env D (τ :: Γ)) :
    semV O passes R (.dann e.alsBlock.2 (.abbruch (.schrumpf k))) σ ρ =
      weiterZ O passes R k (execEnd O passes R e σ ρ).schrumpf.zuAusgang := by
  rw [semV_alsBlock]
  cases execEnd O passes R e σ ρ <;> rfl

/-! ### Returns -/

theorem semV_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    (semV O passes R (.ende (.ret (l := l) e hperm)) σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) :=
  ZErg.gleich_refl _

theorem semV_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    (semV O passes R (.ende (.cons (.ret e hperm) rest)) σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  rw [semV_ende_cons]
  exact ZErg.gleich_refl _

theorem semV_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    (semV O passes R (.dann (.cons (.ret e hperm) rest) k) σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  rw [semV_dann_cons]
  exact weiterZ_zurueck O passes R (.dann rest k) _ _

end Stufen

end Gabbro.Grammatik
