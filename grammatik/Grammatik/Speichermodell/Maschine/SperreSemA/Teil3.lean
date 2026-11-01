module

public import Grammatik.Speichermodell.Atomar.AtomarSem
public import Grammatik.Speichermodell.Maschine.SperreSemA.Teil2

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section StufenA
variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semHA_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    (semHA S O U A passes R (.ende (.ret (l := l) e hperm)) σ ρ).gleich
      (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ)) :=
  ZErgG.gleich_refl _

theorem semHA_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    (semHA S O U A passes R (.ende (.cons (.ret e hperm) rest)) σ ρ).gleich
      (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ)) := by
  rw [semHA_ende_cons]
  exact ZErgG.gleich_refl _

theorem semHA_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    (semHA S O U A passes R (.dann (.cons (.ret e hperm) rest) k) σ ρ).gleich
      (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ)) := by
  rw [semHA_dann_cons]
  exact weiterHA_zurueck S O U A passes R (.dann rest k) _ _

/-! ### Reason returns (2026-09-14): the residue predicts the reason exit
    at the current world -/

theorem semHA_rueckGrund {Λ : List (Res D)} (r : Fin V.gruende) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    (semHA S O U A passes R (.ende (.retWhy (l := l) r hperm)) σ ρ).gleich (.why σ r) :=
  ZErgG.gleich_refl _

theorem semHA_rueckConsGrund {Λ : List (Res D)} (r : Fin V.gruende) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    (semHA S O U A passes R (.ende (.cons (.retWhy r hperm) rest)) σ ρ).gleich (.why σ r) := by
  rw [semHA_ende_cons]
  exact ZErgG.gleich_refl _

theorem semHA_dannRetGrund {Λ Λ'' : List (Res D)} (r : Fin V.gruende)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    (semHA S O U A passes R (.dann (.cons (.retWhy r hperm) rest) k) σ ρ).gleich (.why σ r) := by
  rw [semHA_dann_cons]
  exact weiterHA_grund S O U A passes R (.dann rest k) _ _

/-! ### The device forms -/

theorem semHA_regLies {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) = some v)
    (hz : D.rzusage r v = true) :
    semHA S O U A passes R (.dann (.regRead r hk rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (σ.fragt (.inr (.inl r))) (.cons v ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv, hz, if_true]
  rfl

theorem semHA_regLiesElseWahr {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) = some v)
    (hw : wahr? (eval (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) zusage (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) (.cons v ρ)) = true) :
    semHA S O U A passes R (.dann (.regReadElse r hk zusage sonst rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) (.cons v ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv, hw, if_true]
  rfl

theorem semHA_regLiesElseFalsch {Λ Λ' : List (Res D)} (r : D.Reg)
    (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) = some v)
    (hw : wahr? (eval (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) zusage (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) (.cons v ρ)) = false) :
    (semHA S O U A passes R (.dann (.regReadElse r hk zusage sonst rest) k) σ ρ).folgt
      (semHA S O U A passes R (.dann sonst.alsBlock.2 (.abbruch k)) (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv, hw, Bool.false_eq_true, if_false]
  rw [semHA_alsBlock]
  exact ZErgG.folgt_refl _

theorem semHA_awaits {Λ Λ' : List (Res D)} (g : D.Glob) (payload : List D.Glob)
    (hp : payload = D.nutzlast g) (hL : gdarf D g Λ) (hat : D.atomar g = true) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (hvis : O.sichtbar g (leseA A (σ.fragt (.inr (.inr g))) Λ [.inr g]) = true) :
    semHA S O U A passes R (.dann (.awaits g payload hp hL hat rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (leseA A (σ.fragt (.inr (.inr g))) Λ [.inr g])
        (.cons ((leseA A (σ.fragt (.inr (.inr g))) Λ [.inr g]).globs g) ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hvis, if_true]
  rfl

/-! ### The checks of G, failing -/

theorem semHA_trav_falsch {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (ks : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = false) :
    semHA S O U A passes R (.trav t inv body ks k) σ ρ = .logik .schleife := by
  cases ks with
  | nil =>
      simp only [semHA, weiterHA, laufA, traverseLauf, leseBA, hw]
      exact weiterHA_logik S O U A passes R k _
  | cons i is =>
      simp only [semHA, weiterHA, laufA, traverseLauf, leseBA, hw]
      exact weiterHA_logik S O U A passes R k _

theorem semHA_ewig_falsch {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = false) :
    semHA S O U A passes R (.ewig a (n + 1) inv body k) σ ρ = .logik .schleife := by
  simp only [semHA, weiterHA, laufA, foreverLauf, leseBA, hw]
  exact weiterHA_logik S O U A passes R k _

theorem semHA_leaveTrav_falsch {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ) (hl : true = true)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = false) :
    semHA S O U A passes R (.dann (.cons (.leave hl) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      .logik .schleife := by
  rw [semHA_dann_cons]
  show weiterHA S O U A passes R (.travRest t inv body is k) (.leave hl σ (.cons i ρ)) = _
  simp only [weiterHA, leseBA, Env.tail, hw]
  exact weiterHA_logik S O U A passes R k _

end StufenA

end Gabbro.Grammatik
