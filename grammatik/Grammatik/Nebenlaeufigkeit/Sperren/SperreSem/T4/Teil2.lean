module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T3
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T4.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Stufen
variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semH_nextWieder {Λ Λx : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semH S O U passes R (.dann (.cons (.next h) rest) (.wiederRest n bis body ueber k)) σ ρ =
      semH S O U passes R (.wieder n bis body ueber k) σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_leaveEwig {Λ Λx : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semH S O U passes R (.dann (.cons (.leave h) rest) (.ewigRest a n inv body k)) σ ρ =
      semH S O U passes R k σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_nextEwig {Λ Λx : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semH S O U passes R (.dann (.cons (.next h) rest) (.ewigRest a n inv body k)) σ ρ =
      semH S O U passes R (.ewig a n inv body k) σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_peelDann {Γ : Ctx} {Λ Λ1 Λ2 : List (Res D)}
    (rest : Block D V true Γ Λ Λ1) (b : Block D V true Γ Λ1 Λ2) (k : GRest D V true Γ Λ2)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) :
    semH S O U passes R (.dann (.cons (if x then .leave h else .next h) rest) (.dann b k)) σ ρ =
      semH S O U passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ := by
  rw [semH_dann_cons, semH_dann_cons]
  cases x <;> rfl

theorem semH_peelSchrumpf {Γ : Ctx} {Λ Λ1 : List (Res D)} {τ : Ty}
    (rest : Block D V true (τ :: Γ) Λ Λ1) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D (τ :: Γ)) (h : true = true) (x : Bool) :
    semH S O U passes R (.dann (.cons (if x then .leave h else .next h) rest) (.schrumpf k)) σ ρ =
      semH S O U passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ.tail := by
  rw [semH_dann_cons, semH_dann_cons]
  cases x <;> rfl

/-- **A `leave`/`next` out of a `locks` body releases through the check.** -/
theorem semH_peelFrei {Γ : Ctx} {Λ Λ1 : List (Res D)} (L : D.Lock)
    (rest : Block D V true Γ Λ (Res.held L :: Λ1)) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) (hi : S.inv L σ.speicher = true) :
    semH S O U passes R (.dann (.cons (if x then .leave h else .next h) rest) (.frei L k)) σ ρ =
      semH S O U passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) (σ.gibt L) ρ := by
  rw [semH_dann_cons, semH_dann_cons]
  cases x
  · show weiterH S O U passes R k (freiH S L (.next h σ ρ)) =
      weiterH S O U passes R k (.next h (σ.gibt L) ρ)
    simp only [freiH, hi, if_true]
  · show weiterH S O U passes R k (freiH S L (.leave h σ ρ)) =
      weiterH S O U passes R k (.leave h (σ.gibt L) ρ)
    simp only [freiH, hi, if_true]

/-- **A `leave`/`next` out of a `locks` body where the invariant fails
    predicts `logik schleife`.** -/
theorem semH_peelFrei_falsch {Γ : Ctx} {Λ Λ1 : List (Res D)} (L : D.Lock)
    (rest : Block D V true Γ Λ (Res.held L :: Λ1)) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) (hi : S.inv L σ.speicher = false) :
    semH S O U passes R (.dann (.cons (if x then .leave h else .next h) rest) (.frei L k)) σ ρ =
      .logik .schleife := by
  rw [semH_dann_cons]
  cases x
  · show weiterH S O U passes R k (freiH S L (.next h σ ρ)) = _
    simp only [freiH, hi, Bool.false_eq_true, if_false]
    exact weiterH_logik S O U passes R k _
  · show weiterH S O U passes R k (freiH S L (.leave h σ ρ)) = _
    simp only [freiH, hi, Bool.false_eq_true, if_false]
    exact weiterH_logik S O U passes R k _

theorem semH_peelAbbruch {Γ : Ctx} {Λ Λ1 Λk : List (Res D)}
    (rest : Block D V true Γ Λ Λ1) (k : GRest D V true Γ Λk)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) :
    semH S O U passes R (.dann (.cons (if x then .leave h else .next h) rest) (.abbruch k)) σ ρ =
      semH S O U passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ := by
  rw [semH_dann_cons, semH_dann_cons]
  cases x <;> rfl

/-- The `else` residue after a reason answer (`.abbruch (.schrumpf k)`)
    means the end block's outcome, the reason dropped, continued by `k`. -/
theorem semH_alsBlock_schrumpf {Λ Λk : List (Res D)} {τ : Ty} (e : Endblock D V l (τ :: Γ) Λ)
    (k : GRest D V l Γ Λk) (σ : World D) (ρ : Env D (τ :: Γ)) :
    semH S O U passes R (.dann e.alsBlock.2 (.abbruch (.schrumpf k))) σ ρ =
      weiterH S O U passes R k (execEndH S O U passes R e σ ρ).schrumpf.zuAusgang := by
  rw [semH_alsBlock]
  cases execEndH S O U passes R e σ ρ <;> rfl

/-! ### Returns -/

theorem semH_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    (semH S O U passes R (.ende (.ret (l := l) e hperm)) σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) :=
  ZErgG.gleich_refl _

theorem semH_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    (semH S O U passes R (.ende (.cons (.ret e hperm) rest)) σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  rw [semH_ende_cons]
  exact ZErgG.gleich_refl _

theorem semH_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    (semH S O U passes R (.dann (.cons (.ret e hperm) rest) k) σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  rw [semH_dann_cons]
  exact weiterH_zurueck S O U passes R (.dann rest k) _ _

/-! ### Reason returns (2026-09-14): the residue predicts the reason exit
    at the current world -/

theorem semH_rueckGrund {Λ : List (Res D)} (r : Fin V.gruende) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    (semH S O U passes R (.ende (.retWhy (l := l) r hperm)) σ ρ).gleich (.why σ r) :=
  ZErgG.gleich_refl _

theorem semH_rueckConsGrund {Λ : List (Res D)} (r : Fin V.gruende) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    (semH S O U passes R (.ende (.cons (.retWhy r hperm) rest)) σ ρ).gleich (.why σ r) := by
  rw [semH_ende_cons]
  exact ZErgG.gleich_refl _

theorem semH_dannRetGrund {Λ Λ'' : List (Res D)} (r : Fin V.gruende)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    (semH S O U passes R (.dann (.cons (.retWhy r hperm) rest) k) σ ρ).gleich (.why σ r) := by
  rw [semH_dann_cons]
  exact weiterH_grund S O U passes R (.dann rest k) _ _

/-! ### The device forms -/

theorem semH_regLies {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) = some v)
    (hz : D.rzusage r v = true) :
    semH S O U passes R (.dann (.regRead r hk rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.fragt (.inr (.inl r))) (.cons v ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv, hz, if_true]
  rfl

theorem semH_regLiesElseWahr {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) = some v)
    (hw : wahr? (eval ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) zusage ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) (.cons v ρ)) = true) :
    semH S O U passes R (.dann (.regReadElse r hk zusage sonst rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) (.cons v ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv, hw, if_true]
  rfl

theorem semH_regLiesElseFalsch {Λ Λ' : List (Res D)} (r : D.Reg)
    (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) = some v)
    (hw : wahr? (eval ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) zusage ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) (.cons v ρ)) = false) :
    (semH S O U passes R (.dann (.regReadElse r hk zusage sonst rest) k) σ ρ).folgt
      (semH S O U passes R (.dann sonst.alsBlock.2 (.abbruch k)) ((σ.fragt (.inr (.inl r))).lese Λ zusage.orte) ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv, hw, Bool.false_eq_true, if_false]
  rw [semH_alsBlock]
  exact ZErgG.folgt_refl _

theorem semH_awaits {Λ Λ' : List (Res D)} (g : D.Glob) (payload : List D.Glob)
    (hp : payload = D.nutzlast g) (hL : gdarf D g Λ) (hat : D.atomar g = true) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) (hvis : O.sichtbar g (σ.fragt (.inr (.inr g))) = true) :
    semH S O U passes R (.dann (.awaits g payload hp hL hat rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) ((σ.fragt (.inr (.inr g))).lese Λ [.inr g])
        (.cons (((σ.fragt (.inr (.inr g))).lese Λ [.inr g]).globs g) ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hvis, if_true]
  rfl

/-! ### The checks of G, failing -/

theorem semH_trav_falsch {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (ks : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false) :
    semH S O U passes R (.trav t inv body ks k) σ ρ = .logik .schleife := by
  cases ks with
  | nil =>
      simp only [semH, weiterH, laufA, traverseLauf, leseB, hw]
      exact weiterH_logik S O U passes R k _
  | cons i is =>
      simp only [semH, weiterH, laufA, traverseLauf, leseB, hw]
      exact weiterH_logik S O U passes R k _

theorem semH_ewig_falsch {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false) :
    semH S O U passes R (.ewig a (n + 1) inv body k) σ ρ = .logik .schleife := by
  simp only [semH, weiterH, laufA, foreverLauf, leseB, hw]
  exact weiterH_logik S O U passes R k _

theorem semH_leaveTrav_falsch {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ) (hl : true = true)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false) :
    semH S O U passes R (.dann (.cons (.leave hl) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      .logik .schleife := by
  rw [semH_dann_cons]
  show weiterH S O U passes R (.travRest t inv body is k) (.leave hl σ (.cons i ρ)) = _
  simp only [weiterH, leseB, Env.tail, hw]
  exact weiterH_logik S O U passes R k _

end Stufen

end Gabbro.Grammatik
