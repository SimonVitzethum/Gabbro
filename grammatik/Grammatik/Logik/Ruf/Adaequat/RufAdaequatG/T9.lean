/- Part 9 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T8

namespace Gabbro.Grammatik

variable {D : Deklaration}

section SemSchritt

variable (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem sem_blatt {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
    (σ σ' : World D) (ρ ρ' : Env D Γ) (h : execStmt O passes keinRuf s σ ρ = .ok σ' ρ') :
    semR O passes (.ende rest) σ' ρ' = semR O passes (.ende (.cons s rest)) σ ρ := by
  simp only [semR, execEnd, h]

theorem sem_dannBlatt {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ σ' : World D) (ρ ρ' : Env D Γ)
    (h : execStmt O passes keinRuf s σ ρ = .ok σ' ρ') :
    semR O passes (.dann rest k) σ' ρ' = semR O passes (.dann (.cons s rest) k) σ ρ := by
  rw [semR_dann O passes (.cons s rest), nachA_cons, h]
  rfl

theorem sem_endeEntf {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann (.cons s .nil) (.ende rest)) σ ρ =
      semR O passes (.ende (.cons s rest)) σ ρ := by
  rw [semR_dann, nachA_cons]
  exact (endErg_cons O passes s rest σ ρ).symm

theorem sem_iteWahr {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semR O passes (.dann t (.dann rest k)) (σ.lese Λ c.orte) ρ =
      semR O passes (.dann (.cons (.ite c t e) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt, hw, if_true]

theorem sem_iteFalsch {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    semR O passes (.dann e (.dann rest k)) (σ.lese Λ c.orte) ρ =
      semR O passes (.dann (.cons (.ite c t e) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt, hw, Bool.false_eq_true, if_false]

theorem sem_optSome {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (.index n))
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v) :
    semR O passes (.dann p (.schrumpf (.dann rest k))) (σ.lese Λ o.orte) (.cons v ρ) =
      semR O passes (.dann (.cons (.onOption o p a) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt, hv]
  rw [nachA_schrumpf]

theorem sem_optNone {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none) :
    semR O passes (.dann a (.dann rest k)) (σ.lese Λ o.orte) ρ =
      semR O passes (.dann (.cons (.onOption o p a) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt, hv]

theorem sem_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (lo hi : Int) (b : Block D V l (.int lo hi :: Γ) Λ Λ') (nutz : Nutzlast (some (lo, hi)))
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some (lo, hi), b, nutz⟩) :
    semR O passes (.dann b (.schrumpf (.dann rest k))) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semR O passes (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact (semR_dann O passes b _ _ _).trans (nachA_schrumpf O passes _ _).symm

theorem sem_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast none)
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    semR O passes (.dann b (.dann rest k)) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semR O passes (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact semR_dann O passes b _ _ _

theorem sem_grund {Λ Λ' Λ'' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.why n))
    (arms : GrundArms D V l Γ Λ Λ' n) (rest : Block D V l Γ Λ' Λ'')
    (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann (grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ))
        (.dann rest k)) (σ.lese Λ r.orte) ρ =
      semR O passes (.dann (.cons (.onWhy r arms) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt]
  rw [execGrund_wahlW O passes keinRuf arms]

theorem sem_breaking {Λ Λ' Λ'' : List (Res D)} (i : D.Inv) (body : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann body (.dann rest k)) σ ρ =
      semR O passes (.dann (.cons (.breaking i body) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt]

theorem sem_locks {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    (semR O passes (.dann body (.frei L (.dann rest k))) (σ.nimmt L) ρ).gleich
      (semR O passes (.dann (.cons (.locks L hr body) rest) k) σ ρ) := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons, semR_dann]
  simp only [execStmt]
  exact nachA_frei O passes _ L _

theorem sem_endeBind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Endblock D V l (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    semR O passes (.ende rest) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) =
      semR O passes (.ende (.bind e rest)) σ ρ := by
  simp only [semR, execEnd]
  rw [endErg_schrumpf]

theorem sem_dannBind {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) =
      semR O passes (.dann (.bind e rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock]
  rw [nachA_schrumpf]

theorem sem_narrowOk {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ) =
      semR O passes (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semR_dann O passes (.narrow e lo' hi' sonst rest), execBlock_narrow]
  unfold narrowWeiter
  rw [dif_pos h, nachA_schrumpf, semR_dann]

theorem Endblock.ohneOrakel_alsBlock {V : Vertrag D} {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
      e.alsBlock.2.ohneOrakel = e.ohneOrakel
  | _, _, .ret _ _ => rfl
  | _, _, .retWhy _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
  | _, _, .bind _ rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
  | _, _, .bindCall _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
  | _, _, .bindAxiom .. => rfl
  | _, _, .bindAxiomElse .. => rfl

/-- A covered end block run as a block is a covered block. -/
theorem EndG.alsBlock {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {e : Endblock D V l Γ Λ},
      EndG A e → BlockG A true e.alsBlock.2
  | _, _, _, _, .ret e hΛ => .cons _ _ (.ret e hΛ) .nil
  | _, _, _, _, .cons s _ hs hr => .cons s _ hs (EndG.alsBlock hr)
  | _, _, _, _, .bind e _ hr => .bind e _ (EndG.alsBlock hr)

/-- An end block run as a block in front of any continuation means the end
    block (it never ends normally). -/
theorem semR_alsBlock {Λ Λk : List (Res D)} (e : Endblock D V l Γ Λ)
    (k : GRest D V l Γ Λk) (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann e.alsBlock.2 (.abbruch k)) σ ρ = semR O passes (.ende e) σ ρ := by
  rw [semR_dann, Endblock.execBlock_alsBlock, nachA_zuAusgang]
  rfl

theorem sem_narrowElse {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    semR O passes (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ e.orte) ρ =
      semR O passes (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semR_alsBlock]
  rw [semR_dann O passes (.narrow e lo' hi' sonst rest), execBlock_narrow]
  unfold narrowWeiter
  rw [dif_neg h, nachA_zuAusgang]
  rfl

theorem sem_pruefWahr {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semR O passes (.dann rest k) (σ.lese Λ c.orte) ρ =
      semR O passes (.dann (.check c sonst rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hw, if_true]

theorem sem_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    semR O passes (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ c.orte) ρ =
      semR O passes (.dann (.check c sonst rest) k) σ ρ := by
  rw [semR_alsBlock]
  rw [semR_dann]
  simp only [execBlock, hw, Bool.false_eq_true, if_false]
  rw [nachA_zuAusgang]
  rfl

theorem sem_exchange {Λ Λ' : List (Res D)} (g : D.Glob)
    (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
    (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann rest (.schrumpf k))
        ((σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
            (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ)))
        (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ) =
      semR O passes (.dann (.exchange g neuE hw hL rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock]
  rw [nachA_schrumpf]

theorem sem_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) =
      semR O passes (.dann (.float op a b lo hi rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hv]
  rw [nachA_schrumpf]

theorem sem_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semR O passes (.dann rest (.schrumpf k)) σ (.cons v ρ) =
      semR O passes (.dann (.floatLit q lo hi rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hv]
  rw [nachA_schrumpf]

theorem sem_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semR O passes (.dann (.floatOf e lo hi rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hv]
  rw [nachA_schrumpf]

theorem sem_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semR O passes (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hv]
  rw [nachA_schrumpf]

theorem sem_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    semR O passes (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ e.orte) ρ =
      semR O passes (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semR_alsBlock]
  rw [semR_dann]
  simp only [execBlock, hn]
  rw [nachA_zuAusgang]
  rfl

theorem sem_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    semR O passes (.ende (.ret (l := l) e hperm)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := rfl

theorem sem_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semR O passes (.ende (.cons (.ret e hperm) rest)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  simp only [semR, execEnd, execStmt, endErg]

theorem sem_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann (.cons (.ret e hperm) rest) k) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  rw [semR_dann, nachA_cons]
  rfl

end SemSchritt
theorem faeden_upd (sp : Speicher D) (m : Faden → RufFadenG D) (f : Faden)
    (z : RufFadenG D) (la : Lauf D) (st : World D) :
    (⟨sp, rufUpdateG m f z, la, st⟩ : RufMaschineG D).faeden f = z :=
  rufUpdateG_self m f z

theorem weltVon_upd (sp : Speicher D) (m : Faden → RufFadenG D) (f : Faden)
    (z : RufFadenG D) (la : Lauf D) (st : World D) :
    (⟨sp, rufUpdateG m f z, la, st⟩ : RufMaschineG D).weltVon f = sp.welt z.spur := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]

/-- What one step of thread `f` does to a covered frame: either the frame
    stays on top with a covered residue and the same frame result (up to
    the trace), or it pops, logging a `rueck` whose world and value ARE the
    frame result (up to the trace). -/
def ErhaltG (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) (M M' : RufMaschineG D)
    (f : Faden) (z : RufFadenG D) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D z.kopf.f) l Γ Λ) : Prop :=
  (∃ (l' : Bool) (Γ' : Ctx) (Λ' : List (Res D)) (ρ' : Env D Γ')
      (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (sp : List (Ereignis D)),
      M'.faeden f = ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, sp, z.log⟩ ∧
      RestG A r' ∧ (semR O passes r' (M'.weltVon f) ρ').gleich (semR O passes r (M.weltVon f) ρ)) ∨
  (∃ (v : ErgVal D (D.erg z.kopf.f)) (s1 : World D),
      (M'.faeden f).log = RufEreignisF.rueck z.kopf.f z.kopf.rho v z.kopf.s0 s1 :: z.log ∧
      (semR O passes r (M.weltVon f) ρ).gleich (.zurueck s1 v))

set_option hygiene false in
/-- Refute a step whose head shape the covered residue cannot have. -/
macro "widerlege" h:ident : tactic => `(tactic| (
  rw [hR] at $h:ident
  cases $h:ident
  first
  | exact absurd hcov.dann_cons_art (by simp [Stmt.gArt, Stmt.blattArt])
  | exact absurd hcov.ende_cons_art (by simp [Stmt.gArt, Stmt.blattArt])
  | (obtain ⟨_, hbo, _⟩ := hcov.dann_inv; simp [Block.ohneOrakel] at hbo; done)
  | (obtain ⟨⟨_, hbw⟩, _, _⟩ := hcov.dann_inv; cases hbw; done)
  | (obtain ⟨hew, _⟩ := hcov.ende_inv; cases hew; done)
  | cases hcov))

theorem armWahlG_G {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    ArmsG A mr arms → BlockG A mr (armWahlG arms v).2.1
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, h => h.cons_inv.1
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, h => armWahlG_G rest _ h.cons_inv.2

theorem grundWahlG_G {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    GrundArmsG A mr arms → BlockG A mr (grundWahlG arms r)
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, h => h.cons_inv.1
  | _, .cons _ rest, ⟨_ + 1, _⟩, h => grundWahlG_G rest _ h.cons_inv.2

theorem armWahlG_G' {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs)
    (v : Wert D (.sum cs)) {c : Option (Int × Int)} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {nutz : Nutzlast c} (hw : armWahlG arms v = ⟨c, b, nutz⟩) (h : ArmsG A mr arms) :
    BlockG A mr b := by
  have h0 := armWahlG_G arms v h
  rw [hw] at h0
  exact h0

theorem armWahlG_ohne' {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs)
    (v : Wert D (.sum cs)) {c : Option (Int × Int)} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {nutz : Nutzlast c} (hw : armWahlG arms v = ⟨c, b, nutz⟩) (h : arms.ohneOrakel = true) :
    b.ohneOrakel = true := by
  have h0 := armWahlG_ohneOrakel arms v h
  rw [hw] at h0
  exact h0


end Gabbro.Grammatik
