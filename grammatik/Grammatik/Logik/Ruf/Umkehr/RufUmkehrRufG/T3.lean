/- Part 3 of 6 of `RufUmkehrRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufUmkehrRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

section SemSchrittK

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
  {Γ : Ctx}

theorem semK_blatt {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
    (σ σ' : World D) (ρ ρ' : Env D Γ) (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    semK O passes R (.ende rest) σ' ρ' = semK O passes R (.ende (.cons s rest)) σ ρ := by
  simp only [semK, execEnd, h]

theorem semK_dannBlatt {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ σ' : World D) (ρ ρ' : Env D Γ)
    (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    semK O passes R (.dann rest k) σ' ρ' = semK O passes R (.dann (.cons s rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons s rest), nachK_cons, h]
  rfl

theorem semK_endeEntf {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann (.cons s .nil) (.ende rest)) σ ρ =
      semK O passes R (.ende (.cons s rest)) σ ρ := by
  rw [semK_dann, nachK_cons]
  exact (endErgK_cons O passes R s rest σ ρ).symm

theorem semK_iteWahr {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semK O passes R (.dann t (.dann rest k)) (σ.lese Λ c.orte) ρ =
      semK O passes R (.dann (.cons (.ite c t e) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt, hw, if_true]

theorem semK_iteFalsch {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    semK O passes R (.dann e (.dann rest k)) (σ.lese Λ c.orte) ρ =
      semK O passes R (.dann (.cons (.ite c t e) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt, hw, Bool.false_eq_true, if_false]

theorem semK_optSome {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (.index n))
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v) :
    semK O passes R (.dann p (.schrumpf (.dann rest k))) (σ.lese Λ o.orte) (.cons v ρ) =
      semK O passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt, hv]
  rw [nachK_schrumpf]

theorem semK_optNone {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none) :
    semK O passes R (.dann a (.dann rest k)) (σ.lese Λ o.orte) ρ =
      semK O passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt, hv]

theorem semK_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (lo hi : Int) (b : Block D V l (.int lo hi :: Γ) Λ Λ') (nutz : Nutzlast (some (lo, hi)))
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some (lo, hi), b, nutz⟩) :
    semK O passes R (.dann b (.schrumpf (.dann rest k))) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semK O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact (semK_dann O passes R b _ _ _).trans (nachK_schrumpf O passes R _ _).symm

theorem semK_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast none)
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    semK O passes R (.dann b (.dann rest k)) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semK O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact semK_dann O passes R b _ _ _

theorem semK_grund {Λ Λ' Λ'' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.why n))
    (arms : GrundArms D V l Γ Λ Λ' n) (rest : Block D V l Γ Λ' Λ'')
    (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann (grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ))
        (.dann rest k)) (σ.lese Λ r.orte) ρ =
      semK O passes R (.dann (.cons (.onWhy r arms) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt]
  rw [execGrund_wahlW O passes R arms]

theorem semK_breaking {Λ Λ' Λ'' : List (Res D)} (i : D.Inv) (body : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann body (.dann rest k)) σ ρ =
      semK O passes R (.dann (.cons (.breaking i body) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt]

theorem semK_locks {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    (semK O passes R (.dann body (.frei L (.dann rest k))) (σ.nimmt L) ρ).gleich
      (semK O passes R (.dann (.cons (.locks L hr body) rest) k) σ ρ) := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt]
  exact nachK_frei O passes R _ L _

theorem semK_endeBind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Endblock D V l (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.ende rest) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) =
      semK O passes R (.ende (.bind e rest)) σ ρ := by
  simp only [semK, execEnd]
  rw [endErg_schrumpf]

theorem semK_dannBind {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) =
      semK O passes R (.dann (.bind e rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock]
  rw [nachK_schrumpf]

theorem semK_narrowOk {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    semK O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ) =
      semK O passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semK_dann O passes R (.narrow e lo' hi' sonst rest), execBlock_narrowK]
  unfold narrowWeiterK
  rw [dif_pos h, nachK_schrumpf, semK_dann]

theorem Endblock.kOk_alsBlock {V : Vertrag D} {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), e.alsBlock.2.kOk = e.kOk
  | _, _, .ret _ _ => rfl
  | _, _, .retWhy _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, Block.kOk, Endblock.kOk, Endblock.kOk_alsBlock rest]
  | _, _, .bind _ rest => by
      simp only [Endblock.alsBlock, Block.kOk, Endblock.kOk, Endblock.kOk_alsBlock rest]
  | _, _, .bindCall _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.kOk, Endblock.kOk, Endblock.kOk_alsBlock rest]
  | _, _, .bindAxiom .. => rfl
  | _, _, .bindAxiomElse .. => rfl

/-- A covered end block run as a block is a covered block. -/
theorem EndR.alsBlock {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {e : Endblock D V l Γ Λ},
      EndR A C e → BlockR A C true e.alsBlock.2
  | _, _, _, _, .ret e hΛ => .cons _ _ (.ret e hΛ) .nil
  | _, _, _, _, .retWhy r hΛ => by
      simp only [Endblock.alsBlock]
      exact .cons _ _ (@StmtR.retWhy _ _ A C _ false [] _ r hΛ) .nil
  | _, _, _, _, .cons s _ hs hr => .cons s _ hs (EndR.alsBlock hr)
  | _, _, _, _, .bind e _ hr => .bind e _ (EndR.alsBlock hr)

/-- An end block run as a block in front of any continuation means the end
    block (it never ends normally). -/
theorem semK_alsBlock {Λ Λk : List (Res D)} (e : Endblock D V l Γ Λ)
    (k : GRest D V l Γ Λk) (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann e.alsBlock.2 (.abbruch k)) σ ρ = semK O passes R (.ende e) σ ρ := by
  rw [semK_dann, Endblock.execBlock_alsBlock, nachK_zuAusgang]
  rfl

theorem semK_narrowElse {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    semK O passes R (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ e.orte) ρ =
      semK O passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semK_alsBlock]
  rw [semK_dann O passes R (.narrow e lo' hi' sonst rest), execBlock_narrowK]
  unfold narrowWeiterK
  rw [dif_neg h, nachK_zuAusgang]
  rfl

theorem semK_pruefWahr {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semK O passes R (.dann rest k) (σ.lese Λ c.orte) ρ =
      semK O passes R (.dann (.check c sonst rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock, hw, if_true]

theorem semK_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    semK O passes R (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ c.orte) ρ =
      semK O passes R (.dann (.check c sonst rest) k) σ ρ := by
  rw [semK_alsBlock]
  rw [semK_dann]
  simp only [execBlock, hw, Bool.false_eq_true, if_false]
  rw [nachK_zuAusgang]
  rfl

theorem semK_exchange {Λ Λ' : List (Res D)} (g : D.Glob)
    (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
    (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann rest (.schrumpf k))
        ((σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
            (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ)))
        (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ) =
      semK O passes R (.dann (.exchange g neuE hw hL rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock]
  rw [nachK_schrumpf]

theorem semK_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semK O passes R (.dann rest (.schrumpf k)) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) =
      semK O passes R (.dann (.float op a b lo hi rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock, hv]
  rw [nachK_schrumpf]

theorem semK_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semK O passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) =
      semK O passes R (.dann (.floatLit q lo hi rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock, hv]
  rw [nachK_schrumpf]

theorem semK_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semK O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semK O passes R (.dann (.floatOf e lo hi rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock, hv]
  rw [nachK_schrumpf]

theorem semK_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semK O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semK O passes R (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock, hv]
  rw [nachK_schrumpf]

theorem semK_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    semK O passes R (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ e.orte) ρ =
      semK O passes R (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semK_alsBlock]
  rw [semK_dann]
  simp only [execBlock, hn]
  rw [nachK_zuAusgang]
  rfl

theorem semK_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.ende (.ret (l := l) e hperm)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := rfl

theorem semK_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.ende (.cons (.ret e hperm) rest)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  simp only [semK, execEnd, execStmt, endErg]

theorem semK_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann (.cons (.ret e hperm) rest) k) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  rw [semK_dann, nachK_cons]
  rfl

end SemSchrittK
section RufSemK

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
  {Γ : Ctx}

/-- A call in block position, when the handler answers normally, continues
    with the rest. -/
theorem semK_rufDann {Λ Λ'' : List (Res D)} (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D V l Γ (nach D g Λ) Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (σ1 : World D) (v1 : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ1 v1) :
    semK O passes R (.dann (.cons (.call g args hp hr) rest) k) σ ρ =
      semK O passes R (.dann rest k) σ1 ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons]
  simp only [execStmt, h]
  rfl

/-- A call at `ende` position, when the handler answers normally. -/
theorem semK_ruf {Λ : List (Res D)} (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Endblock D V l Γ (nach D g Λ)) (σ : World D) (ρ : Env D Γ)
    (σ1 : World D) (v1 : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ1 v1) :
    semK O passes R (.ende (.cons (.call g args hp hr) rest)) σ ρ =
      semK O passes R (.ende rest) σ1 ρ := by
  simp only [semK, execEnd, execStmt, h]

/-- A bind-call, when the handler answers normally, binds the value. -/
theorem semK_bindCall {Λ Λ' : List (Res D)} {τ : Ty} (g : D.Fn)
    (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D V l (τ :: Γ) (nach D g Λ) Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (σ1 : World D) (v1 : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ1 v1) :
    semK O passes R (.dann (.bindCall g args he hp hr rest) k) σ ρ =
      semK O passes R (.dann rest (.schrumpf k)) σ1 (.cons (ergWert he v1) ρ) := by
  rw [semK_dann]
  simp only [execBlock, h]
  rw [nachK_schrumpf, semK_dann]

end RufSemK
/-- A leaf does not consult the call handler. -/
theorem istBlatt_R (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} (h : s.istBlatt = true)
    (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R s σ ρ = execStmt O passes keinRuf s σ ρ := by
  cases s <;> first | rfl | simp [Stmt.istBlatt] at h

/-- How the machine resumes a caller when the callee `g` returns `v`: the
    caller itself (it did not wait), or its waiting continuation with `v`
    bound (a `let x = g(…)`, with or without an else block). -/
inductive Wiederauf (g : D.Fn) (caller : RufRahmenG D) (v : ErgVal D (D.erg g)) :
    RufRahmenG D → Prop where
  | wie (hnw : caller.wartend = false) : Wiederauf g caller v caller
  | bind {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ)
      (hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩) (he : D.erg g = some τ) :
      Wiederauf g caller v ⟨caller.f, caller.rho, caller.s0,
        ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc, .dann restb (.schrumpf k)⟩⟩
  | bindSonst {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ)
      (hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩) (he : D.erg g = some τ) :
      Wiederauf g caller v ⟨caller.f, caller.rho, caller.s0,
        ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc, .dann restb (.schrumpf k)⟩⟩

/-- The frame a call leaves below its callee, and how the caller's frame
    result `S0` continues from the callee's normal answer: plainly (the
    caller advanced past the call), or with the answer bound (`wartet`). -/
def WarteK (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (A : D.Lock → Prop)
    (C : D.Fn → Prop) (T : RufRahmenG D) (g : D.Fn) (rhoG : Env D (D.params g))
    (σc : World D) (Fw : RufRahmenG D) (S0 : REnde (vertragVon D T.f)) : Prop :=
  (∃ (l' : Bool) (Γ' : Ctx) (Λ' : List (Res D)) (ρ' : Env D Γ')
      (rw : GRest D (vertragVon D T.f) l' Γ' Λ'),
      Fw = ⟨T.f, T.rho, T.s0, ⟨l', Γ', Λ', ρ', rw⟩⟩ ∧ rw.wartend = false ∧ RestK A C rw ∧
      ∀ σ1 v1, R g σc rhoG = .ok σ1 v1 → S0 = semK O passes R rw σ1 ρ') ∨
  (∃ (l' : Bool) (Γ' : Ctx) (Λ' Λ'' : List (Res D)) (τ : Ty) (ρ' : Env D Γ')
      (restb : Block D (vertragVon D T.f) l' (τ :: Γ') Λ' Λ'')
      (k : GRest D (vertragVon D T.f) l' Γ' Λ'') (he : D.erg g = some τ),
      Fw = ⟨T.f, T.rho, T.s0, ⟨l', Γ', Λ', ρ', .wartet restb k⟩⟩ ∧
      RestK A C (.dann restb (.schrumpf k)) ∧
      ∀ σ1 v1, R g σc rhoG = .ok σ1 v1 →
        S0 = semK O passes R (.dann restb (.schrumpf k)) σ1 (.cons (ergWert he v1) ρ'))

/-- What one step of thread `f` does to a covered top frame: it stays on
    top with a covered residue and the same frame result (up to the trace);
    or it pops, logging a `rueck` whose world and value ARE the frame result
    (up to the trace), and resumes the caller; or it pushes an admitted
    callee's fresh frame above the caller's waiting frame. -/
def ErhaltK (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (A : D.Lock → Prop)
    (C : D.Fn → Prop) (M M' : RufMaschineG D) (f : Faden) (z : RufFadenG D) {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ) (r : GRest D (vertragVon D z.kopf.f) l Γ Λ) :
    Prop :=
  (∃ (l' : Bool) (Γ' : Ctx) (Λ' : List (Res D)) (ρ' : Env D Γ')
      (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (sp : List (Ereignis D)),
      M'.faeden f = ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, sp, z.log⟩ ∧
      RestK A C r' ∧
      (semK O passes R r' (M'.weltVon f) ρ').gleich (semK O passes R r (M.weltVon f) ρ)) ∨
  (∃ (v : ErgVal D (D.erg z.kopf.f)) (s1 : World D) (caller neu : RufRahmenG D)
      (rst : List (RufRahmenG D)),
      z.stapel = caller :: rst ∧ Wiederauf z.kopf.f caller v neu ∧
      M'.faeden f = ⟨rst, neu, s1.spur,
        RufEreignisF.rueck z.kopf.f z.kopf.rho v z.kopf.s0 s1 :: z.log⟩ ∧
      M'.speicher = s1.speicher ∧
      (semK O passes R r (M.weltVon f) ρ).gleich (.zurueck s1 v)) ∨
  (∃ (g : D.Fn) (rhoG : Env D (D.params g)) (σc : World D) (Fw : RufRahmenG D),
      C g ∧
      M'.faeden f = ⟨Fw :: z.stapel, ⟨g, rhoG, σc, ⟨false, D.params g,
          Signatur.anfang D (D.signatur g), rhoG, .ende (P.rumpf g)⟩⟩, σc.spur,
        RufEreignisF.eintritt g rhoG σc :: z.log⟩ ∧
      M'.speicher = σc.speicher ∧
      WarteK O passes R A C z.kopf g rhoG σc Fw (semK O passes R r (M.weltVon f) ρ))

set_option hygiene false in
/-- Refute a step whose head shape the covered residue cannot have. -/
macro "widerlegeK" h:ident : tactic => `(tactic| (
  rw [hR] at $h:ident
  cases $h:ident
  first
  | exact absurd hcov.dann_cons_kOk (by simp [Stmt.kOk])
  | exact absurd hcov.ende_cons_kOk (by simp [Stmt.kOk])
  | exact absurd hcov.dann_kOk (by simp [Block.kOk])
  | exact absurd hcov.ende_kOk (by simp [Endblock.kOk])
  | cases hcov))


end Gabbro.Grammatik
