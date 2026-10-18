/- Part 3 of 4 of `ZielOrtVollSem` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrtVollSem.lean` imports all parts). -/
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Stufen

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semV_ende_cons {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.ende (.cons s rest)) σ ρ =
      weiterZ O passes R (.ende rest) (execStmt O passes R s σ ρ) := by
  show zErg (execEnd O passes R (.cons s rest) σ ρ) = _
  simp only [execEnd]
  cases execStmt O passes R s σ ρ <;> rfl

theorem laufA_nil {Λ : List (Res D)} (o : Ausgang V l Γ) :
    laufA (fun σ ρ => execBlock O passes R (.nil : Block D V l Γ Λ Λ) σ ρ) o = o := by
  cases o <;> rfl

theorem semV_endeEntf {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.ende (.cons s rest)) σ ρ =
      semV O passes R (.dann (.cons s .nil) (.ende rest)) σ ρ := by
  rw [semV_ende_cons, semV_dann_cons]
  show _ = weiterZ O passes R (.ende rest) (laufA _ _)
  rw [laufA_nil]

theorem semV_blatt {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
    (σ σ' : World D) (ρ ρ' : Env D Γ) (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    semV O passes R (.ende (.cons s rest)) σ ρ = semV O passes R (.ende rest) σ' ρ' := by
  rw [semV_ende_cons, h]
  rfl

theorem semV_dannBlatt {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ σ' : World D) (ρ ρ' : Env D Γ)
    (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    semV O passes R (.dann (.cons s rest) k) σ ρ = semV O passes R (.dann rest k) σ' ρ' := by
  rw [semV_dann_cons, h]
  rfl

theorem semV_dannLeer {Λ : List (Res D)} (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann .nil k) σ ρ = semV O passes R k σ ρ := rfl

theorem semV_ite {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) (b : Bool)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = b) :
    semV O passes R (.dann (.cons (.ite c t e) rest) k) σ ρ =
      semV O passes R (.dann (if b then t else e) (.dann rest k)) (σ.lese Λ c.orte) ρ := by
  rw [semV_dann_cons]
  cases b <;> simp only [execStmt, hw] <;> rfl

theorem semV_optSome {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (.index n))
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v) :
    semV O passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ =
      semV O passes R (.dann p (.schrumpf (.dann rest k))) (σ.lese Λ o.orte) (.cons v ρ) := by
  rw [semV_dann_cons]
  simp only [execStmt, hv]
  rfl

theorem semV_optNone {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none) :
    semV O passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ =
      semV O passes R (.dann a (.dann rest k)) (σ.lese Λ o.orte) ρ := by
  rw [semV_dann_cons]
  simp only [execStmt, hv]
  rfl

theorem semV_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (lo hi : Int) (b : Block D V l (.int lo hi :: Γ) Λ Λ') (nutz : Nutzlast (some (lo, hi)))
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some (lo, hi), b, nutz⟩) :
    semV O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ =
      semV O passes R (.dann b (.schrumpf (.dann rest k))) (σ.lese Λ v.orte) (armEnv nutz ρ) := by
  rw [semV_dann_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  rfl

theorem semV_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast none)
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    semV O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ =
      semV O passes R (.dann b (.dann rest k)) (σ.lese Λ v.orte) (armEnv nutz ρ) := by
  rw [semV_dann_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  rfl

theorem semV_grund {Λ Λ' Λ'' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.why n))
    (arms : GrundArms D V l Γ Λ Λ' n) (rest : Block D V l Γ Λ' Λ'')
    (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.onWhy r arms) rest) k) σ ρ =
      semV O passes R (.dann (grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ))
        (.dann rest k)) (σ.lese Λ r.orte) ρ := by
  rw [semV_dann_cons]
  simp only [execStmt]
  rw [execGrund_wahlW O passes R arms]
  rfl

theorem semV_breaking {Λ Λ' Λ'' : List (Res D)} (i : D.Inv) (body : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.breaking i body) rest) k) σ ρ =
      semV O passes R (.dann body (.dann rest k)) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_locks {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.locks L hr body) rest) k) σ ρ =
      semV O passes R (.dann body (.frei L (.dann rest k))) (σ.nimmt L) ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_frei {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) : semV O passes R (.frei L k) σ ρ = semV O passes R k (σ.gibt L) ρ := rfl

theorem semV_schrumpf {Λ : List (Res D)} {τ : Ty} (k : GRest D V l Γ Λ) (σ : World D)
    (v : Wert D τ) (ρ : Env D Γ) :
    semV O passes R (.schrumpf k) σ (.cons v ρ) = semV O passes R k σ ρ := rfl

theorem semV_endeBind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Endblock D V l (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.ende (.bind e rest)) σ ρ =
      semV O passes R (.ende rest) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := by
  show zErg (execEnd O passes R (.bind e rest) σ ρ) = zErg (execEnd O passes R rest _ _)
  simp only [execEnd]
  rw [zErg_schrumpf]

theorem semV_dannBind {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.bind e rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := rfl

theorem semV_narrowOk {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    semV O passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ) := by
  rw [semV_dann, execBlock_narrowK]
  unfold narrowWeiterK
  rw [dif_pos h]
  rfl

theorem semV_narrowElse {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    (semV O passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ).folgt
      (semV O passes R (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ e.orte) ρ) := by
  rw [semV_dann, execBlock_narrowK]
  unfold narrowWeiterK
  rw [dif_neg h]
  rw [semV_alsBlock]
  exact ZErg.folgt_refl _

theorem semV_pruefWahr {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semV O passes R (.dann (.check c sonst rest) k) σ ρ =
      semV O passes R (.dann rest k) (σ.lese Λ c.orte) ρ := by
  rw [semV_dann]
  simp only [execBlock, hw, if_true]
  rfl

theorem semV_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    (semV O passes R (.dann (.check c sonst rest) k) σ ρ).folgt
      (semV O passes R (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ c.orte) ρ) := by
  rw [semV_dann]
  simp only [execBlock, hw, Bool.false_eq_true, if_false]
  rw [semV_alsBlock]
  exact ZErg.folgt_refl _

theorem semV_exchange {Λ Λ' : List (Res D)} (g : D.Glob)
    (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
    (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.exchange g neuE hw hL rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k))
        ((σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
            (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ)))
        (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ) := rfl

theorem semV_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semV O passes R (.dann (.float op a b lo hi rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv]
  rfl

theorem semV_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semV O passes R (.dann (.floatLit q lo hi rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv]
  rfl

theorem semV_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semV O passes R (.dann (.floatOf e lo hi rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv]
  rfl

theorem semV_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semV O passes R (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv]
  rfl

theorem semV_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    (semV O passes R (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ).folgt
      (semV O passes R (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ e.orte) ρ) := by
  rw [semV_dann]
  simp only [execBlock, hn]
  rw [semV_alsBlock]
  exact ZErg.folgt_refl _

/-! ### Loops -/

theorem semV_dannTrav {Λ Λ'' : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.traverse t inv body) rest) k) σ ρ =
      semV O passes R (.trav t inv body (alleIndizes (D.count t)) (.dann rest k)) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_travNext {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (i : Wert D (.index (D.count t))) (is : List (Wert D (.index (D.count t))))
    (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semV O passes R (.trav t inv body (i :: is) k) σ ρ =
      semV O passes R (.dann body (.travRest t inv body is k)) (σ.lese Λ inv.orte) (.cons i ρ) := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterZ O passes R k (traverseLauf _ _ (i :: is) σ ρ) =
    weiterZ O passes R (.travRest t inv body is k)
      (execBlock O passes R body (leseB inv σ ρ).1 (.cons i ρ))
  simp only [traverseLauf, hl, Bool.true_eq_false, if_false]
  cases execBlock O passes R body (leseB inv σ ρ).1 (.cons i ρ) <;> rfl

theorem semV_travFort {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.travRest t inv body is k) σ (.cons i ρ) =
      semV O passes R (.trav t inv body is k) σ ρ := rfl

theorem semV_travDone {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semV O passes R (.trav t inv body [] k) σ ρ = semV O passes R k (σ.lese Λ inv.orte) ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterZ O passes R k (traverseLauf (fun σ ρ => execBlock O passes R body σ ρ)
    (leseB inv) [] σ ρ) = weiterZ O passes R k (.ok _ ρ)
  simp only [traverseLauf, hl, if_true]
  rfl

theorem semV_dannRetry {Λ Λ'' : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.retry n bis body ueber) rest) k) σ ρ =
      semV O passes R (.wieder n bis body ueber (.dann rest k)) σ ρ := by
  rw [semV_dann_cons]
  rfl

/-- A block `.nil` in front of a residue changes nothing. -/
theorem weiterZ_dannLeer {Λ : List (Res D)} (k : GRest D V l Γ Λ) (o : Ausgang V l Γ) :
    weiterZ O passes R (.dann .nil k) o = weiterZ O passes R k o := by
  cases o <;> rfl

/-- The spent `retry` (corrected 2026-09-13): `if bis {} else { overflow }`. -/
theorem semV_wiederUeber {Λ : List (Res D)} (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.wieder 0 bis body ueber k) σ ρ =
      semV O passes R (.dann (.cons (.ite bis .nil ueber) .nil) k) σ ρ := by
  cases hb : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) with
  | true =>
      rw [semV_ite O passes R bis .nil ueber .nil k σ ρ true hb]
      show weiterZ O passes R k (retryLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB bis)
        (fun σ ρ => execBlock O passes R ueber σ ρ) 0 σ ρ) = _
      have hl : (leseB bis σ ρ).2 = true := hb
      simp only [retryLauf, hl, if_true]
      rfl
  | false =>
      rw [semV_ite O passes R bis .nil ueber .nil k σ ρ false hb]
      show weiterZ O passes R k (retryLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB bis)
        (fun σ ρ => execBlock O passes R ueber σ ρ) 0 σ ρ) = _
      have hl : (leseB bis σ ρ).2 = false := hb
      simp only [retryLauf, hl, Bool.false_eq_true, if_false]
      show _ = weiterZ O passes R (.dann .nil k) (execBlock O passes R ueber (leseB bis σ ρ).1 ρ)
      rw [weiterZ_dannLeer]

theorem semV_wiederWeiter {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true) :
    semV O passes R (.wieder (n + 1) bis body ueber k) σ ρ =
      semV O passes R k (σ.lese Λ bis.orte) ρ := by
  have hl : (leseB bis σ ρ).2 = true := hw
  show weiterZ O passes R k (retryLauf _ _ _ (n + 1) σ ρ) = weiterZ O passes R k (.ok _ ρ)
  simp only [retryLauf, hl, if_true]
  rfl

theorem semV_wiederSchritt {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false) :
    semV O passes R (.wieder (n + 1) bis body ueber k) σ ρ =
      semV O passes R (.dann body (.wiederRest n bis body ueber k)) (σ.lese Λ bis.orte) ρ := by
  have hl : (leseB bis σ ρ).2 = false := hw
  show weiterZ O passes R k (retryLauf _ _ _ (n + 1) σ ρ) =
    weiterZ O passes R (.wiederRest n bis body ueber k)
      (execBlock O passes R body (leseB bis σ ρ).1 ρ)
  simp only [retryLauf, hl, Bool.false_eq_true, if_false]
  cases execBlock O passes R body (leseB bis σ ρ).1 ρ <;> rfl

theorem semV_wiederFort {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.wiederRest n bis body ueber k) σ ρ =
      semV O passes R (.wieder n bis body ueber k) σ ρ := rfl

theorem semV_dannForever {Λ Λ'' : List (Res D)} (a : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.forever a inv body) rest) k) σ ρ =
      semV O passes R (.ewig a passes inv body (.dann rest k)) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_ewigWeiter {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semV O passes R (.ewig a (n + 1) inv body k) σ ρ =
      semV O passes R (.dann body (.ewigRest a n inv body k)) (σ.lese Λ inv.orte) ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterZ O passes R k (foreverLauf a _ _ (n + 1) σ ρ) =
    weiterZ O passes R (.ewigRest a n inv body k)
      (execBlock O passes R body (leseB inv σ ρ).1 ρ)
  simp only [foreverLauf, hl, Bool.true_eq_false, if_false]
  cases execBlock O passes R body (leseB inv σ ρ).1 ρ <;> rfl

theorem semV_ewigFort {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.ewigRest a n inv body k) σ ρ =
      semV O passes R (.ewig a n inv body k) σ ρ := rfl

/-! ### The exits `leave` and `next` -/

theorem semV_leaveTrav {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semV O passes R (.dann (.cons (.leave h) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      semV O passes R k (σ.lese Λ inv.orte) ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  rw [semV_dann_cons]
  show weiterZ O passes R k (if (leseB inv σ ρ).2 = true then _ else _) = _
  rw [if_pos hl]
  rfl

theorem semV_nextTrav {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semV O passes R (.dann (.cons (.next h) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      semV O passes R (.trav t inv body is k) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_leaveWieder {Λ Λx : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semV O passes R (.dann (.cons (.leave h) rest) (.wiederRest n bis body ueber k)) σ ρ =
      semV O passes R k σ ρ := by
  rw [semV_dann_cons]
  rfl

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
