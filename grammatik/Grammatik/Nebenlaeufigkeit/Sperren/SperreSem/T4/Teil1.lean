module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T3

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

section Stufen

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semH_ende_cons {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.ende (.cons s rest)) σ ρ =
      weiterH S O U passes R (.ende rest) (execStmtH S O U passes R s σ ρ) := by
  show zErgG (execEndH S O U passes R (.cons s rest) σ ρ) = _
  simp only [execEndH]
  cases execStmtH S O U passes R s σ ρ <;> rfl

theorem laufAH_nil {Λ : List (Res D)} (o : Ausgang V l Γ) :
    laufA (fun σ ρ => execBlockH S O U passes R (.nil : Block D V l Γ Λ Λ) σ ρ) o = o := by
  cases o <;> rfl

theorem semH_endeEntf {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.ende (.cons s rest)) σ ρ =
      semH S O U passes R (.dann (.cons s .nil) (.ende rest)) σ ρ := by
  rw [semH_ende_cons, semH_dann_cons]
  show _ = weiterH S O U passes R (.ende rest) (laufA _ _)
  rw [laufAH_nil]

theorem semH_dannLeer {Λ : List (Res D)} (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann .nil k) σ ρ = semH S O U passes R k σ ρ := by rfl

theorem semH_ite {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) (b : Bool)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = b) :
    semH S O U passes R (.dann (.cons (.ite c t e) rest) k) σ ρ =
      semH S O U passes R (.dann (if b then t else e) (.dann rest k)) (σ.lese Λ c.orte) ρ := by
  rw [semH_dann_cons]
  cases b <;> simp only [execStmtH, hw] <;> rfl

theorem semH_optSome {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (.index n))
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v) :
    semH S O U passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ =
      semH S O U passes R (.dann p (.schrumpf (.dann rest k))) (σ.lese Λ o.orte) (.cons v ρ) := by
  rw [semH_dann_cons]
  simp only [execStmtH, hv]
  rfl

theorem semH_optNone {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none) :
    semH S O U passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ =
      semH S O U passes R (.dann a (.dann rest k)) (σ.lese Λ o.orte) ρ := by
  rw [semH_dann_cons]
  simp only [execStmtH, hv]
  rfl

theorem semH_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option Ty)}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (τ : Ty) (b : Block D V l (τ :: Γ) Λ Λ') (nutz : Nutzlast D.Fn D.passt (some τ))
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some τ, b, nutz⟩) :
    semH S O U passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ =
      semH S O U passes R (.dann b (.schrumpf (.dann rest k))) (σ.lese Λ v.orte)
        (armEnv nutz ρ) := by
  rw [semH_dann_cons]
  simp only [execStmtH]
  rw [execArmsH_wahl, hw]
  rfl

theorem semH_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option Ty)}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast D.Fn D.passt none)
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    semH S O U passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ =
      semH S O U passes R (.dann b (.dann rest k)) (σ.lese Λ v.orte) (armEnv nutz ρ) := by
  rw [semH_dann_cons]
  simp only [execStmtH]
  rw [execArmsH_wahl, hw]
  rfl

theorem semH_grund {Λ Λ' Λ'' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.why n))
    (arms : GrundArms D V l Γ Λ Λ' n) (rest : Block D V l Γ Λ' Λ'')
    (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.onWhy r arms) rest) k) σ ρ =
      semH S O U passes R (.dann (grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ))
        (.dann rest k)) (σ.lese Λ r.orte) ρ := by
  rw [semH_dann_cons]
  simp only [execStmtH]
  rw [execGrundH_wahlW S O U passes R arms]
  rfl

theorem semH_breaking {Λ Λ' Λ'' : List (Res D)} (i : D.Inv) (body : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.breaking i body) rest) k) σ ρ =
      semH S O U passes R (.dann body (.dann rest k)) σ ρ := by
  rw [semH_dann_cons]
  rfl

/-- **The acquire**: the body runs from the environment's move of the
    acquire world, and the release marker `frei L` carries the release
    check. -/
theorem semH_locks {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.locks L hr body) rest) k) σ ρ =
      semH S O U passes R (.dann body (.frei L (.dann rest k))) ((U L σ).nimmt L) ρ := by
  rw [semH_dann_cons]
  rfl

/-- **The release**, where the invariant holds. -/
theorem semH_frei {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) (hi : S.inv L σ.speicher = true) :
    semH S O U passes R (.frei L k) σ ρ = semH S O U passes R k (σ.gibt L) ρ := by
  show weiterH S O U passes R k (freiH S L (.ok σ ρ)) = _
  simp only [freiH, hi, if_true]
  rfl

/-- **A release where the invariant fails predicts `logik schleife`.** -/
theorem semH_frei_falsch {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) (hi : S.inv L σ.speicher = false) :
    semH S O U passes R (.frei L k) σ ρ = .logik .schleife := by
  show weiterH S O U passes R k (freiH S L (.ok σ ρ)) = _
  simp only [freiH, hi, Bool.false_eq_true, if_false]
  exact weiterH_logik S O U passes R k _

theorem semH_schrumpf {Λ : List (Res D)} {τ : Ty} (k : GRest D V l Γ Λ) (σ : World D)
    (v : Wert D τ) (ρ : Env D Γ) :
    semH S O U passes R (.schrumpf k) σ (.cons v ρ) = semH S O U passes R k σ ρ := by rfl

theorem semH_endeBind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Endblock D V l (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.ende (.bind e rest)) σ ρ =
      semH S O U passes R (.ende rest) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := by
  show zErgG (execEndH S O U passes R (.bind e rest) σ ρ) =
    zErgG (execEndH S O U passes R rest _ _)
  simp only [execEndH]
  rw [zErgG_schrumpf]

theorem semH_dannBind {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.bind e rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := by rfl

theorem semH_narrowOk {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    semH S O U passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ) := by
  rw [semH_dann]
  simp only [execBlockH, dif_pos h]
  rfl

theorem semH_narrowElse {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    (semH S O U passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ).folgt
      (semH S O U passes R (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ e.orte) ρ) := by
  rw [semH_dann]
  simp only [execBlockH, dif_neg h]
  rw [semH_alsBlock]
  exact ZErgG.folgt_refl _

theorem semH_pruefWahr {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semH S O U passes R (.dann (.check c sonst rest) k) σ ρ =
      semH S O U passes R (.dann rest k) (σ.lese Λ c.orte) ρ := by
  rw [semH_dann]
  simp only [execBlockH, hw, if_true]
  rfl

theorem semH_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    (semH S O U passes R (.dann (.check c sonst rest) k) σ ρ).folgt
      (semH S O U passes R (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ c.orte) ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hw, Bool.false_eq_true, if_false]
  rw [semH_alsBlock]
  exact ZErgG.folgt_refl _

theorem semH_exchange {Λ Λ' : List (Res D)} (g : D.Glob)
    (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
    (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.exchange g neuE hw hL rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k))
        ((σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
            (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ)))
        (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ) := by rfl

theorem semH_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semH S O U passes R (.dann (.float op a b lo hi rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv]
  rfl

theorem semH_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semH S O U passes R (.dann (.floatLit q lo hi rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv]
  rfl

theorem semH_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semH S O U passes R (.dann (.floatOf e lo hi rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv]
  rfl

theorem semH_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semH S O U passes R (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv]
  rfl

theorem semH_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    (semH S O U passes R (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ).folgt
      (semH S O U passes R (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ e.orte) ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hn]
  rw [semH_alsBlock]
  exact ZErgG.folgt_refl _

/-! ### Loops -/

theorem semH_dannTrav {Λ Λ'' : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.traverse t inv body) rest) k) σ ρ =
      semH S O U passes R (.trav t inv body (alleIndizes (D.count t)) (.dann rest k)) σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_travNext {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (i : Wert D (.index (D.count t))) (is : List (Wert D (.index (D.count t))))
    (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semH S O U passes R (.trav t inv body (i :: is) k) σ ρ =
      semH S O U passes R (.dann body (.travRest t inv body is k)) (σ.lese Λ inv.orte)
        (.cons i ρ) := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterH S O U passes R k (traverseLauf _ _ (i :: is) σ ρ) =
    weiterH S O U passes R (.travRest t inv body is k)
      (execBlockH S O U passes R body (leseB inv σ ρ).1 (.cons i ρ))
  simp only [traverseLauf, hl, Bool.true_eq_false, if_false]
  cases execBlockH S O U passes R body (leseB inv σ ρ).1 (.cons i ρ) <;> rfl

theorem semH_travFort {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.travRest t inv body is k) σ (.cons i ρ) =
      semH S O U passes R (.trav t inv body is k) σ ρ := by rfl

theorem semH_travDone {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semH S O U passes R (.trav t inv body [] k) σ ρ =
      semH S O U passes R k (σ.lese Λ inv.orte) ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterH S O U passes R k (traverseLauf (fun σ ρ => execBlockH S O U passes R body σ ρ)
    (leseB inv) [] σ ρ) = weiterH S O U passes R k (.ok _ ρ)
  simp only [traverseLauf, hl, if_true]
  rfl

theorem semH_dannRetry {Λ Λ'' : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.retry n bis body ueber) rest) k) σ ρ =
      semH S O U passes R (.wieder n bis body ueber (.dann rest k)) σ ρ := by
  rw [semH_dann_cons]
  rfl

/-- A block `.nil` in front of a residue changes nothing. -/
theorem weiterH_dannLeer {Λ : List (Res D)} (k : GRest D V l Γ Λ) (o : Ausgang V l Γ) :
    weiterH S O U passes R (.dann .nil k) o = weiterH S O U passes R k o := by
  cases o <;> rfl

/-- The spent `retry` (corrected 2026-09-13): `if bis {} else { overflow }`. -/
theorem semH_wiederUeber {Λ : List (Res D)} (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.wieder 0 bis body ueber k) σ ρ =
      semH S O U passes R (.dann (.cons (.ite bis .nil ueber) .nil) k) σ ρ := by
  cases hb : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) with
  | true =>
      rw [semH_ite S O U passes R bis .nil ueber .nil k σ ρ true hb]
      show weiterH S O U passes R k (retryLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB bis)
        (fun σ ρ => execBlockH S O U passes R ueber σ ρ) 0 σ ρ) = _
      have hl : (leseB bis σ ρ).2 = true := hb
      simp only [retryLauf, hl, if_true]
      rfl
  | false =>
      rw [semH_ite S O U passes R bis .nil ueber .nil k σ ρ false hb]
      show weiterH S O U passes R k (retryLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB bis)
        (fun σ ρ => execBlockH S O U passes R ueber σ ρ) 0 σ ρ) = _
      have hl : (leseB bis σ ρ).2 = false := hb
      simp only [retryLauf, hl, Bool.false_eq_true, if_false]
      show _ = weiterH S O U passes R (.dann .nil k) (execBlockH S O U passes R ueber (leseB bis σ ρ).1 ρ)
      rw [weiterH_dannLeer]

theorem semH_wiederWeiter {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true) :
    semH S O U passes R (.wieder (n + 1) bis body ueber k) σ ρ =
      semH S O U passes R k (σ.lese Λ bis.orte) ρ := by
  have hl : (leseB bis σ ρ).2 = true := hw
  show weiterH S O U passes R k (retryLauf _ _ _ (n + 1) σ ρ) =
    weiterH S O U passes R k (.ok _ ρ)
  simp only [retryLauf, hl, if_true]
  rfl

theorem semH_wiederSchritt {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false) :
    semH S O U passes R (.wieder (n + 1) bis body ueber k) σ ρ =
      semH S O U passes R (.dann body (.wiederRest n bis body ueber k)) (σ.lese Λ bis.orte) ρ := by
  have hl : (leseB bis σ ρ).2 = false := hw
  show weiterH S O U passes R k (retryLauf _ _ _ (n + 1) σ ρ) =
    weiterH S O U passes R (.wiederRest n bis body ueber k)
      (execBlockH S O U passes R body (leseB bis σ ρ).1 ρ)
  simp only [retryLauf, hl, Bool.false_eq_true, if_false]
  cases execBlockH S O U passes R body (leseB bis σ ρ).1 ρ <;> rfl

theorem semH_wiederFort {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.wiederRest n bis body ueber k) σ ρ =
      semH S O U passes R (.wieder n bis body ueber k) σ ρ := by rfl

theorem semH_dannForever {Λ Λ'' : List (Res D)} (a : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.forever a inv body) rest) k) σ ρ =
      semH S O U passes R (.ewig a passes inv body (.dann rest k)) σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_ewigWeiter {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semH S O U passes R (.ewig a (n + 1) inv body k) σ ρ =
      semH S O U passes R (.dann body (.ewigRest a n inv body k)) (σ.lese Λ inv.orte) ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterH S O U passes R k (foreverLauf a _ _ (n + 1) σ ρ) =
    weiterH S O U passes R (.ewigRest a n inv body k)
      (execBlockH S O U passes R body (leseB inv σ ρ).1 ρ)
  simp only [foreverLauf, hl, Bool.true_eq_false, if_false]
  cases execBlockH S O U passes R body (leseB inv σ ρ).1 ρ <;> rfl

theorem semH_ewigFort {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.ewigRest a n inv body k) σ ρ =
      semH S O U passes R (.ewig a n inv body k) σ ρ := by rfl

/-! ### The exits `leave` and `next` -/

theorem semH_leaveTrav {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semH S O U passes R (.dann (.cons (.leave h) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      semH S O U passes R k (σ.lese Λ inv.orte) ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  rw [semH_dann_cons]
  show weiterH S O U passes R k (if (leseB inv σ ρ).2 = true then _ else _) = _
  rw [if_pos hl]
  rfl

theorem semH_nextTrav {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semH S O U passes R (.dann (.cons (.next h) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      semH S O U passes R (.trav t inv body is k) σ ρ := by
  rw [semH_dann_cons]
  rfl

/-! ### Consuming runs -/

theorem semH_dannVerbrauch {Λ Λ'' : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.consumeTraverse t member edge inv bound mass body) rest) k) σ ρ =
      semH S O U passes R (.verbrauch t member edge inv bound mass body
        ((D.count t).toNat + bound.toNat + 1) (.dann rest k)) σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_verbrauchWeiter {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true)
    (σ₂ : World D) (v : Wert D (.index (D.count t))) (b : Bool) (m : Int)
    (hsel : verbrauchSel t member edge (leseB inv σ ρ).1 ρ = (σ₂, some v, b))
    (hm : (eval (σ₂.lese Λ mass.orte) mass (σ₂.lese Λ mass.orte) ρ).n = m) :
    semH S O U passes R (.verbrauch t member edge inv bound mass body (rest + 1) k) σ ρ =
      semH S O U passes R (.dann body
        (.verbrauchRest t member edge inv bound mass body rest m k))
        (σ₂.lese Λ mass.orte) (.cons v ρ) := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterH S O U passes R k (verbrauchLauf _ _ (rest + 1) σ ρ) =
    weiterH S O U passes R (.verbrauchRest t member edge inv bound mass body rest m k)
      (execBlockH S O U passes R body (σ₂.lese Λ mass.orte) (.cons v ρ))
  simp only [verbrauchLauf, hl, Bool.true_eq_false, if_false, hsel]
  cases execBlockH S O U passes R body (σ₂.lese Λ mass.orte) (.cons v ρ) with
  | ok σ' ρ' =>
      by_cases hfall : 0 ≤ (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n ∧
          (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n ≤ bound ∧
          (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n < m
      · simp only [hfall, if_true]
      · simp only [hfall, if_false]
  | next _ σ' ρ' =>
      by_cases hfall : 0 ≤ (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n ∧
          (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n ≤ bound ∧
          (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n < m
      · simp only [hfall, if_true]
      · simp only [hfall, if_false]
  | leave _ σ' ρ' =>
      by_cases hfall : 0 ≤ (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n ∧
          (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n ≤ bound ∧
          (eval (σ'.lese Λ mass.orte) mass (σ'.lese Λ mass.orte) ρ'.tail).n < m
      · simp only [hfall, if_true]
        by_cases hc' : (leseB inv (σ'.lese Λ mass.orte) ρ'.tail).2 = true
        · simp only [hc', if_true]
        · simp only [show (leseB inv (σ'.lese Λ mass.orte) ρ'.tail).2 = false from by
            cases h' : (leseB inv (σ'.lese Λ mass.orte) ρ'.tail).2 with
            | false => rfl
            | true => exact absurd h' hc', if_false]
      · simp only [hfall, if_false]
  | zurueck σ' v => rfl
  | why σ' r => rfl
  | logik e => rfl
  | hardware e => rfl

theorem semH_verbrauchLeer {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true)
    (σ₂ : World D)
    (hsel : verbrauchSel t member edge (leseB inv σ ρ).1 ρ = (σ₂, none, false)) :
    semH S O U passes R (.verbrauch t member edge inv bound mass body (rest + 1) k) σ ρ =
      semH S O U passes R k σ₂ ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterH S O U passes R k (verbrauchLauf _ _ (rest + 1) σ ρ) =
    weiterH S O U passes R k (.ok σ₂ ρ)
  simp only [verbrauchLauf, hl, hsel, Bool.true_eq_false, if_false]

theorem semH_verbrauchFort {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (vor : Int) (k : GRest D V l Γ Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ)
    (σ₁ : World D) (hs₁ : σ₁ = σ.lese Λ mass.orte)
    (m' : Int) (hm' : (eval σ₁ mass σ₁ ρ).n = m')
    (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor) :
    semH S O U passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      σ (.cons i ρ) =
      semH S O U passes R (.verbrauch t member edge inv bound mass body rest k) σ₁ ρ := by
  show weiterH S O U passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      (.ok σ (.cons i ρ)) =
    weiterH S O U passes R (.verbrauch t member edge inv bound mass body rest k) (.ok σ₁ ρ)
  simp only [weiterH, hs₁, hm', hfall, if_true, laufA]

theorem semH_leaveVerbrauch {Λ Λx : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (vor : Int) (k : GRest D V l Γ Λ)
    (restb : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true)
    (σm : World D) (hsm : σm = σ.lese Λ mass.orte)
    (m' : Int) (hm' : (eval σm mass σm ρ).n = m')
    (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor)
    (hw : wahr? (eval (σm.lese Λ inv.orte) inv (σm.lese Λ inv.orte) ρ) = true) :
    semH S O U passes R (.dann (.cons (.leave h) restb)
      (.verbrauchRest t member edge inv bound mass body rest vor k)) σ (.cons i ρ) =
      semH S O U passes R k ((σm.lese Λ inv.orte)) ρ := by
  rw [semH_dann_cons]
  show weiterH S O U passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      (.leave h σ (.cons i ρ)) = _
  simp only [weiterH, hsm, hm', hfall, if_true]
  have hl : (leseB inv σm ρ).2 = true := hw
  simp only [hl, if_true]

theorem semH_nextVerbrauch {Λ Λx : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (vor : Int) (k : GRest D V l Γ Λ)
    (restb : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true)
    (σm : World D) (hsm : σm = σ.lese Λ mass.orte)
    (m' : Int) (hm' : (eval σm mass σm ρ).n = m')
    (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor) :
    semH S O U passes R (.dann (.cons (.next h) restb)
      (.verbrauchRest t member edge inv bound mass body rest vor k)) σ (.cons i ρ) =
      semH S O U passes R (.verbrauch t member edge inv bound mass body rest k) σm ρ := by
  rw [semH_dann_cons]
  show weiterH S O U passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      (.next h σ (.cons i ρ)) = _
  simp only [weiterH, hsm, hm', hfall, if_true, laufA]

theorem semH_leaveWieder {Λ Λx : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semH S O U passes R (.dann (.cons (.leave h) rest) (.wiederRest n bis body ueber k)) σ ρ =
      semH S O U passes R k σ ρ := by
  rw [semH_dann_cons]
  rfl

end Stufen
end Gabbro.Grammatik
