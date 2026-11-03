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

end Stufen
end Gabbro.Grammatik
