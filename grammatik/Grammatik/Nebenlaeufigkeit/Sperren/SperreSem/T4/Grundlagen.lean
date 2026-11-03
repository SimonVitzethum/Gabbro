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

end Stufen
end Gabbro.Grammatik
