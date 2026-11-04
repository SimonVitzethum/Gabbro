/- Part 9 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T8
@[expose] public section


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

theorem sem_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option Ty)}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (τ : Ty) (b : Block D V l (τ :: Γ) Λ Λ') (nutz : Nutzlast D.Fn D.passt (some τ))
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some τ, b, nutz⟩) :
    semR O passes (.dann b (.schrumpf (.dann rest k))) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semR O passes (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semR_dann O passes (.cons _ rest), nachA_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact (semR_dann O passes b _ _ _).trans (nachA_schrumpf O passes _ _).symm

theorem sem_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option Ty)}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast D.Fn D.passt none)
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
  | _, _, .retScoped _ _ => rfl
  | _, _, .retWhyScoped _ _ => rfl
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
  | _, _, .bindCallElse _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
  | _, _, .bindAxiom .. => rfl
  | _, _, .bindAxiomElse .. => rfl
  | _, _, .bindAxiomOpt .. => rfl
  | _, _, .bindAxiomOptElse .. => rfl
  | _, _, .regRead .. => rfl
  | _, _, .regReadElse .. => rfl
  | _, _, .awaits .. => rfl
  | _, _, .bindCallInd _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
  | _, _, .bindCallIndElse _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
  | _, _, .narrow _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
  | _, _, .narrowRequired _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
  | _, _, .exchange _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
  | _, _, .ite _ t _ => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock t, Bool.and_comm]

  | _, _, .float op a b lo hi rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
  | _, _, .floatLit q lo hi rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
  | _, _, .floatOf e lo hi rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
  | _, _, .floatNarrow e lo hi sonst rest => by
      simp only [Endblock.alsBlock, Block.ohneOrakel, Endblock.ohneOrakel,
        Endblock.ohneOrakel_alsBlock rest]
/-- A covered end block run as a block is a covered block. -/
theorem EndG.alsBlock {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {e : Endblock D V l Γ Λ},
      EndG A e → BlockG A true e.alsBlock.2
  | _, _, _, _, .ret e hΛ => .cons _ _ (.ret e hΛ) .nil
  | _, _, _, _, .cons s _ hs hr => .cons s _ hs (EndG.alsBlock hr)
  | _, _, _, _, .bind e _ hr => .bind e _ (EndG.alsBlock hr)

  | _, _, _, _, .float op a b lo hi _ hr => .float op a b lo hi _ (EndG.alsBlock hr)

  | _, _, _, _, .floatLit q lo hi _ hr => .floatLit q lo hi _ (EndG.alsBlock hr)

  | _, _, _, _, .floatOf e lo hi _ hr => .floatOf e lo hi _ (EndG.alsBlock hr)

  | _, _, _, _, .floatNarrow e lo hi sonst _ hs hr => .floatNarrow e lo hi sonst _ hs (EndG.alsBlock hr)


/-- An end block run as a block in front of any continuation means the end
    block (it never ends normally). -/
theorem semR_alsBlock {Λ Λk : List (Res D)} (e : Endblock D V l Γ Λ)
    (k : GRest D V l Γ Λk) (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann e.alsBlock.2 (.abbruch k)) σ ρ = semR O passes (.ende e) σ ρ := by
  rw [semR_dann, Endblock.execBlock_alsBlock, nachA_zuAusgang]
  rfl

end SemSchritt
end Gabbro.Grammatik
