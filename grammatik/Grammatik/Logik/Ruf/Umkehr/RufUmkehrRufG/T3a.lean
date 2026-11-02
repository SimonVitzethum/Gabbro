/- Part 3 of 6 of `RufUmkehrRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufUmkehrRufG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T2
@[expose] public section


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

theorem semK_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option Ty)}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (τ : Ty) (b : Block D V l (τ :: Γ) Λ Λ') (nutz : Nutzlast D.Fn D.passt (some τ))
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some τ, b, nutz⟩) :
    semK O passes R (.dann b (.schrumpf (.dann rest k))) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semK O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact (semK_dann O passes R b _ _ _).trans (nachK_schrumpf O passes R _ _).symm

theorem semK_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option Ty)}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast D.Fn D.passt none)
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
  | _, _, .retScoped _ _ => rfl
  | _, _, .retWhyScoped _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, Block.kOk, Endblock.kOk, Endblock.kOk_alsBlock rest]
  | _, _, .bind _ rest => by
      simp only [Endblock.alsBlock, Block.kOk, Endblock.kOk, Endblock.kOk_alsBlock rest]
  | _, _, .bindCall _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.kOk, Endblock.kOk, Endblock.kOk_alsBlock rest]
  | _, _, .bindCallElse .. => rfl
  | _, _, .bindAxiom .. => rfl
  | _, _, .bindAxiomElse .. => rfl
  | _, _, .bindAxiomOpt .. => rfl
  | _, _, .bindAxiomOptElse .. => rfl

  | _, _, .regRead .. => rfl

  | _, _, .regReadElse .. => rfl

  | _, _, .awaits .. => rfl

  | _, _, .bindCallInd .. => rfl
  | _, _, .bindCallIndElse .. => rfl
  | _, _, .narrow _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.kOk, Endblock.kOk, Endblock.kOk_alsBlock rest]
  | _, _, .narrowRequired _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.kOk, Endblock.kOk, Endblock.kOk_alsBlock rest]
  | _, _, .exchange _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.kOk, Endblock.kOk, Endblock.kOk_alsBlock rest]
  | _, _, .ite _ t _ => by
      simp only [Endblock.alsBlock, Block.kOk, Endblock.kOk, Endblock.kOk_alsBlock t, Bool.and_comm]

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


end SemSchrittK
end Gabbro.Grammatik
