module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T1
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Schritte
variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem w_dannBind {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (rest : Block D (vertragVon D z.kopf.f) l (τ :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bind e rest) k⟩)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (.cons (eval ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ) ρ)
        (.dann rest (.schrumpf k)) ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannBind M f l Γ Λ Λ' Λ' τ e rest k ρ hhead _ rfl _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_narrowOk {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int}
    (lo' hi' : Int) (e : Expr D Γ Λ (.int lo hi))
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.narrow e lo' hi' sonst rest) k⟩)
    {σ : World D} (hW : M.weltVon f = σ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ)
        (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) := by
  subst hz
  subst hW
  exact ⟨_, RufSchrittG.dannNarrowOk M f l Γ Λ Λ' Λ' lo hi lo' hi' e sonst rest k ρ hhead
    _ rfl h _ rfl hΛ, zustandG_neu rfl rfl⟩

theorem w_narrowRequired {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int}
    (lo' hi' : Int) (e : Expr D Γ Λ (.int lo hi))
    (rest : Block D (vertragVon D z.kopf.f) l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.narrowRequired e lo' hi' rest) k⟩)
    {σ : World D} (hW : M.weltVon f = σ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ)
        (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) := by
  subst hz
  subst hW
  exact ⟨_, RufSchrittG.dannNarrowRequired M f l Γ Λ Λ' lo hi lo' hi' e rest k ρ hhead
    _ rfl h _ rfl hΛ, zustandG_neu rfl rfl⟩

theorem w_narrowElse {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int}
    (lo' hi' : Int) (e : Expr D Γ Λ (.int lo hi))
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.narrow e lo' hi' sonst rest) k⟩)
    (h : ¬ (lo' ≤ (eval ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ).n ∧
      (eval ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ).n ≤ hi'))
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann sonst.alsBlock.2 (.abbruch k)) ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannNarrowElse M f l Γ Λ Λ' Λ' lo hi lo' hi' e sonst rest k ρ hhead
    _ rfl h _ rfl hΛ, zustandG_neu rfl rfl⟩

theorem w_pruefWahr {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (c : Expr D Γ Λ .bool) (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.check c sonst rest) k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ c.orte) c ((M.weltVon f).lese Λ c.orte) ρ)
      = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ (.dann rest k)
        ((M.weltVon f).lese Λ c.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannPruefWahr M f l Γ Λ Λ' Λ' c sonst rest k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_pruefFalsch {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (c : Expr D Γ Λ .bool) (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.check c sonst rest) k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ c.orte) c ((M.weltVon f).lese Λ c.orte) ρ)
      = false)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann sonst.alsBlock.2 (.abbruch k))
        ((M.weltVon f).lese Λ c.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannPruefFalsch M f l Γ Λ Λ' Λ' c sonst rest k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_regLies {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (rest : Block D (vertragVon D z.kopf.f) l (D.rtyp r :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.regRead r hk rest) k⟩)
    (v : Wert D (D.rtyp r))
    (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon f).fragt (.inr (.inl r)))) = some v)
    (hzs : D.rzusage r v = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann rest (.schrumpf k)) ((M.weltVon f).fragt (.inr (.inl r))) := by
  subst hz
  exact ⟨_, RufSchrittG.dannRegLies M f l Γ Λ Λ' r hk rest k ρ hhead v hv hzs hΛ,
    zustandG_neu rfl rfl⟩

theorem w_regLiesElseWahr {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool)
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (D.rtyp r :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.regReadElse r hk zusage sonst rest) k⟩)
    (v : Wert D (D.rtyp r))
    (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon f).fragt (.inr (.inl r)))) = some v)
    (hw : wahr? (eval (((M.weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte) zusage
      (((M.weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte) (.cons v ρ)) = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann rest (.schrumpf k)) (((M.weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannRegLiesElseWahr M f l Γ Λ Λ' r hk zusage sonst rest k ρ hhead
    v hv _ rfl hw (leseEv _ Λ zusage.orte ++ [Ereignis.fremd (.inr (.inl r))])
    (by rw [lese_spur, List.append_assoc]; rfl) hΛ, zustandG_neu rfl rfl⟩

theorem w_regLiesElseFalsch {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool)
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (D.rtyp r :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.regReadElse r hk zusage sonst rest) k⟩)
    (v : Wert D (D.rtyp r))
    (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon f).fragt (.inr (.inl r)))) = some v)
    (hw : wahr? (eval (((M.weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte) zusage
      (((M.weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte) (.cons v ρ)) = false)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann sonst.alsBlock.2 (.abbruch k)) (((M.weltVon f).fragt (.inr (.inl r))).lese Λ zusage.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannRegLiesElseFalsch M f l Γ Λ Λ' r hk zusage sonst rest k ρ hhead
    v hv _ rfl hw (leseEv _ Λ zusage.orte ++ [Ereignis.fremd (.inr (.inl r))])
    (by rw [lese_spur, List.append_assoc]; rfl) hΛ, zustandG_neu rfl rfl⟩

theorem w_awaits {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
    (hL : gdarf D g Λ) (hat : D.atomar g = true)
    (rest : Block D (vertragVon D z.kopf.f) l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.awaits g payload hp hL hat rest) k⟩)
    (hvis : O.sichtbar g ((M.weltVon f).fragt (.inr (.inr g))) = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (.cons ((((M.weltVon f).fragt (.inr (.inr g))).lese Λ [.inr g]).globs g) ρ)
        (.dann rest (.schrumpf k)) (((M.weltVon f).fragt (.inr (.inr g))).lese Λ [.inr g]) := by
  subst hz
  exact ⟨_, RufSchrittG.dannAwaits M f l Γ Λ Λ' g payload hp hL hat rest k ρ hhead hvis _ rfl
    (leseEv _ Λ [.inr g] ++ [Ereignis.fremd (.inr (.inr g))])
    (by rw [lese_spur, List.append_assoc]; rfl) hΛ, zustandG_neu rfl rfl⟩

theorem w_exchange {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (g : D.Glob) (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
    (hw : (vertragVon D z.kopf.f).gschreibt g = true) (hL : gdarf D g Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.exchange g neuE hw hL rest) k⟩)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (.cons (((M.weltVon f).lese Λ (.inr g :: neuE.orte)).globs g) ρ)
        (.dann rest (.schrumpf k))
        (((M.weltVon f).lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval ((M.weltVon f).lese Λ (.inr g :: neuE.orte)) neuE
            ((M.weltVon f).lese Λ (.inr g :: neuE.orte))
            (.cons (((M.weltVon f).lese Λ (.inr g :: neuE.orte)).globs g) ρ))) := by
  subst hz
  exact ⟨_, RufSchrittG.dannExchange M f l Γ Λ Λ' g neuE hw hL rest k ρ hhead _ rfl _ rfl
    ([Ereignis.gzugriff g true Λ ((M.weltVon f).lese Λ (.inr g :: neuE.orte)).haelt] ++
      leseEv (M.weltVon f) Λ (.inr g :: neuE.orte))
    (by rw [List.append_assoc]; rfl) hΛ, zustandG_neu rfl rfl⟩

theorem w_gleit {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp) (a : Expr D Γ Λ (.fl l₁ h₁))
    (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.float op a b lo hi rest) k⟩)
    (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval ((M.weltVon f).lese Λ (a.orte ++ b.orte)) a
        ((M.weltVon f).lese Λ (a.orte ++ b.orte)) ρ).x
      (eval ((M.weltVon f).lese Λ (a.orte ++ b.orte)) b
        ((M.weltVon f).lese Λ (a.orte ++ b.orte)) ρ).x) = some v)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann rest (.schrumpf k)) ((M.weltVon f).lese Λ (a.orte ++ b.orte)) := by
  subst hz
  exact ⟨_, RufSchrittG.dannGleit M f l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead
    _ rfl v hv _ rfl hΛ, zustandG_neu rfl rfl⟩

theorem w_gleitLit {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (q lo hi : Int × Int)
    (rest : Block D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.floatLit q lo hi rest) k⟩)
    (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann rest (.schrumpf k)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannGleitLit M f l Γ Λ Λ' q lo hi rest k ρ hhead v hv,
    zustandG_neu rfl rfl⟩

theorem w_gleitVon {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁)) (lo hi : Int × Int)
    (rest : Block D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.floatOf e lo hi rest) k⟩)
    (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval ((M.weltVon f).lese Λ e.orte) e
      ((M.weltVon f).lese Λ e.orte) ρ).n) = some v)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann rest (.schrumpf k)) ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannGleitVon M f l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead _ rfl v hv
    _ rfl hΛ, zustandG_neu rfl rfl⟩

theorem w_gleitNarrowOk {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {l₁ h₁ : Int × Int} (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int)
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.floatNarrow e lo hi sonst rest) k⟩)
    (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval ((M.weltVon f).lese Λ e.orte) e
      ((M.weltVon f).lese Λ e.orte) ρ).x = some v)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann rest (.schrumpf k)) ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannGleitNarrowOk M f l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead
    _ rfl v hv _ rfl hΛ, zustandG_neu rfl rfl⟩

theorem w_gleitNarrowElse {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {l₁ h₁ : Int × Int} (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int)
    (sonst : Endblock D (vertragVon D z.kopf.f) l Γ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l (.fl lo hi :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.floatNarrow e lo hi sonst rest) k⟩)
    (hn : gleitPasst lo hi (eval ((M.weltVon f).lese Λ e.orte) e
      ((M.weltVon f).lese Λ e.orte) ρ).x = none)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann sonst.alsBlock.2 (.abbruch k))
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannGleitNarrowElse M f l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead
    _ rfl hn _ rfl hΛ, zustandG_neu rfl rfl⟩

theorem w_rueck {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst) {Γ : Ctx} {Λ : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨false, Γ, Λ, ρ, .ende (.ret e hperm)⟩)
    (hΛ : HeldIn Λ (offen z.spur)) (hnw : caller.wartend = false) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f caller rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.rueck M f caller rst hpop Γ Λ e hperm ρ hhead _ rfl
    (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl _ rfl _ rfl hnw, gepopptG_neu rfl rfl⟩

theorem w_rueckCons {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst) {Γ : Ctx} {Λ : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende)
    (rest : Endblock D (vertragVon D z.kopf.f) false Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨false, Γ, Λ, ρ, .ende (.cons (.ret e hperm) rest)⟩)
    (hΛ : HeldIn Λ (offen z.spur)) (hnw : caller.wartend = false) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f caller rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.rueckCons M f caller rst hpop Γ Λ e hperm rest ρ hhead _ rfl
    (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl _ rfl _ rfl hnw, gepopptG_neu rfl rfl⟩

theorem w_dannRet {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.ret e hperm) rest) k⟩)
    (hΛ : HeldIn Λ (offen z.spur)) (hnw : caller.wartend = false) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f caller rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannRet M f l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ
    _ rfl _ rfl (M.faeden f).kopf.rho rfl _ rfl _ rfl _ rfl hnw, gepopptG_neu rfl rfl⟩

end Schritte

end Gabbro.Grammatik
