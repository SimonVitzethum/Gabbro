/- Part 2 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Inv

variable {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}

theorem StmtG.ite_inv {Λ Λ' : List (Res D)} {c : Expr D Γ Λ .bool}
    {t e : Block D V l Γ Λ Λ'} (h : StmtG A mr (.ite c t e)) :
    BlockG A mr t ∧ BlockG A mr e := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | ite _ _ _ ht he => exact ⟨ht, he⟩

theorem StmtG.onOption_inv {Λ Λ' : List (Res D)} {n : Int} {o : Expr D Γ Λ (.opt n)}
    {p : Block D V l (.index n :: Γ) Λ Λ'} {a : Block D V l Γ Λ Λ'}
    (h : StmtG A mr (.onOption o p a)) : BlockG A mr p ∧ BlockG A mr a := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | onOption _ _ _ hp ha => exact ⟨hp, ha⟩

theorem StmtG.onTag_inv {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    {v : Expr D Γ Λ (.sum cs)} {arms : Arms D V l Γ Λ Λ' cs}
    (h : StmtG A mr (.onTag v arms)) : ArmsG A mr arms := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | onTag _ _ ha => exact ha

theorem StmtG.onGrund_inv {Λ Λ' : List (Res D)} {n : Nat}
    {r : Expr D Γ Λ (.why n)} {arms : GrundArms D V l Γ Λ Λ' n}
    (h : StmtG A mr (.onWhy r arms)) : GrundArmsG A mr arms := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | onWhy _ _ ha => exact ha

theorem StmtG.breaking_inv {Λ Λ' : List (Res D)} {i : D.Inv}
    {body : Block D V l Γ Λ Λ'} (h : StmtG A mr (.breaking i body)) : BlockG A mr body := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | breaking _ _ hb => exact hb

theorem StmtG.locks_inv {Λ : List (Res D)} {L : D.Lock}
    {hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L}
    {body : Block D V l Γ (.held L :: Λ) (.held L :: Λ)}
    (h : StmtG A mr (.locks L hr body)) : A L ∧ BlockG A false body := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | locks _ _ _ hA hb => exact ⟨hA, hb⟩

theorem StmtG.ret_inv {Λ : List (Res D)} {e : ErgExpr D Γ Λ V.erg} {hΛ : Λ.Perm V.ende}
    (h : StmtG A mr (.ret (l := l) e hΛ)) : mr = true := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp only [Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | ret _ _ => rfl

theorem BlockG.cons_inv {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} (h : BlockG A mr (.cons s rest)) :
    StmtG A mr s ∧ BlockG A mr rest := by
  cases h with
  | cons _ _ hs hr => exact ⟨hs, hr⟩

theorem BlockG.bind_inv {Λ Λ' : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Block D V l (τ :: Γ) Λ Λ'} (h : BlockG A mr (.bind e rest)) : BlockG A mr rest := by
  cases h with
  | bind _ _ hr => exact hr

theorem BlockG.regLies_inv {Λ Λ' : List (Res D)} {r : D.Reg}
    {hk : (D.rklasse r).lesbar = true} {rest : Block D V l (D.rtyp r :: Γ) Λ Λ'}
    (h : BlockG A mr (.regRead r hk rest)) : BlockG A mr rest := by
  cases h with
  | regRead _ _ _ hr => exact hr

theorem BlockG.awaits_inv {Λ Λ' : List (Res D)} {g : D.Glob} {payload : List D.Glob}
    {hp : payload = D.nutzlast g} {hL : gdarf D g Λ} {hat : D.atomar g = true}
    {rest : Block D V l (D.gtyp g :: Γ) Λ Λ'}
    (h : BlockG A mr (.awaits g payload hp hL hat rest)) : BlockG A mr rest := by
  cases h with
  | awaits _ _ _ _ _ _ hr => exact hr

theorem BlockG.exchange_inv {Λ Λ' : List (Res D)} {g : D.Glob}
    {neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)} {hw : V.gschreibt g = true}
    {hL : gdarf D g Λ} {rest : Block D V l (D.gtyp g :: Γ) Λ Λ'}
    (h : BlockG A mr (.exchange g neu hw hL rest)) : BlockG A mr rest := by
  cases h with
  | exchange _ _ _ _ _ hr => exact hr

theorem BlockG.gleit_inv {Λ Λ' : List (Res D)} {l1 h1 l2 h2 : Int × Int} {op : GleitOp}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)} {lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockG A mr (.float op a b lo hi rest)) : BlockG A mr rest := by
  cases h with
  | float _ _ _ _ _ _ hr => exact hr

theorem BlockG.gleitLit_inv {Λ Λ' : List (Res D)} {q lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockG A mr (.floatLit q lo hi rest)) : BlockG A mr rest := by
  cases h with
  | floatLit _ _ _ _ hr => exact hr

theorem BlockG.gleitVon_inv {Λ Λ' : List (Res D)} {l1 h1 : Int}
    {e : Expr D Γ Λ (.int l1 h1)} {lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockG A mr (.floatOf e lo hi rest)) : BlockG A mr rest := by
  cases h with
  | floatOf _ _ _ _ hr => exact hr

theorem BlockG.regLiesElse_inv {Λ Λ' : List (Res D)} {r : D.Reg}
    {hk : (D.rklasse r).lesbar = true} {zusage : Expr D (D.rtyp r :: Γ) Λ .bool}
    {sonst : Endblock D V l Γ Λ} {rest : Block D V l (D.rtyp r :: Γ) Λ Λ'}
    (h : BlockG A mr (.regReadElse r hk zusage sonst rest)) :
    mr = true ∧ BlockG A true rest ∧ EndG A sonst ∧ l = false := by
  cases h with
  | regReadElse _ _ _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem BlockG.narrow_inv {Λ Λ' : List (Res D)} {lo hi : Int}
    {e : Expr D Γ Λ (.int lo hi)} {lo' hi' : Int} {sonst : Endblock D V l Γ Λ}
    {rest : Block D V l (.int lo' hi' :: Γ) Λ Λ'}
    (h : BlockG A mr (.narrow e lo' hi' sonst rest)) :
    mr = true ∧ BlockG A true rest ∧ EndG A sonst ∧ l = false := by
  cases h with
  | narrow _ _ _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem BlockG.pruefung_inv {Λ Λ' : List (Res D)} {c : Expr D Γ Λ .bool}
    {sonst : Endblock D V l Γ Λ} {rest : Block D V l Γ Λ Λ'}
    (h : BlockG A mr (.check c sonst rest)) :
    mr = true ∧ BlockG A true rest ∧ EndG A sonst ∧ l = false := by
  cases h with
  | check _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem BlockG.gleitNarrow_inv {Λ Λ' : List (Res D)} {l1 h1 : Int × Int}
    {e : Expr D Γ Λ (.fl l1 h1)} {lo hi : Int × Int} {sonst : Endblock D V l Γ Λ}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockG A mr (.floatNarrow e lo hi sonst rest)) :
    mr = true ∧ BlockG A true rest ∧ EndG A sonst ∧ l = false := by
  cases h with
  | floatNarrow _ _ _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem ArmsG.cons_inv {Λ Λ' : List (Res D)} {c : Option (Int × Int)}
    {cs : List (Option (Int × Int))} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {rest : Arms D V l Γ Λ Λ' cs} (h : ArmsG A mr (.cons b rest)) :
    BlockG A mr b ∧ ArmsG A mr rest := by
  cases h with
  | cons _ _ hb hr => exact ⟨hb, hr⟩

theorem GrundArmsG.cons_inv {Λ Λ' : List (Res D)} {n : Nat}
    {b : Block D V l Γ Λ Λ'} {rest : GrundArms D V l Γ Λ Λ' n}
    (h : GrundArmsG A mr (.cons b rest)) : BlockG A mr b ∧ GrundArmsG A mr rest := by
  cases h with
  | cons _ _ hb hr => exact ⟨hb, hr⟩

theorem EndG.ret_inv {Λ : List (Res D)} {e : ErgExpr D Γ Λ V.erg} {hΛ : Λ.Perm V.ende}
    (h : EndG A (.ret (l := l) e hΛ)) : l = false := by
  cases h with
  | ret _ _ => rfl

theorem EndG.cons_inv {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : EndG A (.cons s rest)) :
    StmtG A true s ∧ EndG A rest ∧ l = false := by
  cases h with
  | cons _ _ hs hr => exact ⟨hs, hr, rfl⟩

theorem EndG.bind_inv {Λ : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Endblock D V l (τ :: Γ) Λ} (h : EndG A (.bind e rest)) : EndG A rest := by
  cases h with
  | bind _ _ hr => exact hr

end Inv
/-! ## 5. The step rules, re-stated over a thread state `z`

    Each `w_*` lemma fires one `RufSchrittG` constructor on a machine whose
    thread `f` IS `z` (`hz`), with every argument typed at `z.kopf.f`; the
    `subst` turns it into the constructor verbatim. Instantiated with a
    literal `z`, the arguments are typed at the literal's function. -/

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem w_blatt {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Endblock D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s rest)⟩)
    (hΛ : HeldIn Λ (offen z.spur)) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s (M.weltVon f) ρ = .ok σ' ρ')
    (herw : Erw (M.weltVon f) σ') :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ' (.ende rest) σ' := by
  subst hz
  obtain ⟨neu, hneu, hnz⟩ := herw
  exact ⟨_, RufSchrittG.blatt M f l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu
    (kein_nimmt hnz), zustandG_neu rfl rfl⟩

theorem w_dannBlatt {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons s rest) k⟩)
    (hΛ : HeldIn Λ (offen z.spur)) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s (M.weltVon f) ρ = .ok σ' ρ')
    (herw : Erw (M.weltVon f) σ') :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ' (.dann rest k) σ' := by
  subst hz
  obtain ⟨neu, hneu, hnz⟩ := herw
  exact ⟨_, RufSchrittG.dannBlatt M f l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu
    hstep hneu (kein_nimmt hnz), zustandG_neu rfl rfl⟩

theorem w_dannLeer {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann .nil k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ k (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannLeer M f l Γ Λ k ρ hhead, zustandG_neu rfl rfl⟩

theorem w_endeEntf {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Endblock D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hent : GEntfaltbar s = true)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s rest)⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (.cons s .nil) (.ende rest)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.endeEntf M f l Γ Λ Λ' s rest ρ hent hhead, zustandG_neu rfl rfl⟩

theorem w_iteWahr {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    (c : Expr D Γ Λ .bool) (t e : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.ite c t e) rest) k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ c.orte) c ((M.weltVon f).lese Λ c.orte) ρ)
      = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ (.dann t (.dann rest k))
        ((M.weltVon f).lese Λ c.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannIteWahr M f l Γ Λ Λ' Λ'' c t e rest k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_iteFalsch {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    (c : Expr D Γ Λ .bool) (t e : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.ite c t e) rest) k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ c.orte) c ((M.weltVon f).lese Λ c.orte) ρ)
      = false)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ (.dann e (.dann rest k))
        ((M.weltVon f).lese Λ c.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannIteFalsch M f l Γ Λ Λ' Λ'' c t e rest k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_optSome {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {n : Int}
    (o : Expr D Γ Λ (.opt n))
    (p : Block D (vertragVon D z.kopf.f) l (.index n :: Γ) Λ Λ')
    (a : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.onOption o p a) rest) k⟩)
    (v : Wert D (.index n))
    (hv : eval ((M.weltVon f).lese Λ o.orte) o ((M.weltVon f).lese Λ o.orte) ρ =
      Option.some v)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons v ρ)
        (.dann p (.schrumpf (.dann rest k))) ((M.weltVon f).lese Λ o.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannOnOptionSome M f l Γ Λ Λ' Λ'' n o p a rest k ρ hhead _ rfl
    v hv _ rfl hΛ, zustandG_neu rfl rfl⟩

theorem w_optNone {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {n : Int}
    (o : Expr D Γ Λ (.opt n))
    (p : Block D (vertragVon D z.kopf.f) l (.index n :: Γ) Λ Λ')
    (a : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.onOption o p a) rest) k⟩)
    (hv : eval ((M.weltVon f).lese Λ o.orte) o ((M.weltVon f).lese Λ o.orte) ρ =
      Option.none)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann a (.dann rest k)) ((M.weltVon f).lese Λ o.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannOnOptionNone M f l Γ Λ Λ' Λ'' n o p a rest k ρ hhead _ rfl
    hv _ rfl hΛ, zustandG_neu rfl rfl⟩

theorem w_tagSome {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    {cs : List (Option (Int × Int))} (v : Expr D Γ Λ (.sum cs))
    (arms : Arms D (vertragVon D z.kopf.f) l Γ Λ Λ' cs)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.onTag v arms) rest) k⟩)
    (lo hi : Int)
    (b : Block D (vertragVon D z.kopf.f) l (.int lo hi :: Γ) Λ Λ')
    (nutz : Nutzlast (some (lo, hi)))
    (hw : armWahlG arms (eval ((M.weltVon f).lese Λ v.orte) v
      ((M.weltVon f).lese Λ v.orte) ρ) = ⟨some (lo, hi), b, nutz⟩)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (armEnv nutz ρ)
        (.dann b (.schrumpf (.dann rest k))) ((M.weltVon f).lese Λ v.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannOnTagSome M f l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead _ rfl
    lo hi b nutz hw _ rfl hΛ, zustandG_neu rfl rfl⟩

theorem w_tagNone {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    {cs : List (Option (Int × Int))} (v : Expr D Γ Λ (.sum cs))
    (arms : Arms D (vertragVon D z.kopf.f) l Γ Λ Λ' cs)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.onTag v arms) rest) k⟩)
    (b : Block D (vertragVon D z.kopf.f) l Γ Λ Λ') (nutz : Nutzlast none)
    (hw : armWahlG arms (eval ((M.weltVon f).lese Λ v.orte) v
      ((M.weltVon f).lese Λ v.orte) ρ) = ⟨none, b, nutz⟩)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (armEnv nutz ρ)
        (.dann b (.dann rest k)) ((M.weltVon f).lese Λ v.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannOnTagNone M f l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead _ rfl
    b nutz hw _ rfl hΛ, zustandG_neu rfl rfl⟩

theorem w_grund {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} {n : Nat}
    (r : Expr D Γ Λ (.why n))
    (arms : GrundArms D (vertragVon D z.kopf.f) l Γ Λ Λ' n)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.onWhy r arms) rest) k⟩)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (grundWahlG arms (eval ((M.weltVon f).lese Λ r.orte) r
          ((M.weltVon f).lese Λ r.orte) ρ)) (.dann rest k)) ((M.weltVon f).lese Λ r.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannOnGrund M f l Γ Λ Λ' Λ'' n r arms rest k ρ hhead _ rfl
    _ rfl _ rfl hΛ, zustandG_neu rfl rfl⟩

theorem w_breaking {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    (i : D.Inv) (body : Block D (vertragVon D z.kopf.f) l Γ Λ Λ')
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.breaking i body) rest) k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann body (.dann rest k)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannBreaking M f l Γ Λ Λ' Λ'' i body rest k ρ hhead,
    zustandG_neu rfl rfl⟩

theorem w_locks {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D (vertragVon D z.kopf.f) l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hr body) rest) k⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) (hfrei : RufFreiG M f L) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann body (.frei L (.dann rest k))) ((M.weltVon f).nimmt L) := by
  subst hz
  have hn := nicht_gehalten L hr hΛ
  exact ⟨_, RufSchrittG.dannLocks M f l Γ Λ Λ'' L hr body rest k ρ hhead hn.2 hn.1 hfrei,
    zustandG_neu rfl rfl⟩

/-- `locks L` under held static holdings with a FLOOR (held-set relaxation):
    the extra locks of the thread rank below the floor `bo`, the lock ranks
    at least `bo`, so it is not held and ranks above everything held. -/
theorem w_locksB {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D (vertragVon D z.kopf.f) l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.locks L hr body) rest) k⟩)
    {bo : Option Int} (hΛ : HeldB bo Λ (offen z.spur)) (hbo : ∀ c, bo = some c → c ≤ D.rang L)
    (hfrei : RufFreiG M f L) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann body (.frei L (.dann rest k))) ((M.weltVon f).nimmt L) := by
  subst hz
  have hn := nicht_gehaltenB L hr hΛ hbo
  exact ⟨_, RufSchrittG.dannLocks M f l Γ Λ Λ'' L hr body rest k ρ hhead hn.2 hn.1 hfrei,
    zustandG_neu rfl rfl⟩

theorem w_freiGib {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (L : D.Lock) (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Res.held L :: Λ, ρ, .frei L k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ k
        ((M.weltVon f).gibt L) := by
  subst hz
  exact ⟨_, RufSchrittG.freiGib M f l Γ Λ L k ρ hhead, zustandG_neu rfl rfl⟩

theorem w_schrumpf {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (v : Wert D τ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, τ :: Γ, Λ, .cons v ρ, .schrumpf k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ k (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.schrumpfVergiss M f l Γ Λ τ k v ρ hhead, zustandG_neu rfl rfl⟩

theorem w_endeBind {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (rest : Endblock D (vertragVon D z.kopf.f) l (τ :: Γ) Λ)
    (ρ : Env D Γ) (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.bind e rest)⟩)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (.cons (eval ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ) ρ)
        (.ende rest) ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.endeBind M f l Γ Λ τ e rest ρ hhead _ rfl _ rfl hΛ, zustandG_neu rfl rfl⟩

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
