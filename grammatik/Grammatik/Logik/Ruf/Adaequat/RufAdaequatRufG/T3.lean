/- Part 3 of 10 of `RufAdaequatRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

section SchritteGrund

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem w_rueckGrundP {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst)
    {zielG : Fin (D.gruende z.kopf.f) → RufRahmenG D} (hart : PopGrund z.kopf.f caller zielG)
    {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r : Fin (vertragVon D z.kopf.f).gruende)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨lr, Γ, Λ, ρ, .ende (.retWhy r hperm)⟩)
    (hΛ : HeldIn Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptGrundG M' f (zielG r) rst z.kopf.f z.kopf.rho z.kopf.s0 z.log r (M.weltVon f) := by
  subst hz
  cases hart with
  | sonst err restb k ρc hc =>
    exact ⟨_, RufSchrittG.rueckGrund M f r hperm ρ hhead caller rst hpop _ _ _ _ _ _ err restb
      k ρc hc hΛ _ rfl (M.faeden f).kopf.rho rfl _ rfl r rfl rfl, gepopptGrundG_neu rfl rfl⟩

theorem w_rueckConsGrundP {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst)
    {zielG : Fin (D.gruende z.kopf.f) → RufRahmenG D} (hart : PopGrund z.kopf.f caller zielG)
    {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r : Fin (vertragVon D z.kopf.f).gruende)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende)
    (rest : Endblock D (vertragVon D z.kopf.f) lr Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨lr, Γ, Λ, ρ, .ende (.cons (.retWhy r hperm) rest)⟩)
    (hΛ : HeldIn Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptGrundG M' f (zielG r) rst z.kopf.f z.kopf.rho z.kopf.s0 z.log r (M.weltVon f) := by
  subst hz
  cases hart with
  | sonst err restb k ρc hc =>
    exact ⟨_, RufSchrittG.rueckConsGrund M f r hperm rest ρ hhead caller rst hpop _ _ _ _ _ _
      err restb k ρc hc hΛ _ rfl (M.faeden f).kopf.rho rfl _ rfl r rfl rfl,
      gepopptGrundG_neu rfl rfl⟩

theorem w_dannRetGrundP {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst)
    {zielG : Fin (D.gruende z.kopf.f) → RufRahmenG D} (hart : PopGrund z.kopf.f caller zielG)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (r : Fin (vertragVon D z.kopf.f).gruende)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.retWhy r hperm) rest) k⟩)
    (hΛ : HeldIn Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptGrundG M' f (zielG r) rst z.kopf.f z.kopf.rho z.kopf.s0 z.log r (M.weltVon f) := by
  subst hz
  cases hart with
  | sonst err restb k' ρc hc =>
    exact ⟨_, RufSchrittG.dannRetGrund M f r hperm rest k ρ hhead caller rst hpop _ _ _ _ _ _
      err restb k' ρc hc hΛ _ rfl (M.faeden f).kopf.rho rfl _ rfl r rfl rfl,
      gepopptGrundG_neu rfl rfl⟩

end SchritteGrund
/-! ## 4. What a call must deliver: the callee's frame runs to its pop -/

/-- **The callee obligation.** For every admitted callee `g`: if its handler
    run ends normally in `σ'` with value `v`, the machine, from the callee's
    fresh frame (entry world `σ1`, residue `ende (P.rumpf g)`) above any
    caller, runs by steps of `f` alone to the pop that resumes the caller as
    `PopArt` says, logging the return of `v` at world `σ'`, with shared
    memory `σ'.speicher` and the same held locks as at entry; and if the
    handler run answers a reason `r` in `σ'`, the machine pops through the
    error channel into a caller waiting in `let … else` (`PopGrund`),
    logging `grund … r … σ'`. Proved for the body-running handler by
    induction on the depth (`rufOk_tief`). -/
def RufOk (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (A : D.Lock → Prop)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (C : D.Fn → Prop) : Prop :=
  (∀ (g : D.Fn), C g → ∀ (σ1 σ' : World D) (rhoG : Env D (D.params g)) (v : ErgVal D (D.erg g)),
    R g σ1 rhoG = .ok σ' v →
    ∀ (M : RufMaschineG D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (log : List (RufEreignisF D)),
      ZustandG M f (caller :: rst) g rhoG σ1 log rhoG (.ende (P.rumpf g)) σ1 →
      ∀ (ziel : ErgVal D (D.erg g) → RufRahmenG D), PopArt g caller ziel →
      HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) (offen σ1.spur) → FreiA A M f →
      ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
        GepopptG M' f (ziel v) rst g rhoG σ1 (ext ++ log) v σ' ∧ offen σ'.spur = offen σ1.spur) ∧
  (∀ (g : D.Fn), C g → ∀ (σ1 σ' : World D) (rhoG : Env D (D.params g)) (r : Fin (D.gruende g)),
    R g σ1 rhoG = .why σ' r →
    ∀ (M : RufMaschineG D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (log : List (RufEreignisF D)),
      ZustandG M f (caller :: rst) g rhoG σ1 log rhoG (.ende (P.rumpf g)) σ1 →
      ∀ (zielG : Fin (D.gruende g) → RufRahmenG D), PopGrund g caller zielG →
      HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) (offen σ1.spur) → FreiA A M f →
      ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
        GepopptGrundG M' f (zielG r) rst g rhoG σ1 (ext ++ log) r σ' ∧
        offen σ'.spur = offen σ1.spur)

/-- A covered leaf does not consult the call handler. -/
theorem BlattG.exec_R {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {s : Stmt D V l Γ Λ Λ'} (h : BlattG s) (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R s σ ρ = execStmt O passes keinRuf s σ ρ := by
  cases h <;> rfl

/-- The callee's entry holdings from the caller's: `RufPasst.hh` (`⊆`), the
    caller's extra locks below the callee's floor (`hx`, `hb`). -/
theorem heldB_eintritt {V : Vertrag D} {g : D.Fn} {Λ : List (Res D)} {σ : World D}
    (hp : RufPasst D V (D.signatur g) Λ) (hΛ : HeldB V.boden Λ (offen σ.spur))
    (os : List (D.Tab ⊕ D.Glob)) (Λ₀ : List (Res D)) :
    HeldB (D.signatur g).boden (Signatur.anfang D (D.signatur g)) (offen (σ.lese Λ₀ os).spur) :=
  heldB_ruf hp (bodenUnter_refl _) (heldB_lese os hΛ)

/-- After the callee's grund pop the resumed caller frame (its else block)
    IS a thread state of the caller's frame. -/
theorem gepopptGrund_zustand {M : RufMaschineG D} {f : Faden} {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} {g : D.Fn} {rhoG : Env D (D.params g)} {s1 : World D}
    {log e2 : List (RufEreignisF D)} {e : RufEreignisF D} {r : Fin (D.gruende g)}
    {σ' : World D} (h : GepopptGrundG M f caller rst g rhoG s1 (e2 ++ e :: log) r σ')
    {fn : D.Fn} {rho : Env D (D.params fn)} {s0 : World D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {rr : GRest D (vertragVon D fn) l Γ Λ}
    (hc : caller = ⟨fn, rho, s0, ⟨l, Γ, Λ, ρ, rr⟩⟩) :
    ZustandG M f rst fn rho s0
      ((RufEreignisF.why g rhoG r s1 σ' :: e2 ++ [e]) ++ log) ρ rr σ' := by
  refine ⟨?_, h.2⟩
  rw [h.1, hc]
  simp only [List.cons_append, List.append_assoc, List.nil_append]

/-- After the callee's pop the resumed caller frame IS a thread state of the
    caller's frame, whose log gained the call's events. -/
theorem gepoppt_zustand {M : RufMaschineG D} {f : Faden} {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} {g : D.Fn} {rhoG : Env D (D.params g)} {s1 : World D}
    {log e2 : List (RufEreignisF D)} {e : RufEreignisF D} {v : ErgVal D (D.erg g)}
    {σ' : World D} (h : GepopptG M f caller rst g rhoG s1 (e2 ++ e :: log) v σ')
    {fn : D.Fn} {rho : Env D (D.params fn)} {s0 : World D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D fn) l Γ Λ}
    (hc : caller = ⟨fn, rho, s0, ⟨l, Γ, Λ, ρ, r⟩⟩) :
    ZustandG M f rst fn rho s0
      ((RufEreignisF.rueck g rhoG v s1 σ' :: e2 ++ [e]) ++ log) ρ r σ' := by
  refine ⟨?_, h.2⟩
  rw [h.1, hc]
  simp only [List.cons_append, List.append_assoc, List.nil_append]



/-! ## 5. Loops and abrupt exits: the steps, the peels, the sequential outcomes -/

section Schleifen

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem w_dannTrav {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.traverse t inv body) rest) k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.trav t inv body (alleIndizes (D.count t)) (.dann rest k)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannTrav M f l Γ Λ Λ'' t inv body rest k ρ hhead, zustandG_neu rfl rfl⟩

theorem w_travNext {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (i : Wert D (.index (D.count t))) (is : List (Wert D (.index (D.count t))))
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .trav t inv body (i :: is) k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ inv.orte) inv ((M.weltVon f).lese Λ inv.orte) ρ)
      = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log (.cons i ρ)
        (.dann body (.travRest t inv body is k)) ((M.weltVon f).lese Λ inv.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.travNext M f l Γ Λ t inv body i is k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_travFort {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t))))
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (i : Wert D (.index (D.count t)))
    (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, .index (D.count t) :: Γ, Λ, .cons i ρ,
      .travRest t inv body is k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.trav t inv body is k) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.travFort M f l Γ Λ t inv body is k i ρ hhead, zustandG_neu rfl rfl⟩

theorem w_travDone {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .trav t inv body [] k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ inv.orte) inv ((M.weltVon f).lese Λ inv.orte) ρ)
      = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ k
        ((M.weltVon f).lese Λ inv.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.travDone M f l Γ Λ t inv body k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_dannRetry {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (ueber : Block D (vertragVon D z.kopf.f) l Γ Λ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.retry n bis body ueber) rest) k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.wieder n bis body ueber (.dann rest k)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannRetry M f l Γ Λ Λ Λ'' n bis body ueber rest k ρ hhead,
    zustandG_neu rfl rfl⟩

theorem w_wiederUeber {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (bis : Expr D Γ Λ .bool) (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (ueber : Block D (vertragVon D z.kopf.f) l Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .wieder 0 bis body ueber k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (.cons (.ite bis .nil ueber) .nil) k) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.wiederUeber M f l Γ Λ bis body ueber k ρ hhead, zustandG_neu rfl rfl⟩

theorem w_wiederWeiter {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (ueber : Block D (vertragVon D z.kopf.f) l Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .wieder (n + 1) bis body ueber k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ bis.orte) bis ((M.weltVon f).lese Λ bis.orte) ρ)
      = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ k
        ((M.weltVon f).lese Λ bis.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.wiederWeiter M f l Γ Λ n bis body ueber k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_wiederSchritt {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (ueber : Block D (vertragVon D z.kopf.f) l Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .wieder (n + 1) bis body ueber k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ bis.orte) bis ((M.weltVon f).lese Λ bis.orte) ρ)
      = false)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann body (.wiederRest n bis body ueber k)) ((M.weltVon f).lese Λ bis.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.wiederSchritt M f l Γ Λ n bis body ueber k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_wiederFort {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (ueber : Block D (vertragVon D z.kopf.f) l Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λ, ρ, .wiederRest n bis body ueber k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.wieder n bis body ueber k) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.wiederFort M f l Γ Λ n bis body ueber k ρ hhead, zustandG_neu rfl rfl⟩

theorem w_dannForever {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.forever a inv body) rest) k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.ewig a passes inv body (.dann rest k)) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannForever M f l Γ Λ Λ Λ'' a inv body rest k ρ hhead,
    zustandG_neu rfl rfl⟩

theorem w_ewigWeiter {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ewig a (n + 1) inv body k⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ inv.orte) inv ((M.weltVon f).lese Λ inv.orte) ρ)
      = true)
    (hΛ : HeldIn Λ (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann body (.ewigRest a n inv body k)) ((M.weltVon f).lese Λ inv.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.ewigWeiter M f l Γ Λ a n inv body k ρ hhead _ rfl hw _ rfl hΛ,
    zustandG_neu rfl rfl⟩

theorem w_ewigFort {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λ, ρ, .ewigRest a n inv body k⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.ewig a n inv body k) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.ewigFort M f l Γ Λ a n inv body k ρ hhead, zustandG_neu rfl rfl⟩

end Schleifen
/-! ### Abrupt exits: the exit statement, the loop shims, the peels -/

/-- The abrupt exit statement of kind `w` (`true`: `leave`, `false`: `next`),
    at any holdings, inside a loop (`hl`). -/
def abbS {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (hl : l = true) :
    Bool → Stmt D V l Γ Λ Λ
  | true => .leave hl
  | false => .next hl

section Ausgaenge

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- Holdings exactly held carry backwards along a block: a block keeps the
    held locks of its holdings (`Block.held_iff`). -/
theorem heldB_block {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λx Λ : List (Res D)}
    (r : Block D V l Γ Λx Λ) {bo : Option Int} {h : List D.Lock} (hh : HeldB bo Λ h) :
    HeldB bo Λx h :=
  heldB_iff (fun L => (Block.held_iff r L).symm) hh

/-- `leave` at the `traverse` shim: the invariant is read, the loop is left. -/
theorem w_leaveTrav {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λx : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t))))
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (r : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, .index (D.count t) :: Γ, Λx, .cons i ρ,
      .dann (.cons (abbS rfl true) r) (.travRest t inv body is k)⟩)
    (hw : wahr? (eval ((M.weltVon f).lese Λ inv.orte) inv ((M.weltVon f).lese Λ inv.orte) ρ)
      = true)
    (hΛ : HeldIn Λx (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ k
        ((M.weltVon f).lese Λ inv.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannLeaveTrav M f l Γ Λ t inv body is k r i ρ rfl hhead _ _ [] rfl rfl
    (fun _ _ h => absurd h List.not_mem_nil) _ rfl hw _ rfl hΛ, zustandG_neu rfl rfl⟩

/-- `next` at the `traverse` shim: the next index. -/
theorem w_nextTrav {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λx : List (Res D)}
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t))))
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (r : Block D (vertragVon D z.kopf.f) true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, .index (D.count t) :: Γ, Λx, .cons i ρ,
      .dann (.cons (abbS rfl false) r) (.travRest t inv body is k)⟩)
    (hΛ : HeldIn Λx (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.trav t inv body is k) (M.weltVon f) := by
  subst hz
  exact ⟨_, RufSchrittG.dannNextTrav M f l Γ Λ t inv body is k r i ρ rfl hhead _ _ [] rfl rfl
    (fun _ _ h => absurd h List.not_mem_nil) hΛ, zustandG_neu rfl rfl⟩

/-- `leave`/`next` at the `retry` shim. -/
theorem w_abbWieder {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λx : List (Res D)} (w : Bool)
    (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (ueber : Block D (vertragVon D z.kopf.f) l Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (r : Block D (vertragVon D z.kopf.f) true Γ Λx Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λx, ρ,
      .dann (.cons (abbS rfl w) r) (.wiederRest n bis body ueber k)⟩)
    (hΛ : HeldIn Λx (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (match w with | true => k | false => .wieder n bis body ueber k) (M.weltVon f) := by
  subst hz
  cases w with
  | true =>
    exact ⟨_, RufSchrittG.dannLeaveWieder M f l Γ Λ n bis body ueber k r ρ rfl hhead _ _ []
      rfl rfl (fun _ _ h => absurd h List.not_mem_nil) hΛ, zustandG_neu rfl rfl⟩
  | false =>
    exact ⟨_, RufSchrittG.dannNextWieder M f l Γ Λ n bis body ueber k r ρ rfl hhead _ _ []
      rfl rfl (fun _ _ h => absurd h List.not_mem_nil) hΛ, zustandG_neu rfl rfl⟩

/-- `leave`/`next` at the `forever` shim. -/
theorem w_abbEwig {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λx : List (Res D)} (w : Bool)
    (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D z.kopf.f) true Γ Λ Λ)
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (r : Block D (vertragVon D z.kopf.f) true Γ Λx Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λx, ρ,
      .dann (.cons (abbS rfl w) r) (.ewigRest a n inv body k)⟩)
    (hΛ : HeldIn Λx (offen z.spur) := by held_tac) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (match w with | true => k | false => .ewig a n inv body k) (M.weltVon f) := by
  subst hz
  cases w with
  | true =>
    exact ⟨_, RufSchrittG.dannLeaveEwig M f l Γ Λ a n inv body k r ρ rfl hhead _ _ []
      rfl rfl (fun _ _ h => absurd h List.not_mem_nil) hΛ, zustandG_neu rfl rfl⟩
  | false =>
    exact ⟨_, RufSchrittG.dannNextEwig M f l Γ Λ a n inv body k r ρ rfl hhead _ _ []
      rfl rfl (fun _ _ h => absurd h List.not_mem_nil) hΛ, zustandG_neu rfl rfl⟩

/-- Peel a `dann` layer off an abrupt exit. -/
theorem w_peelDann {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {Γ : Ctx} {Λ Λ1 Λ2 : List (Res D)} (w : Bool)
    (r : Block D (vertragVon D z.kopf.f) true Γ Λ Λ1)
    (b : Block D (vertragVon D z.kopf.f) true Γ Λ1 Λ2)
    (k : GRest D (vertragVon D z.kopf.f) true Γ Λ2) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λ, ρ, .dann (.cons (abbS rfl w) r) (.dann b k)⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (.cons (abbS rfl w) .nil) k) (M.weltVon f) := by
  subst hz
  cases w with
  | true => exact ⟨_, RufSchrittG.peelDannLeave M f true Γ Λ r b k ρ rfl hhead,
      zustandG_neu rfl rfl⟩
  | false => exact ⟨_, RufSchrittG.peelDannNext M f true Γ Λ r b k ρ rfl hhead,
      zustandG_neu rfl rfl⟩

/-- Peel a `schrumpf` layer off an abrupt exit: the bound value is dropped. -/
theorem w_peelSchrumpf {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {Γ : Ctx} {Λ Λ1 : List (Res D)} {τ : Ty} (w : Bool)
    (r : Block D (vertragVon D z.kopf.f) true (τ :: Γ) Λ Λ1)
    (k : GRest D (vertragVon D z.kopf.f) true Γ Λ1) (v : Wert D τ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, τ :: Γ, Λ, .cons v ρ, .dann (.cons (abbS rfl w) r) (.schrumpf k)⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (.cons (abbS rfl w) .nil) k) (M.weltVon f) := by
  subst hz
  cases w with
  | true => exact ⟨_, RufSchrittG.peelSchrumpfLeave M f true Γ Λ τ r k (.cons v ρ) rfl hhead,
      zustandG_neu rfl rfl⟩
  | false => exact ⟨_, RufSchrittG.peelSchrumpfNext M f true Γ Λ τ r k (.cons v ρ) rfl hhead,
      zustandG_neu rfl rfl⟩

/-- Peel a `frei` layer off an abrupt exit: the lock is released (`gibt`),
    as `execStmt`'s `locks` releases it around the exit outcome. -/
theorem w_peelFrei {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {Γ : Ctx} {Λ Λ1 : List (Res D)} (w : Bool) (L : D.Lock)
    (r : Block D (vertragVon D z.kopf.f) true Γ Λ (Res.held L :: Λ1))
    (k : GRest D (vertragVon D z.kopf.f) true Γ Λ1) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λ, ρ, .dann (.cons (abbS rfl w) r) (.frei L k)⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (.cons (abbS rfl w) .nil) k) ((M.weltVon f).gibt L) := by
  subst hz
  cases w with
  | true => exact ⟨_, RufSchrittG.peelFreiLeave M f true Γ Λ L r k ρ rfl hhead,
      zustandG_neu rfl rfl⟩
  | false => exact ⟨_, RufSchrittG.peelFreiNext M f true Γ Λ L r k ρ rfl hhead,
      zustandG_neu rfl rfl⟩

/-- Peel an `abbruch` layer off an abrupt exit: a `leave`/`next` in an
    `else` branch reaches the continuation after the branching form. -/
theorem w_peelAbbruch {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {Γ : Ctx} {Λ Λ1 Λk : List (Res D)} (w : Bool)
    (r : Block D (vertragVon D z.kopf.f) true Γ Λ Λ1)
    (k : GRest D (vertragVon D z.kopf.f) true Γ Λk) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨true, Γ, Λ, ρ, .dann (.cons (abbS rfl w) r) (.abbruch k)⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f z.stapel z.kopf.f z.kopf.rho z.kopf.s0 z.log ρ
        (.dann (.cons (abbS rfl w) .nil) k) (M.weltVon f) := by
  subst hz
  cases w with
  | true => exact ⟨_, RufSchrittG.peelAbbruchLeave M f Γ Λ Λ1 Λk r k ρ rfl hhead,
      zustandG_neu rfl rfl⟩
  | false => exact ⟨_, RufSchrittG.peelAbbruchNext M f Γ Λ Λ1 Λk r k ρ rfl hhead,
      zustandG_neu rfl rfl⟩

end Ausgaenge
/-- An outcome that is not an abrupt loop exit (`leave`/`next`). -/
def Ausgang.ohneAbbruch {V : Vertrag D} {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Prop
  | .leave .. => False
  | .next .. => False
  | _ => True


end Gabbro.Grammatik
