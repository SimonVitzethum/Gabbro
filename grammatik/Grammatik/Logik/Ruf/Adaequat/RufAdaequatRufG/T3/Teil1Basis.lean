module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T2

@[expose] public section



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




end Gabbro.Grammatik
