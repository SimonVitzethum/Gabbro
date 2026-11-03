module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T5

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 11. TARGET A: the machine realises the sequential result -/

/-- **TARGET A -- adequacy of the call machine G for call-free bodies.**
    Thread `f` of `M` runs a frame of `fn` (actual parameters `rho`, entry
    world `s0`) above a caller frame that does not wait for a bound value
    (`hnw`: the verbatim pop demands it since 2026-09-13), with residue
    `.ende b` for a covered (call-free, `EndG`) end block `b` at environment
    `ρ`; its static holdings `Λ` name exactly the locks its trace holds; no
    other thread holds a lock `b` may take (`A`). If the sequential semantics, started at
    the thread's current world `M.weltVon f`, returns `v` in world `σ'`,
    then steps of thread `f` alone reach a machine `M'` that has popped the
    frame, logged `rueck fn rho v s0 σ'` with THE SAME value `v`, and whose
    shared memory is `σ'.speicher`.

    How the machine's read world relates: the `rueck` step reads the result
    at `s1 = (M'.weltVon f).lese Λ e.orte` (`e` the returned expression)
    and logs `s1`; `execEnd`'s `ret` returns `σ.lese Λ e.orte`. The theorem
    shows these are EQUAL: the logged `s1` IS `σ'` -- trace included --
    and the new memory is `s1.speicher = σ'.speicher`. Other threads are
    untouched. -/
theorem rufG_adaequat (P : Programm D) (O : Orakel D) (passes : Nat)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (spur : List (Ereignis D)) (log : List (RufEreignisF D)) {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ) (b : Endblock D (vertragVon D fn) false Γ Λ)
    (A : D.Lock → Prop) (hb : EndG A b)
    (hM : M.faeden f = ⟨caller :: rst, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (hnw : caller.wartend = false)
    (hΛ : HeldGenau Λ (offen spur))
    (hfrei : ∀ L, A L → RufFreiG M f L)
    (σ' : World D) (v : ErgVal D (vertragVon D fn).erg)
    (hexec : execEnd O passes keinRuf b (M.weltVon f) ρ = .zurueck σ' v) :
    ∃ M', RufLaufG P O passes f M M' ∧
      M'.faeden f = ⟨rst, caller, σ'.spur, RufEreignisF.rueck fn rho v s0 σ' :: log⟩ ∧
      M'.speicher = σ'.speicher ∧
      (∀ g, g ≠ f → M'.faeden g = M.faeden g) := by
  have hsp : (M.weltVon f).spur = spur := by
    show (M.faeden f).spur = spur
    rw [hM]
  have hZ : ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende b) (M.weltVon f) :=
    ⟨by rw [hsp]; exact hM, rfl⟩
  obtain ⟨M', hl, hG⟩ := endRet P O passes f fn caller rst rho s0 log A hnw b hb
    (M.weltVon f) σ' ρ v hexec M hZ (by rw [hsp]; exact hΛ) hfrei
  exact ⟨M', hl, hG.1, hG.2, rufLaufG_fremd hl⟩

/-! ### The covered fragment is call-free in the sense of `HoareRegeln.lean`

    `EndG` refines `EndOhneRuf`: every covered body is a body the Hoare
    rules' call-freedom predicate accepts, so the sequential side of
    TARGET A is `R`-independent (`endOhneRuf_Runabhaengig`). -/

theorem blattG_ohneRuf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λ'} (h : BlattG s) : StmtOhneRuf s := by
  cases h <;> constructor

set_option maxHeartbeats 1600000 in
mutual

theorem stmtG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'),
    StmtG A mr s → StmtOhneRuf s
  | _, _, _, _, _, .assignSlot t f' i e hw hL, _ => blattG_ohneRuf (.assignSlot t f' i e hw hL)
  | _, _, _, _, _, .assignThru p t ht f' i e hw hL, _ =>
      blattG_ohneRuf (.assignThru _ p t ht f' i e hw hL)
  | _, _, _, _, _, .assignThruOwn p t ht f' i e m s ho he hg hw hL, _ =>
      blattG_ohneRuf (.assignThruOwn _ _ p t ht f' i e m s ho he hg hw hL)
  | _, _, _, _, _, .assignSlotRef r t ht ho f' e hw hL, _ =>
      blattG_ohneRuf (.assignSlotRef _ r t ht ho f' e hw hL)
  | _, _, _, _, _, .assignGlob g e hw hL, _ => blattG_ohneRuf (.assignGlob g e hw hL)
  | _, _, _, _, _, .putBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattG_ohneRuf (.putBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, _, .assignVar x e, _ => blattG_ohneRuf (.assignVar x e)
  | _, _, _, _, _, .shift t f' hτ i von nach hn he hw hL, _ =>
      blattG_ohneRuf (.shift t f' hτ i von nach hn he hw hL)
  | _, _, _, _, _, .regWrite r hk e, _ => blattG_ohneRuf (.regWrite r hk e)
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattG_ohneRuf (.transition r hk m hm hl maske bits)
  | _, _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattG_ohneRuf (.publish g e payload hp hw hL)
  | _, _, _, _, _, .advances m a h hs, _ => blattG_ohneRuf (.advances m a h hs)
  | _, _, _, _, _, .retires m s h a, _ => blattG_ohneRuf (.retires m s h a)
  | _, _, _, _, _, .ite _ t e, hs =>
      .ite _ _ _ (blockG_ohneRuf t hs.ite_inv.1) (blockG_ohneRuf e hs.ite_inv.2)
  | _, _, _, _, _, .onOption _ p a, hs =>
      .onOption _ _ _ (blockG_ohneRuf p hs.onOption_inv.1) (blockG_ohneRuf a hs.onOption_inv.2)
  | _, _, _, _, _, .onTag _ arms, hs => .onTag _ _ (armsG_ohneRuf arms hs.onTag_inv)
  | _, _, _, _, _, .onWhy _ arms, hs => .onWhy _ _ (grundG_ohneRuf arms hs.onGrund_inv)
  | _, _, _, _, _, .call .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .callInd .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .callIndElse .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .locks _ _ body, hs => .locks _ _ _ (blockG_ohneRuf body hs.locks_inv.2)
  | _, _, _, _, _, .breaking _ body, hs => .breaking _ _ (blockG_ohneRuf body hs.breaking_inv)
  | _, _, _, _, _, .traverse .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .consumeTraverse .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .retry .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .forever .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .axiomCall .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .axiomCallElse .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .ret e hΛ, _ => .ret e hΛ
  | _, _, _, _, _, .retWhy .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .retScoped .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .retWhyScoped .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .leave .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])
  | _, _, _, _, _, .next .., hs => absurd hs.art (by simp only [Stmt.gArt, Stmt.blattArt, Bool.false_eq_true, not_false_eq_true])

theorem blockG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'),
    BlockG A mr b → BlockOhneRuf b
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, .cons s rest, hb =>
      .cons _ _ (stmtG_ohneRuf s hb.cons_inv.1) (blockG_ohneRuf rest hb.cons_inv.2)
  | _, _, _, _, _, .bind _ rest, hb => .bind _ _ (blockG_ohneRuf rest hb.bind_inv)
  | _, _, _, _, _, .bindCall .., hb => by cases hb
  | _, _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, _, .bindCallIndElse .., hb => by cases hb
  | _, _, _, _, _, .bindCallElse .., hb => by cases hb
  | _, _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomElse .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomOpt .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomOptElse .., hb => by cases hb
  | _, _, _, _, _, .regRead _ _ rest, hb => .regRead _ _ _ (blockG_ohneRuf rest hb.regLies_inv)
  | _, _, _, _, _, .regReadElse _ _ _ sonst rest, hb =>
      .regReadElse _ _ _ _ _ (endG_ohneRuf sonst hb.regLiesElse_inv.2.2.1)
        (blockG_ohneRuf rest hb.regLiesElse_inv.2.1)
  | _, _, _, _, _, .awaits _ _ _ _ _ rest, hb =>
      .awaits _ _ _ _ _ _ (blockG_ohneRuf rest hb.awaits_inv)
  | _, _, _, _, _, .exchange _ _ _ _ rest, hb =>
      .exchange _ _ _ _ _ (blockG_ohneRuf rest hb.exchange_inv)
  | _, _, _, _, _, .narrow _ _ _ sonst rest, hb =>
      .narrow _ _ _ _ _ (endG_ohneRuf sonst hb.narrow_inv.2.2.1)
        (blockG_ohneRuf rest hb.narrow_inv.2.1)
  | _, _, _, _, _, .narrowRequired _ _ _ _, hb => by cases hb
  | _, _, _, _, _, .check _ sonst rest, hb =>
      .check _ _ _ (endG_ohneRuf sonst hb.pruefung_inv.2.2.1)
        (blockG_ohneRuf rest hb.pruefung_inv.2.1)
  | _, _, _, _, _, .float _ _ _ _ _ rest, hb =>
      .float _ _ _ _ _ _ (blockG_ohneRuf rest hb.gleit_inv)
  | _, _, _, _, _, .floatLit _ _ _ rest, hb =>
      .floatLit _ _ _ _ (blockG_ohneRuf rest hb.gleitLit_inv)
  | _, _, _, _, _, .floatOf _ _ _ rest, hb =>
      .floatOf _ _ _ _ (blockG_ohneRuf rest hb.gleitVon_inv)
  | _, _, _, _, _, .floatNarrow _ _ _ sonst rest, hb =>
      .floatNarrow _ _ _ _ _ (endG_ohneRuf sonst hb.gleitNarrow_inv.2.2.1)
        (blockG_ohneRuf rest hb.gleitNarrow_inv.2.1)

theorem endG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
    EndG A e → EndOhneRuf e
  | _, _, _, .ret e hΛ, _ => .ret e hΛ
  | _, _, _, .retWhy .., he => by cases he
  | _, _, _, .retScoped .., he => by cases he
  | _, _, _, .retWhyScoped .., he => by cases he
  | _, _, _, .leave .., he => by cases he
  | _, _, _, .next .., he => by cases he
  | _, _, _, .cons s rest, he =>
      .cons _ _ (stmtG_ohneRuf s he.cons_inv.1) (endG_ohneRuf rest he.cons_inv.2.1)
  | _, _, _, .bind _ rest, he => .bind _ _ (endG_ohneRuf rest he.bind_inv)
  | _, _, _, .narrowRequired _ _ _ _, he => by cases he

theorem armsG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs), ArmsG A mr arms → ArmsOhneRuf arms
  | _, _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, _, .cons b rest, ha =>
      .cons _ _ (blockG_ohneRuf b ha.cons_inv.1) (armsG_ohneRuf rest ha.cons_inv.2)

theorem grundG_ohneRuf {V : Vertrag D} {A : D.Lock → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), GrundArmsG A mr arms → GrundArmsOhneRuf arms
  | _, _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, _, .cons b rest, ha =>
      .cons _ _ (blockG_ohneRuf b ha.cons_inv.1) (grundG_ohneRuf rest ha.cons_inv.2)

end
/-- **TARGET A for any call handler.** A covered body is call-free, so the
    sequential run under ANY handler `R` (e.g. `rufAt P O passes fuel`, the
    one the program semantics and the Hoare rules use) is the run under
    `keinRuf`; `rufG_adaequat` applies verbatim. -/
theorem rufG_adaequat_R (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (spur : List (Ereignis D)) (log : List (RufEreignisF D)) {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ) (b : Endblock D (vertragVon D fn) false Γ Λ)
    (A : D.Lock → Prop) (hb : EndG A b)
    (hM : M.faeden f = ⟨caller :: rst, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (hnw : caller.wartend = false)
    (hΛ : HeldGenau Λ (offen spur))
    (hfrei : ∀ L, A L → RufFreiG M f L)
    (σ' : World D) (v : ErgVal D (vertragVon D fn).erg)
    (hexec : execEnd O passes R b (M.weltVon f) ρ = .zurueck σ' v) :
    ∃ M', RufLaufG P O passes f M M' ∧
      M'.faeden f = ⟨rst, caller, σ'.spur, RufEreignisF.rueck fn rho v s0 σ' :: log⟩ ∧
      M'.speicher = σ'.speicher ∧
      (∀ g, g ≠ f → M'.faeden g = M.faeden g) := by
  rw [endOhneRuf_Runabhaengig O passes R keinRuf b (endG_ohneRuf b hb)] at hexec
  exact rufG_adaequat P O passes M f fn rho s0 caller rst spur log ρ b A hb hM hnw hΛ hfrei σ' v hexec

end Gabbro.Grammatik
