/-
  File:      stage0/Stage0/Senke/Bild/Korrespondenz.lean
  Subject:   The correspondence between a running image and machine G (image theorem, piece T1, one thread).
             `RandG` is machine G at a statement boundary of the same body (thread `thr` runs the frame of `f`
             with the residue `.ende eb`, the same environment and the same world, `ZustandG`); `Rand` joins it
             with the image side `RandIR`: the world the image holds in memory IS the world of the machine.
             Two kinds of decomposed steps lead from a boundary to the next one:
             * `rand_schritt`: one statement of the G fragment (`StmtR`) that ends normally — the image by the
               statement's code, machine G by steps of `thr` alone (`endeConsOkR` with `stmtOkR`). Every compound
               statement of `StmtR` (`ite`, `onOption`, `onTag`, `onWhy`, `breaking`, `locks`, `traverse`, `retry`,
               `forever`, a `call` of an admitted callee) is ONE such step, with the block forms of `BlockR` inside;
             * `rand_bind`: a `let` binding of the end block (`.bind e rest`) — the image by the code of `e`,
               machine G by its step `endeBind`; the context grows by one variable.
             `Zerlegung` names the decomposed prefix of the body (its context may change along it); `ZerlegSchritt`
             one of its steps. `Korrespondenz` relates an image state inside a decomposed step to the machine at
             the boundary in front of it (G stutters inside a step). `korrespondenz_lauf`: every memory-only prefix
             of the image run from a corresponding boundary either corresponds to a machine `thr` reaches, or has
             passed the end of the decomposed prefix, whose boundary corresponds to a machine `thr` reaches.
-/
module
public import Stage0.Senke.Bild.Rand
public import Stage0.Senke.Bild.Lauf
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T6
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## Machine G at a boundary -/

/-- **Machine G at a statement boundary** of the body of `f`: thread `thr` runs the frame of `f` (entry environment
    `rho`, entry world `s0`) above `stapel`, with the residue `.ende eb`, the environment `ρ` and the world `σ`; its
    holdings tie `Λ`; no other thread holds a lock of `Agl` (the locks the body may take). -/
def RandG (thr : Faden) (stapel : List (RufRahmenG D)) (f : D.Fn) (rho : Env D (D.params f)) (s0 : World D)
    (Agl : D.Lock → Prop) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (eb : Endblock D (vertragVon D f) l Γ Λ)
    (M : RufMaschineG D) (σ : World D) (ρ : Env D Γ) : Prop :=
  (∃ log, ZustandG M thr stapel f rho s0 log ρ (.ende eb) σ) ∧ HeldB (vertragVon D f).boden Λ (offen σ.spur) ∧
    FreiA Agl M thr

/-- **One statement, machine G**: from the boundary in front of `s`, a statement of the G fragment whose sequential
    run ends normally, thread `thr` reaches by its own steps the boundary behind it, with the same world and
    environment as the sequential run. Calls are realised through `hRuf`. -/
theorem randG_schritt {P : Programm D} {O : Orakel D} {passes : Nat}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g} {Cg : D.Fn → Prop} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    (hRuf : RufOk P O passes thr Agl R Cg) {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D f) l Γ Λ Λ'} {rest : Endblock D (vertragVon D f) l Γ Λ'} {M : RufMaschineG D}
    {σ σ1 : World D} {ρ ρ1 : Env D Γ} (hs : StmtR Agl Cg mr s) (hex : execStmt O passes R s σ ρ = .ok σ1 ρ1)
    (h : RandG thr stapel f rho s0 Agl (.cons s rest) M σ ρ) :
    ∃ M', RufLaufG P O passes thr M M' ∧ RandG thr stapel f rho s0 Agl rest M' σ1 ρ1 := by
  obtain ⟨⟨log, hZ⟩, hΛ, hA⟩ := h
  obtain ⟨M', ext, hl, hZ', ho⟩ := endeConsOkR P O passes thr f stapel rho s0 Agl R Cg hRuf hs
    (stmtOkR P O passes thr f stapel rho s0 Agl R Cg hRuf s hs) σ σ1 ρ ρ1 hex M rest hZ hΛ hA
  refine ⟨M', hl, ⟨ext ++ log, hZ'⟩, ?_, hA.lauf hl⟩
  rw [ho]
  exact heldB_iff (fun L => s.held_iff L) hΛ

/-- Without callees in the fragment the call obligation is empty: every call-free statement of `StmtR` steps. -/
theorem rufOk_leer (P : Programm D) (O : Orakel D) (passes : Nat) (thr : Faden) (Agl : D.Lock → Prop)
    (R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g) :
    RufOk P O passes thr Agl R (fun _ => False) :=
  ⟨fun _ hC => (hC : False).elim, fun _ hC => (hC : False).elim⟩

/-- **One binding, machine G**: from the boundary in front of `let x = e; rest`, thread `thr` takes the step
    `endeBind` to the boundary of `rest`, with the world after the reads of `e` and the environment extended by the
    value of `e`. -/
theorem randG_bind {P : Programm D} {O : Orakel D} {passes : Nat} {thr : Faden}
    {stapel : List (RufRahmenG D)} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Endblock D (vertragVon D f) l (τ :: Γ) Λ} {M : RufMaschineG D} {σ : World D} {ρ : Env D Γ}
    (h : RandG thr stapel f rho s0 Agl (.bind e rest) M σ ρ) :
    ∃ M', RufLaufG P O passes thr M M' ∧
      RandG thr stapel f rho s0 Agl rest M' (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := by
  obtain ⟨⟨log, hZ⟩, hΛ, hA⟩ := h
  have hW := hZ.welt
  obtain ⟨M1, hs1, hZ1⟩ := w_endeBind (P := P) (O := O) (passes := passes) hZ.1 e rest ρ rfl hΛ.heldIn
  rw [hW] at hZ1
  exact ⟨M1, RufLaufG.einzeln hs1, ⟨log, hZ1⟩, heldB_lese e.orte hΛ, hA.lauf (RufLaufG.einzeln hs1)⟩

variable [Kern]

/-! ## Both sides -/

/-- **The correspondence at a statement boundary**: the image stands at the start of the code of `eb` (`RandIR`) and
    machine G at the residue `.ende eb` (`RandG`), with ONE world `σ` and ONE environment `ρ` for both. -/
def Rand (B : BodyFrame D) (thr : Faden) (stapel : List (RufRahmenG D)) (rho : Env D (D.params B.f))
    (s0 : World D) (Agl : D.Lock → Prop) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (eb : Endblock D (vertragVon D B.f) l Γ Λ) (pc : Runner.W) (m : Runner.Mem) (M : RufMaschineG D)
    (σ : World D) (ρ : Env D Γ) : Prop :=
  B.RandIR eb pc m σ ρ ∧ RandG thr stapel B.f rho s0 Agl eb M σ ρ

/-- **One statement, both sides**: a stuttering step of the simulation — the image runs the `n` instructions of
    `s`, thread `thr` runs its own steps, and the boundary behind `s` corresponds again. -/
theorem rand_schritt {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] (hB : B.Ok) {Cg : D.Fn → Prop}
    {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params B.f)} {s0 : World D}
    {Agl : D.Lock → Prop} (hRuf : RufOk B.P B.O B.passes thr Agl B.R Cg) {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {s : Stmt D (vertragVon D B.f) l Γ Λ Λ'} {rest : Endblock D (vertragVon D B.f) l Γ Λ'}
    {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D} {σ σ1 : World D} {ρ ρ1 : Env D Γ}
    (hs : StmtR Agl Cg mr s) (hex : execStmt B.O B.passes B.R s σ ρ = .ok σ1 ρ1)
    (h : Rand B thr stapel rho s0 Agl (.cons s rest) pc m M σ ρ) :
    ∃ (n : Nat) (m1 : Runner.Mem) (M' : RufMaschineG D),
      Star ⟨pc, B.fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * n), B.fp⟩ m1 ∧ AgreeW B.L B.fp B.lo B.K m m1 ∧
      RufLaufG B.P B.O B.passes thr M M' ∧
      Rand B thr stapel rho s0 Agl rest (pc + BitVec.ofNat 64 (16 * n)) m1 M' σ1 ρ1 := by
  obtain ⟨cr, cs, tr, ts, m1, _, _, s1, a1, hR1⟩ := BodyFrame.randIR_schritt hB h.1 hex
  obtain ⟨M', hl, hG⟩ := randG_schritt hRuf hs hex h.2
  exact ⟨cs.length, m1, M', s1, a1, hl, hR1, hG⟩

/-- **One binding, both sides**: the image runs the code of `e`, thread `thr` takes `endeBind`, and the boundary of
    `rest` corresponds again, with one world and one environment for both. -/
theorem rand_bind {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] (hB : B.Ok) {thr : Faden}
    {stapel : List (RufRahmenG D)} {rho : Env D (D.params B.f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Endblock D (vertragVon D B.f) l (τ :: Γ) Λ} {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D}
    {σ : World D} {ρ : Env D Γ} (h : Rand B thr stapel rho s0 Agl (.bind e rest) pc m M σ ρ) :
    ∃ (n : Nat) (m1 : Runner.Mem) (M' : RufMaschineG D),
      Star ⟨pc, B.fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * n), B.fp⟩ m1 ∧ AgreeW B.L B.fp B.lo B.K m m1 ∧
      RufLaufG B.P B.O B.passes thr M M' ∧
      Rand B thr stapel rho s0 Agl rest (pc + BitVec.ofNat 64 (16 * n)) m1 M' (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := by
  obtain ⟨ce, m1, s1, a1, hR1⟩ := BodyFrame.randIR_bind hB h.1
  obtain ⟨M', hl, hG⟩ := randG_bind (P := B.P) (O := B.O) (passes := B.passes) h.2
  exact ⟨ce.length, m1, M', s1, a1, hl, hR1, hG⟩

/-! ## The decomposed prefix and the correspondence inside it -/

/-- **One decomposed step** from the end block `eb` at `σ`, `ρ` to the end block `eb'` at `σ1`, `ρ1`: a statement
    that ends normally in the sequential semantics (`.cons s rest` to `rest`), or a `let` binding (`.bind e rest` to
    `rest`, as `execEnd` and machine G's `endeBind` take it). -/
inductive ZerlegSchritt (B : BodyFrame D) {l : Bool} :
    {Γ : Ctx} → {Λ : List (Res D)} → Endblock D (vertragVon D B.f) l Γ Λ → World D → Env D Γ →
    {Γ' : Ctx} → {Λ' : List (Res D)} → Endblock D (vertragVon D B.f) l Γ' Λ' → World D → Env D Γ' → Prop where
  | stmt {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D (vertragVon D B.f) l Γ Λ Λ')
      (rest : Endblock D (vertragVon D B.f) l Γ Λ') (σ σ1 : World D) (ρ ρ1 : Env D Γ)
      (hex : execStmt B.O B.passes B.R s σ ρ = .ok σ1 ρ1) :
      ZerlegSchritt B (.cons s rest) σ ρ rest σ1 ρ1
  | bind {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
      (rest : Endblock D (vertragVon D B.f) l (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
      ZerlegSchritt B (.bind e rest) σ ρ rest (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ)

/-- **The decomposed prefix of a body**: from `eb` at world `σ` and environment `ρ`, statements of the G fragment
    (`StmtR Agl Cg`) that end normally and `let` bindings, up to the end block `ebe` reached at `σe`, `ρe`. The
    context grows at every binding. -/
inductive Zerlegung (B : BodyFrame D) (Agl : D.Lock → Prop) (Cg : D.Fn → Prop) {l : Bool} :
    {Γ : Ctx} → {Λ : List (Res D)} → Endblock D (vertragVon D B.f) l Γ Λ → World D → Env D Γ →
    {Γe : Ctx} → {Λe : List (Res D)} → Endblock D (vertragVon D B.f) l Γe Λe → World D → Env D Γe → Prop where
  | halt {Γ : Ctx} {Λ : List (Res D)} (eb : Endblock D (vertragVon D B.f) l Γ Λ) (σ : World D) (ρ : Env D Γ) :
      Zerlegung B Agl Cg eb σ ρ eb σ ρ
  | schritt {Γ Γe : Ctx} {mr : Bool} {Λ Λ' Λe : List (Res D)} (s : Stmt D (vertragVon D B.f) l Γ Λ Λ')
      (rest : Endblock D (vertragVon D B.f) l Γ Λ') (ebe : Endblock D (vertragVon D B.f) l Γe Λe)
      (σ σ1 σe : World D) (ρ ρ1 : Env D Γ) (ρe : Env D Γe) (hs : StmtR Agl Cg mr s)
      (hex : execStmt B.O B.passes B.R s σ ρ = .ok σ1 ρ1) (hk : Zerlegung B Agl Cg rest σ1 ρ1 ebe σe ρe) :
      Zerlegung B Agl Cg (.cons s rest) σ ρ ebe σe ρe
  | bind {Γ Γe : Ctx} {Λ Λe : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
      (rest : Endblock D (vertragVon D B.f) l (τ :: Γ) Λ) (ebe : Endblock D (vertragVon D B.f) l Γe Λe)
      (σ σe : World D) (ρ : Env D Γ) (ρe : Env D Γe)
      (hk : Zerlegung B Agl Cg rest (σ.lese Λ e.orte) (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ)
        ebe σe ρe) :
      Zerlegung B Agl Cg (.bind e rest) σ ρ ebe σe ρe

/-- **Korrespondenz** of the image state `(t, m)` with the machine `M`: `(t, m)` lies inside a decomposed step
    (`ZerlegSchritt`: a statement that ends normally, or a binding) from `eb` to `eb'` — on a run from the boundary
    in front of the step, which corresponds to `M`, to the boundary behind it, which corresponds to a machine `M'`
    that `thr` reaches from `M`. The run of the whole step changes only the frame from `lo` on, the world and the
    lock words (`AgreeW`). The contexts in front of and behind the step are part of the existential. -/
def Korrespondenz (B : BodyFrame D) (thr : Faden) (stapel : List (RufRahmenG D)) (rho : Env D (D.params B.f))
    (s0 : World D) (Agl : D.Lock → Prop) (l : Bool) (t : T) (m : Runner.Mem) (M : RufMaschineG D) : Prop :=
  ∃ (Γ Γ' : Ctx) (Λ Λ' : List (Res D)) (eb : Endblock D (vertragVon D B.f) l Γ Λ)
    (eb' : Endblock D (vertragVon D B.f) l Γ' Λ') (pc : Runner.W) (mb m1 : Runner.Mem) (σ σ1 : World D)
    (ρ : Env D Γ) (ρ1 : Env D Γ') (n : Nat) (M' : RufMaschineG D),
    ZerlegSchritt B eb σ ρ eb' σ1 ρ1 ∧ Rand B thr stapel rho s0 Agl eb pc mb M σ ρ ∧
    Star ⟨pc, B.fp⟩ mb t m ∧ Star t m ⟨pc + BitVec.ofNat 64 (16 * n), B.fp⟩ m1 ∧
    AgreeW B.L B.fp B.lo B.K mb m1 ∧ RufLaufG B.P B.O B.passes thr M M' ∧
    Rand B thr stapel rho s0 Agl eb' (pc + BitVec.ofNat 64 (16 * n)) m1 M' σ1 ρ1

/-- **The small-step invariant (T1, one thread)**: let the image stand at a boundary that corresponds to `M`, in
    front of a decomposed prefix `Zerlegung … eb σ ρ ebe σe ρe`. Then every prefix of `n` memory-only image steps
    either lies inside a decomposed step and corresponds (`Korrespondenz`) to a machine that `thr` reaches from
    `M`, or has passed the boundary in front of `ebe`, which corresponds to a machine that `thr` reaches from `M`.
    The memory-only premise excludes the steps whose answer is not unique (system calls, floating requests). -/
theorem korrespondenz_lauf {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] (hB : B.Ok)
    {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {thr : Faden} {stapel : List (RufRahmenG D)}
    {rho : Env D (D.params B.f)} {s0 : World D} (hRuf : RufOk B.P B.O B.passes thr Agl B.R Cg)
    {l : Bool} {Γ Γe : Ctx} {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ}
    {ebe : Endblock D (vertragVon D B.f) l Γe Λe} {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe}
    (hk : Zerlegung B Agl Cg eb σ ρ ebe σe ρe) :
    ∀ {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D}, Rand B thr stapel rho s0 Agl eb pc m M σ ρ →
    ∀ {n : Nat} {t : T} {m' : Runner.Mem}, StarM n ⟨pc, B.fp⟩ m t m' →
      (∃ M', RufLaufG B.P B.O B.passes thr M M' ∧ Korrespondenz B thr stapel rho s0 Agl l t m' M') ∨
      (∃ (pce : Runner.W) (me : Runner.Mem) (Me : RufMaschineG D),
        Rand B thr stapel rho s0 Agl ebe pce me Me σe ρe ∧ RufLaufG B.P B.O B.passes thr M Me ∧
        ∃ k, StarM k ⟨pce, B.fp⟩ me t m') := by
  induction hk with
  | halt eb σ ρ =>
    intro pc m M hR n t m' hrun
    exact Or.inr ⟨pc, m, M, hR, RufLaufG.refl M, n, hrun⟩
  | schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs hex _ ih =>
    intro pc m M hR n t m' hrun
    obtain ⟨n1, m1, M1, s1, a1, hl1, hR1⟩ := rand_schritt hB hRuf hs hex hR
    rcases hrun.weiche s1 with hvor | ⟨k, hnach⟩
    · exact Or.inl ⟨M, RufLaufG.refl M, _, _, _, _, .cons s rest, rest, pc, m, m1, σ, σ1, ρ, ρ1, n1, M1,
        ZerlegSchritt.stmt (B := B) s rest σ σ1 ρ ρ1 hex, hR, hrun.star, hvor, a1, hl1, hR1⟩
    · rcases ih hR1 hnach with ⟨M', hl', hK'⟩ | ⟨pce, me, Me, hRe, hle, k', hk'⟩
      · exact Or.inl ⟨M', hl1.trans hl', hK'⟩
      · exact Or.inr ⟨pce, me, Me, hRe, hl1.trans hle, k', hk'⟩
  | bind e rest ebe σ σe ρ ρe _ ih =>
    intro pc m M hR n t m' hrun
    obtain ⟨n1, m1, M1, s1, a1, hl1, hR1⟩ := rand_bind hB hR
    rcases hrun.weiche s1 with hvor | ⟨k, hnach⟩
    · exact Or.inl ⟨M, RufLaufG.refl M, _, _, _, _, .bind e rest, rest, pc, m, m1, σ, _, ρ, _, n1, M1,
        ZerlegSchritt.bind (B := B) e rest σ ρ, hR, hrun.star, hvor, a1, hl1, hR1⟩
    · rcases ih hR1 hnach with ⟨M', hl', hK'⟩ | ⟨pce, me, Me, hRe, hle, k', hk'⟩
      · exact Or.inl ⟨M', hl1.trans hl', hK'⟩
      · exact Or.inr ⟨pce, me, Me, hRe, hl1.trans hle, k', hk'⟩

end Gabbro.Stage0.Senke.BildLauf
