/-
  File:      stage0/Stage0/Senke/Bild/Ruf/KorrespondenzL.lean
  Subject:   **The correspondence of the image with machine G, with calls** (package P3 of the closed calls of the
             image theorem, part 2). `Rand` ties ONE world to both sides; across a call the image (handler `rufAt`)
             and machine G (body run `rufRumpf`) reach worlds that differ by the contract READ events of `rufAt`.
             `RandL` keeps the image side exact (`RandIR` at the sequential world, which IS the world in the
             image's memory) and takes machine G up to read events (`RandGL`). `randL_schritt`/`randL_bind`,
             `KorrespondenzL` and `korrespondenzL_lauf` are `rand_schritt`/`rand_bind`, `Korrespondenz` and
             `korrespondenz_lauf` with `RandL` for `Rand` and the call obligation `RufOkGleich` for `RufOk`, under
             the named oracle property `LeseblindOK`. A call of an admitted callee is ONE decomposed step, as before.
             The exact forms stay (`Korrespondenz.lean`); an exact boundary is one up to read events (`randL_von`),
             and so is an exact correspondence (`korrespondenzL_von`).
-/
module
public import Stage0.Senke.Bild.Ruf.RufOkGleich
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration}

variable [Kern]

/-! ## Both sides, machine G up to read events -/

/-- **The correspondence at a statement boundary, machine G up to read events**: the image stands at the start of the
    code of `eb` with the world `σ` in memory (`RandIR`), and machine G at the residue `.ende eb` at a world `≈` to
    `σ`, with the same environment `ρ` (`RandGL`). -/
def RandL (B : BodyFrame D) (thr : Faden) (stapel : List (RufRahmenG D)) (rho : Env D (D.params B.f))
    (s0 : World D) (Agl : D.Lock → Prop) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (eb : Endblock D (vertragVon D B.f) l Γ Λ) (pc : Runner.W) (m : Runner.Mem) (M : RufMaschineG D)
    (σ : World D) (ρ : Env D Γ) : Prop :=
  B.RandIR eb pc m σ ρ ∧ RandGL thr stapel B.f rho s0 Agl eb M σ ρ

/-- An exact boundary is one up to read events. -/
theorem randL_von {B : BodyFrame D} {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params B.f)}
    {s0 : World D} {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {eb : Endblock D (vertragVon D B.f) l Γ Λ} {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D}
    {σ : World D} {ρ : Env D Γ} (h : Rand B thr stapel rho s0 Agl eb pc m M σ ρ) :
    RandL B thr stapel rho s0 Agl eb pc m M σ ρ :=
  ⟨h.1, randGL_von h.2⟩

/-- **One statement, both sides, with calls**: the image runs the code of `s` (a call of an admitted callee
    included), thread `thr` runs its own steps, and the boundary behind `s` corresponds again, machine G up to read
    events. -/
theorem randL_schritt {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] [LeseblindOK B.O] (hB : B.Ok)
    {Cg : D.Fn → Prop} {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params B.f)} {s0 : World D}
    {Agl : D.Lock → Prop} (hRuf : RufOkGleich B.P B.O B.passes thr Agl B.R Cg) {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {s : Stmt D (vertragVon D B.f) l Γ Λ Λ'} {rest : Endblock D (vertragVon D B.f) l Γ Λ'}
    {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D} {σ σ1 : World D} {ρ ρ1 : Env D Γ}
    (hs : StmtR Agl Cg mr s) (hex : execStmt B.O B.passes B.R s σ ρ = .ok σ1 ρ1)
    (h : RandL B thr stapel rho s0 Agl (.cons s rest) pc m M σ ρ) :
    ∃ (n : Nat) (m1 : Runner.Mem) (M' : RufMaschineG D),
      Star ⟨pc, B.fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * n), B.fp⟩ m1 ∧ AgreeW B.L B.fp B.lo B.K m m1 ∧
      RufLaufG B.P B.O B.passes thr M M' ∧
      RandL B thr stapel rho s0 Agl rest (pc + BitVec.ofNat 64 (16 * n)) m1 M' σ1 ρ1 := by
  obtain ⟨cr, cs, tr, ts, m1, _, _, s1, a1, hR1⟩ := BodyFrame.randIR_schritt hB h.1 hex
  obtain ⟨M', hl, hG⟩ := randGL_schritt (leseblind_von B.O) hRuf hs hex h.2
  exact ⟨cs.length, m1, M', s1, a1, hl, hR1, hG⟩

/-- **One binding, both sides**: the image runs the code of `e`, thread `thr` takes `endeBind`, and the boundary of
    `rest` corresponds again, machine G up to read events. -/
theorem randL_bind {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] (hB : B.Ok) {thr : Faden}
    {stapel : List (RufRahmenG D)} {rho : Env D (D.params B.f)} {s0 : World D} {Agl : D.Lock → Prop}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Endblock D (vertragVon D B.f) l (τ :: Γ) Λ} {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D}
    {σ : World D} {ρ : Env D Γ} (h : RandL B thr stapel rho s0 Agl (.bind e rest) pc m M σ ρ) :
    ∃ (n : Nat) (m1 : Runner.Mem) (M' : RufMaschineG D),
      Star ⟨pc, B.fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * n), B.fp⟩ m1 ∧ AgreeW B.L B.fp B.lo B.K m m1 ∧
      RufLaufG B.P B.O B.passes thr M M' ∧
      RandL B thr stapel rho s0 Agl rest (pc + BitVec.ofNat 64 (16 * n)) m1 M' (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := by
  obtain ⟨ce, m1, s1, a1, hR1⟩ := BodyFrame.randIR_bind hB h.1
  obtain ⟨M', hl, hG⟩ := randGL_bind (P := B.P) (O := B.O) (passes := B.passes) h.2
  exact ⟨ce.length, m1, M', s1, a1, hl, hR1, hG⟩

/-! ## The correspondence inside a decomposed step -/

/-- **KorrespondenzL**: `Korrespondenz` with machine G up to read events at both boundaries of the decomposed step
    (`RandL` for `Rand`). -/
def KorrespondenzL (B : BodyFrame D) (thr : Faden) (stapel : List (RufRahmenG D)) (rho : Env D (D.params B.f))
    (s0 : World D) (Agl : D.Lock → Prop) (l : Bool) (t : T) (m : Runner.Mem) (M : RufMaschineG D) : Prop :=
  ∃ (Γ Γ' : Ctx) (Λ Λ' : List (Res D)) (eb : Endblock D (vertragVon D B.f) l Γ Λ)
    (eb' : Endblock D (vertragVon D B.f) l Γ' Λ') (pc : Runner.W) (mb m1 : Runner.Mem) (σ σ1 : World D)
    (ρ : Env D Γ) (ρ1 : Env D Γ') (n : Nat) (M' : RufMaschineG D),
    ZerlegSchritt B eb σ ρ eb' σ1 ρ1 ∧ RandL B thr stapel rho s0 Agl eb pc mb M σ ρ ∧
    Star ⟨pc, B.fp⟩ mb t m ∧ Star t m ⟨pc + BitVec.ofNat 64 (16 * n), B.fp⟩ m1 ∧
    AgreeW B.L B.fp B.lo B.K mb m1 ∧ RufLaufG B.P B.O B.passes thr M M' ∧
    RandL B thr stapel rho s0 Agl eb' (pc + BitVec.ofNat 64 (16 * n)) m1 M' σ1 ρ1

/-- An exact correspondence is one up to read events. -/
theorem korrespondenzL_von {B : BodyFrame D} {thr : Faden} {stapel : List (RufRahmenG D)}
    {rho : Env D (D.params B.f)} {s0 : World D} {Agl : D.Lock → Prop} {l : Bool} {t : T} {m : Runner.Mem}
    {M : RufMaschineG D} (h : Korrespondenz B thr stapel rho s0 Agl l t m M) :
    KorrespondenzL B thr stapel rho s0 Agl l t m M := by
  obtain ⟨Γ, Γ', Λ, Λ', eb, eb', pc, mb, m1, σ, σ1, ρ, ρ1, n, M', hz, hR, h1, h2, ha, hl, hR'⟩ := h
  exact ⟨Γ, Γ', Λ, Λ', eb, eb', pc, mb, m1, σ, σ1, ρ, ρ1, n, M', hz, randL_von hR, h1, h2, ha, hl,
    randL_von hR'⟩

/-- **The small-step invariant with calls (T1, one thread)**: `korrespondenz_lauf` with the call obligation up to
    read events (`RufOkGleich`, which `rufAt` keeps at every depth for the callees admitted there,
    `rufOk_gleich_tief`) and machine G up to read events. From a boundary that corresponds to `M`, in front of a
    decomposed prefix, every prefix of `n` memory-only image steps either lies inside a decomposed step and
    corresponds to a machine that `thr` reaches from `M`, or has passed the boundary in front of `ebe`, which
    corresponds to a machine that `thr` reaches from `M`. -/
theorem korrespondenzL_lauf {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] [LeseblindOK B.O] (hB : B.Ok)
    {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {thr : Faden} {stapel : List (RufRahmenG D)}
    {rho : Env D (D.params B.f)} {s0 : World D} (hRuf : RufOkGleich B.P B.O B.passes thr Agl B.R Cg)
    {l : Bool} {Γ Γe : Ctx} {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ}
    {ebe : Endblock D (vertragVon D B.f) l Γe Λe} {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe}
    (hk : Zerlegung B Agl Cg eb σ ρ ebe σe ρe) :
    ∀ {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D}, RandL B thr stapel rho s0 Agl eb pc m M σ ρ →
    ∀ {n : Nat} {t : T} {m' : Runner.Mem}, StarM n ⟨pc, B.fp⟩ m t m' →
      (∃ M', RufLaufG B.P B.O B.passes thr M M' ∧ KorrespondenzL B thr stapel rho s0 Agl l t m' M') ∨
      (∃ (pce : Runner.W) (me : Runner.Mem) (Me : RufMaschineG D),
        RandL B thr stapel rho s0 Agl ebe pce me Me σe ρe ∧ RufLaufG B.P B.O B.passes thr M Me ∧
        ∃ k, StarM k ⟨pce, B.fp⟩ me t m') := by
  induction hk with
  | halt eb σ ρ =>
    intro pc m M hR n t m' hrun
    exact Or.inr ⟨pc, m, M, hR, RufLaufG.refl M, n, hrun⟩
  | schritt s rest ebe σ σ1 σe ρ ρ1 ρe hs hex _ ih =>
    intro pc m M hR n t m' hrun
    obtain ⟨n1, m1, M1, s1, a1, hl1, hR1⟩ := randL_schritt hB hRuf hs hex hR
    rcases hrun.weiche s1 with hvor | ⟨k, hnach⟩
    · exact Or.inl ⟨M, RufLaufG.refl M, _, _, _, _, .cons s rest, rest, pc, m, m1, σ, σ1, ρ, ρ1, n1, M1,
        ZerlegSchritt.stmt (B := B) s rest σ σ1 ρ ρ1 hex, hR, hrun.star, hvor, a1, hl1, hR1⟩
    · rcases ih hR1 hnach with ⟨M', hl', hK'⟩ | ⟨pce, me, Me, hRe, hle, k', hk'⟩
      · exact Or.inl ⟨M', hl1.trans hl', hK'⟩
      · exact Or.inr ⟨pce, me, Me, hRe, hl1.trans hle, k', hk'⟩
  | bind e rest ebe σ σe ρ ρe _ ih =>
    intro pc m M hR n t m' hrun
    obtain ⟨n1, m1, M1, s1, a1, hl1, hR1⟩ := randL_bind hB hR
    rcases hrun.weiche s1 with hvor | ⟨k, hnach⟩
    · exact Or.inl ⟨M, RufLaufG.refl M, _, _, _, _, .bind e rest, rest, pc, m, m1, σ, _, ρ, _, n1, M1,
        ZerlegSchritt.bind (B := B) e rest σ ρ, hR, hrun.star, hvor, a1, hl1, hR1⟩
    · rcases ih hR1 hnach with ⟨M', hl', hK'⟩ | ⟨pce, me, Me, hRe, hle, k', hk'⟩
      · exact Or.inl ⟨M', hl1.trans hl', hK'⟩
      · exact Or.inr ⟨pce, me, Me, hRe, hl1.trans hle, k', hk'⟩

#print axioms korrespondenzL_lauf

end Gabbro.Stage0.Senke.BildLauf
