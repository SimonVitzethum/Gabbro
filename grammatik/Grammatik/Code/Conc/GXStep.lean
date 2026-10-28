import Grammatik.Code.Conc.Thread
import Grammatik.Code.Conc.Shared
import Grammatik.Code.Refine.StmtOk

/-
  File:      Grammatik/Code/Conc/GXStep.lean
  Subject:   TRACK L, PHASE L3 -- THE SIMULATION OF A MACHINE-GX STEP OF A STATEMENT BY STEPS OF THE THREAD MACHINE.

  A GX step of thread `u` that runs a statement `s` to a normal end (`RufSchrittGX` over the `blatt`/`dannBlatt` steps
  of G, whose `execStmt` outcome is `ok σ' ρ'`) is a G step on a PRESENTED memory `sp0` (it agrees with the machine's
  memory `sp` outside the shared atomics `Tg`); the successor memory `sp'` agrees with `σ'` outside `Tg`
  (`Speichermodell/Atomar/AtomarLauf.lean`, `gx_aussen`). `stmt_gx` says: if the shared IR memory represents `sp` and
  thread `u` stands at the entry of the lowering of `s`, then the thread machine reaches, with ONLY thread `u` moving,
  a state in which `u` stands at the continuation, the shared memory represents `sp'`, the locals of `u` are
  `ρ'` and every other thread is where it was. The proof is `lowerS_ok` (any statement, every memory-model interface)
  plus the three representation transfers of `Conc/Present.lean`; nothing about the statement is redone.

  `envRep_other`: another thread's locals survive the run (the frame `Fr` keeps every block that is no table, no
  global and no cell of the running thread's locals).

  WHAT THIS IS NOT: a simulation of every G step. The steps that unfold a compound (`ite`, `match`, loops, `locks`)
  and the call steps move the G residue, not the memory; their correspondence with an IR position (the label the
  lowering of the continuation starts at) is the structural half of the simulation and is open (PLAN 9a). The
  direction is the forward one used throughout Track L: every GX step is MATCHED by IR steps; that every IR
  interleaving is covered by a GX run needs a reduction argument (a lowered statement touches shared memory in one
  access at most, except a shared atomic's) and is open too.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang RufAusgang Speicher TraegerGleich
  Ereignis execStmt)

variable {D : Deklaration} {V : Vertrag D}

/-- `Rep` does not see the trace: a memory-only world and the world it came from are represented alike. -/
theorem rep_welt {lay : Layout D} {σ : World D} {m : Mem} (tr : List (Ereignis D)) (h : Rep lay σ m) :
    Rep lay (σ.speicher.welt tr) m :=
  rep_agree (σ := σ) (σ' := σ.speicher.welt tr) (fun _ _ _ => rfl) (fun _ _ => rfl) h

/-- **Another thread's locals survive a run of this thread**: they are blocks that existed and are none of this
    thread's cells. -/
theorem envRep_other {lay : Layout D} {cenv cenv' : List Reg} {r0 : Nat} {m m' : Mem} {rs rs' rsv : Regs}
    {Γ' : Ctx} (ρv : Env D Γ') (hw : m.Wf) (hF : Fr lay cenv r0 m rs m' rs')
    (hE : EnvRep lay rsv m cenv' ρv)
    (hdis : ∀ r ∈ cenv', ∀ b, rsv r = some (.ptr b 0) → ¬ Own cenv rs b) : EnvRep lay rsv m' cenv' ρv :=
  envRep_load cenv' ρv (fun r hr b hb hf o t v hl =>
    hF.2.2 b hf (envRep_blocks_lt hw cenv' ρv hE r hr b hb) (hdis r hr b hb) o t v hl) hE

/-- **A GX step of a statement is matched by steps of the thread machine.** -/
theorem stmt_gx (lay : Layout D) (hL : LayoutOk lay) {Tg : D.Tab ⊕ D.Glob → Prop} (hT : TgShared lay Tg)
    (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Gabbro.Grammatik.Stmt D V l Γ Λ Λ')
    (lb k : Lbl) (st st' : St) (blks : List Block) (h : lowerS lay cenv lv s lb k st = some (blks, st'))
    (M : Modl) (S : Sees) (fn : Nat) (hM : InM M fn blks) (hk : KOk M fn k) (hlv : LvOk M fn lv)
    (hFn : FnOk lay M) (hCall : CallRef lay M S R)
    (T : TM) (u : Nat) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hth : T.th u = .run ⟨fn, lb, 0, rs, dst⟩ ks)
    (sp sp0 sp' : Speicher D) (tr : List (Ereignis D))
    (hR : Rep lay (sp.welt []) T.m) (hpres : ∀ c, ¬ Tg c → TraegerGleich sp0 sp c)
    (ρ : Env D Γ) (hE : EnvRep lay rs T.m cenv ρ) (hW : WfL lay T.m) (hc : ∀ x ∈ cenv, x < st.r)
    (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes R s (sp0.welt tr) ρ = Ausgang.ok σ' ρ')
    (hsucc : ∀ c, ¬ Tg c → TraegerGleich sp' σ'.speicher c) :
    ∃ (T' : TM) (rs' : Regs), TReach M S T T' ∧ T'.th u = .run ⟨fn, k, 0, rs', dst⟩ ks ∧
      (∀ v, v ≠ u → T'.th v = T.th v) ∧ Rep lay (sp'.welt []) T'.m ∧ EnvRep lay rs' T'.m cenv ρ' ∧ WfL lay T'.m ∧
      Fr lay cenv st.r T.m rs T'.m rs' := by
  have hR0 : Rep lay (sp0.welt tr) T.m := rep_presented hT hpres hR
  have hok := lowerS_ok lay hL cenv lv O passes R s lb k st st' blks h M S fn hM hk hlv hFn hCall
    (sp0.welt tr) ρ T.m rs ks dst hR0 hE hW hc
  rw [hstep] at hok
  obtain ⟨m', rs', hreach, ⟨hRp, hEp, hWp, _⟩, hF⟩ := hok
  have hcfg : T.cfg u = .run T.m ⟨fn, lb, 0, rs, dst⟩ ks := by simp only [TM.cfg, hth]
  refine ⟨T.upd u (.run m' ⟨fn, k, 0, rs', dst⟩ ks), rs', treach_solo hreach T hcfg, ?_, ?_, ?_, hEp, hWp, hF⟩
  · simp only [TM.upd, ↓reduceIte]
  · intro v hv
    exact upd_other T _ hv
  · exact rep_successor hT hsucc (rep_welt [] hRp)

end Gabbro.Code.Lower
