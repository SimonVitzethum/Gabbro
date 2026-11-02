module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T2.Teil1a
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section



namespace Gabbro.Grammatik.EZD

open Gabbro.Grammatik
variable {D : Deklaration}

/-! ## 3. The oracle arm: `axiomCall` writes stay inside the declared frame.

  `GutO` says the oracle answer's world differs from the entry world at most
  on carriers with `D.aschreibt/D.agschreibt = true`. Hence a slot of `t`
  with `D.aschreibt a t = false` survives any `axiomCall a` step.
  Proved via `axiomAntwort_gut` (the `Gut` package) rather than by unfolding
  `execStmt`: the `Rahmen` half is exactly the needed slot equality. -/

/-- The oracle frame keeps a non-written table slot, via the unconditional
    `Rahmen` conjunct of `GutO` (the trace clause is conditional and not
    needed here). -/
theorem axiomCall_slots_frame (O : Orakel D) (hO : GutO O) (a : D.Ax)
    (t : D.Tab) (ht : D.aschreibt a t = false)
    (sg : World D) (rho : Env D (D.aparams a)) (k : Int) (f : D.Feld t) :
    (O.wirkt a sg rho).1.slots t k f = sg.slots t k f := by
  -- project the `Rahmen` slot leg of `GutO` at `ht`.
  exact (hO a sg rho).1.1 t ht k f

/-! ## 4. Slot preservation per leaf shape: every non-recording leaf keeps `slots t`.

  Each lemma below takes the firing equation `hstep` for ONE statement form
  and concludes `σ'.slots t k f = σ.slots t k f` for every table `t`. All are
  used by their proofs (rule 3): the two global-writing forms (`assignGlob`,
  `publish`) by the step lemma's global case, the rest by the compound-case
  analysis there. Forms that write a table slot (`assignSlot`, `assignDurch`,
  `uebergang`, `schreibBytes`) are NOT here: they record their event (§2). -/

/-- `assignGlob` writes a global: every table slot rides along. -/
theorem assignGlob_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {g : D.Glob} {e : Expr D Γ Λ (D.gtyp g)}
    {hw : V.gschreibt g = true} {hL : gdarf D g Λ}
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignGlob (V := V) (l := l) g e hw hL) sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  have hcomp : (execStmt O passes keinRuf
      (Stmt.assignGlob (V := V) (l := l) g e hw hL) sg rho).welt =
      some ((sg.lese Λ e.orte).schreibGlob g Λ
        (eval (sg.lese Λ e.orte) e (sg.lese Λ e.orte) rho)) := rfl
  rw [hcomp] at hstep
  have hsg' : sg' = ((sg.lese Λ e.orte).schreibGlob g Λ
      (eval (sg.lese Λ e.orte) e (sg.lese Λ e.orte) rho)) :=
    Option.some_inj.mp hstep.symm
  rw [hsg']
  rfl

/-- `publish` writes a global: every table slot rides along. -/
theorem publish_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {g : D.Glob} {e : Expr D Γ Λ (D.gtyp g)} {payload : List D.Glob}
    {hp : payload = D.nutzlast g} {hw : V.gschreibt g = true} {hL : gdarf D g Λ}
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.publish (V := V) (l := l) g e payload hp hw hL) sg rho).welt
      = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  have hcomp : (execStmt O passes keinRuf
      (Stmt.publish (V := V) (l := l) g e payload hp hw hL) sg rho).welt =
      some ((sg.lese Λ e.orte).schreibGlob g Λ
        (eval (sg.lese Λ e.orte) e (sg.lese Λ e.orte) rho)) := rfl
  rw [hcomp] at hstep
  have hsg' : sg' = ((sg.lese Λ e.orte).schreibGlob g Λ
      (eval (sg.lese Λ e.orte) e (sg.lese Λ e.orte) rho)) :=
    Option.some_inj.mp hstep.symm
  rw [hsg']
  rfl

/-- `assignVar` touches only the environment: every table slot rides along. -/
theorem assignVar_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {x : Var Γ τ} {e : Expr D Γ Λ τ}
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignVar (V := V) (l := l) x e) sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  have hcomp : (execStmt O passes keinRuf
      (Stmt.assignVar (V := V) (l := l) x e) sg rho).welt =
      some (sg.lese Λ e.orte) := rfl
  rw [hcomp] at hstep
  have hsg' : sg' = sg.lese Λ e.orte := Option.some_inj.mp hstep.symm
  rw [hsg']
  rfl

/-- `regSchreib` touches only the device: every table slot rides along. -/
theorem regSchreib_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : D.Reg} {hk : (D.rklasse r).schreibbar = true} {e : Expr D Γ Λ (D.rtyp r)}
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.regWrite (V := V) (l := l) r hk e) sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  have hcomp : (execStmt O passes keinRuf
      (Stmt.regWrite (V := V) (l := l) r hk e) sg rho).welt =
      some (sg.lese Λ e.orte) := rfl
  rw [hcomp] at hstep
  have hsg' : sg' = sg.lese Λ e.orte := Option.some_inj.mp hstep.symm
  rw [hsg']
  rfl

/-- `ret` only reads: every table slot rides along. -/
theorem ret_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {e : ErgExpr D Γ Λ V.erg} {hΛ : Λ.Perm V.ende}
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.ret (V := V) (l := l) e hΛ) sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  have hcomp : (execStmt O passes keinRuf
      (Stmt.ret (V := V) (l := l) e hΛ) sg rho).welt =
      some (sg.lese Λ e.orte) := rfl
  rw [hcomp] at hstep
  have hsg' : sg' = sg.lese Λ e.orte := Option.some_inj.mp hstep.symm
  rw [hsg']
  rfl

/-! ## 5. Identity leaves: `transition`, `advances`, `retires`, `retGrund`,
    `leave`, `next` compute `.ok/.leave/.next` of the entry world or `σ`
    itself; every table slot rides along by one substitution. -/

/-- `transition` keeps every table slot (device-only step). -/
theorem transition_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : D.Reg} {hk : (D.rklasse r).schreibbar = true} {m : D.Reg}
    {hm : D.spiegel r = some m} {hl : (D.rklasse m).lesbar = true}
    {maske bits : Int}
    (s : Stmt D V l Γ Λ Λ)
    (hs : s = Stmt.transition (V := V) (l := l) r hk m hm hl maske bits)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl

end Gabbro.Grammatik.EZD
