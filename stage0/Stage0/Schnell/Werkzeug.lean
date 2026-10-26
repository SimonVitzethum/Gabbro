/-
  File:      stage0/Stage0/Schnell/Werkzeug.lean
  Subject:   Tools of the simulation lemmas (`Schnell/Sim/*.lean`): expressions evaluated over memories only
             (`evalS`; `eval_S` turns every evaluation into one, so the premises of a rule over the fast and over the
             machine's worlds become the same statement), the memory of the worlds a rule builds, and the tactic
             `paar` that pairs those worlds.
-/
import Stage0.Schnell.Normal

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- An expression over two memories (entry and current). -/
def evalS {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (S₀ S : Speicher D) (e : Expr D Γ Λ τ) (ρ : Env D Γ) : Wert D τ :=
  eval (S₀.welt []) e (S.welt []) ρ

theorem eval_S {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (σ₀ σ : World D) (e : Expr D Γ Λ τ) (ρ : Env D Γ) :
    eval σ₀ e σ ρ = evalS σ₀.speicher σ.speicher e ρ :=
  eval_spurfrei e σ₀ (σ₀.speicher.welt []) σ (σ.speicher.welt []) rfl rfl rfl rfl ρ

/-- Arguments over two memories. -/
def evalArgsS {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} (S₀ S : Speicher D) (args : Args D Γ Λ τs) (ρ : Env D Γ) :
    Env D τs :=
  evalArgs (S₀.welt []) args (S.welt []) ρ

theorem evalArgs_S {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} (σ₀ σ : World D) (args : Args D Γ Λ τs)
    (ρ : Env D Γ) : evalArgs σ₀ args σ ρ = evalArgsS σ₀.speicher σ.speicher args ρ := by
  induction args with
  | nil => rfl
  | cons e rest ih =>
    simp only [evalArgsS, evalArgs] at ih ⊢
    rw [ih, eval_spurfrei e σ₀ (σ₀.speicher.welt []) σ (σ.speicher.welt []) rfl rfl rfl rfl ρ]

/-- A result expression over two memories. -/
def evalErgS {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} (S₀ S : Speicher D) (x : ErgExpr D Γ Λ e) (ρ : Env D Γ) :
    ErgVal D e :=
  evalErg (S₀.welt []) x (S.welt []) ρ

theorem evalErg_S {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} (σ₀ σ : World D) (x : ErgExpr D Γ Λ e)
    (ρ : Env D Γ) : evalErg σ₀ x σ ρ = evalErgS σ₀.speicher σ.speicher x ρ := by
  cases x with
  | empty => rfl
  | val e => exact eval_spurfrei e σ₀ (σ₀.speicher.welt []) σ (σ.speicher.welt []) rfl rfl rfl rfl ρ

theorem speicher_lese (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    (σ.lese Λ os).speicher = σ.speicher := rfl
theorem speicher_fragt (σ : World D) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : (σ.fragt q).speicher = σ.speicher := rfl
theorem speicher_merke (σ : World D) (es : List (Ereignis D)) : (σ.merke es).speicher = σ.speicher := rfl
theorem speicher_nimmt (σ : World D) (L : D.Lock) : (σ.nimmt L).speicher = σ.speicher := rfl
theorem speicher_gibt (σ : World D) (L : D.Lock) : (σ.gibt L).speicher = σ.speicher := rfl
theorem speicher_weltVon (M : RufMaschineG D) (g : Faden) : (M.weltVon g).speicher = M.speicher := by
  cases M
  rfl
theorem speicher_normal (w : World D) (M : RufMaschineG D) : (normal w M).speicher = M.speicher := rfl

/-- What turns a premise over the fast worlds into the premise over the machine's worlds. -/
macro "sim_simp" : tactic => `(tactic| simp only [offen_normal, rufFreiG_normal, eval_S, evalArgs_S, evalErg_S,
  speicher_lese, speicher_fragt, speicher_merke, speicher_nimmt, speicher_gibt, speicher_weltVon, speicher_normal]
  at *)

/-- Pairs the worlds a rule builds from the thread's world of the normal form and of the machine. -/
macro "paar" : tactic => `(tactic| repeat (first
  | assumption
  | exact paar_normal _ _
  | refine Paar.lese (schwanz_normal _ _) ?_ _ _
  | refine Paar.fragt ?_ _
  | refine Paar.nimmt (schwanz_normal _ _) ?_ _
  | refine Paar.gibt ?_ _
  | refine Paar.merke ?_ _
  | refine Paar.schreibSlot (schwanz_normal _ _) ?_ _ _ _ _ _
  | refine Paar.schreibGlob (schwanz_normal _ _) ?_ _ _ _))

/-- Closes a goal of a simulation lemma: a premise of the machine's rule from the fast one, a memory, frames or a
    trace of the two results. -/
macro "sim_ziel" : tactic => `(tactic| first
  | rfl
  | exact stapel_normal _ _
  | (simp only [List.map_map]; rfl)
  | (simp only [normal, fadenNormal, List.map_cons, List.map_map]; rfl)
  | assumption
  | exact (List.nil_append _).symm
  | exact List.singleton_append.symm
  | (apply Paar.speicher; assumption)
  | (apply Paar.speicher; paar; done)
  | (apply Paar.neu_eq' (by assumption); paar; done)
  | (sim_simp; assumption)
  | (sim_simp; rfl)
  | (simp only [offen_normal, eval_S, evalArgs_S, evalErg_S, speicher_lese, speicher_fragt, speicher_merke,
      speicher_nimmt, speicher_gibt, speicher_weltVon, speicher_normal, RufRahmenG.ohne]; done))

end Gabbro.Stage0
