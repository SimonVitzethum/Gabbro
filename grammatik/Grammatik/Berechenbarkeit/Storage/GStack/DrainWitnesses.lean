import Grammatik.Berechenbarkeit.Storage.GStack.Drain
import Grammatik.Berechenbarkeit.Storage.GStack.GrantWitnesses

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.DrainWitnesses

open InvDynZeuge Witnesses

def emptyFailure {Γ : Ctx} : Endblock FD FV true Γ [] := .ret .empty (List.Perm.refl [])

def loop {Γ : Ctx} : Stmt FD FV false Γ [] [] :=
  drain LL LG rfl (fgdarf _) rfl fdarf rfl (fgdarf _) emptyFailure ()

/-- A nonempty actual G stack requires exactly three loop passes: two pops
with real releases and the final successful logical guard check. -/
theorem exact_budget_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    (∃ σ' ρ', execStmt O passes R loop w0 initialEnv = .ok σ' ρ') ↔ 2 < passes :=
  drain_iff_budget O passes R LL LG rfl (fgdarf _) rfl fdarf rfl (fgdarf _) emptyFailure ()
    w0 initialEnv [zero, zero] reused_contents freiOk_w0

theorem drain_values_zeuge (O : Orakel FD) (n : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    ∃ σ', execStmt O (n + 3) R loop w0 initialEnv = .ok σ' initialEnv ∧
      Represents LL LG σ' [] ∧ FA.FreiOk σ' :=
  drain_bound O (n + 3) R LL LG rfl (fgdarf _) rfl fdarf rfl (fgdarf _) emptyFailure ()
    w0 initialEnv [zero, zero] reused_contents freiOk_w0 (by simp)

theorem insufficient_budget_zeuge (O : Orakel FD)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    ¬ ∃ σ' ρ', execStmt O 2 R loop w0 initialEnv = .ok σ' ρ' := by
  rw [exact_budget_zeuge]
  decide

/-- Even an empty initial stack must execute one guard check. -/
theorem empty_budget_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    (∃ σ' ρ', execStmt O passes R loop initialWorld initialEnv = .ok σ' ρ') ↔ 0 < passes :=
  drain_iff_budget O passes R LL LG rfl (fgdarf _) rfl fdarf rfl (fgdarf _) emptyFailure ()
    initialWorld initialEnv [] empty_contents initial_free

def body : Endblock FD FV false [] [] := .cons loop (.ret .empty (List.Perm.refl []))

def program : Programm FD where
  invariante := fun i => i.elim
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => body

/-- The existing structural classifier stays conditional. The separate
rank/trace theorem supplies the exact bound for represented input states. -/
theorem conditional_class_zeuge : klasse program [()] (fun _ => false) () = .bedingt := by decide

theorem core_accepted_zeuge :
    Akzeptiert program ⟨fun L => L.elim, fun L => L.elim⟩ [()] []
      [.inl (), .inr 0, .inr 1, .inr 2, .inr 3] [()] = true := by decide +kernel

theorem program_return_zeuge (O : Orakel FD)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    ∃ σ', execEnd O 3 R body w0 .nil = .zurueck σ' () ∧
      Represents LL LG σ' [] ∧ FA.FreiOk σ' := by
  obtain ⟨σ', he, hr, hf⟩ := drain_bound O 3 R LL LG rfl (fgdarf _) rfl fdarf rfl (fgdarf _) emptyFailure ()
    w0 (.nil) [zero, zero] reused_contents freiOk_w0 (by decide)
  refine ⟨σ', ?_, hr, hf⟩
  have hloop : execStmt O 3 R loop w0 (.nil : Env FD []) = .ok σ' .nil := he
  unfold body
  rw [execEnd, hloop]
  rfl

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.DrainWitnesses
