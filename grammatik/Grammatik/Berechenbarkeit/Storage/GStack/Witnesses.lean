import Grammatik.Berechenbarkeit.Storage.GStack.Termination
import Grammatik.Bausteine.Arena.Struktur.ArenaDynZeuge
import Grammatik.Zielsatz.Kern.Akzeptiert

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses

open InvDynZeuge
open ArenaKette

abbrev Payload := FD.typ FA.tab FA.feld

def byte (n : Nat) (hn : n ≤ 255) : Wert FD Payload := ⟨n, by omega, by omega⟩
def seven : Wert FD Payload := byte 7 (by decide)
def zero : Wert FD Payload := byte 0 (by decide)

def initialEnv : Env FD [Payload, Payload] := .cons zero (.cons seven .nil)
def initialWorld : World FD := wd 0 4 4 nx0 rn0 rn0

def failure {Γ : Ctx} : Endblock FD FV false Γ [] := .ret .empty (List.Perm.refl [])

def fresh : Allocator FA FV false [Payload, Payload] [] :=
  Gabbro.Grammatik.Block.arenaAlloc FA.toArenaForm (.var (.there .here)) rfl fdarf rfl (fgdarf _) failure

def recycle : Allocator FA FV false [Payload, Payload] [] :=
  Gabbro.Grammatik.Block.freiNimm FA (.var (.there .here)) rfl fdarf rfl (fgdarf _) failure

/-- Original locals are sink=0, input=7. Pop saves the payload into the sink
before its two internal binders are removed, and after the cell has been freed. -/
def roundTrip (allocator : Allocator FA FV false [Payload, Payload] []) :
    Gabbro.Grammatik.Block FD FV false [Payload, Payload] [] [] :=
  .cons (.ite .tru (Block.tryPush .tru failure allocator LL LG rfl fdarf rfl (fgdarf _) .nil) .nil)
    (Block.popAndRelease LL LG rfl (fgdarf _) rfl fdarf rfl (fgdarf _) failure
      (.cons (.assignVar (.there (.there .here)) (.var .here)) .nil))

theorem empty_contents : Represents LL LG initialWorld [] := represents_empty rfl

theorem initial_free : FA.FreiOk initialWorld :=
  ⟨[], FreiForm.Kette.nil, .nil, by simp⟩

/-- Provider refusal executes the supplied continuation without allocating or
touching a stored payload, even though the finite arena has room. -/
theorem refused_push_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    execBlock O passes R
      (Block.tryPush (.not .tru) failure fresh LL LG rfl fdarf rfl (fgdarf _) .nil)
      initialWorld initialEnv = .zurueck initialWorld () := rfl

/-- An empty stack takes the ordinary failure branch before any payload read
or release. No successful pop is invented for the empty representation. -/
theorem empty_pop_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    execBlock O passes R
      (Block.popAndRelease LL LG rfl (fgdarf _) rfl fdarf rfl (fgdarf _) failure .nil)
      initialWorld initialEnv =
        .zurueck (initialWorld.lese [] [Sum.inr LG.g]) () := rfl

theorem reused_contents : Represents LL LG w0 [zero, zero] := by
  refine ⟨[2, 0], listeKette_w0, by decide, ?_, rfl⟩
  intro i hi
  apply (lebt_w0 i).mpr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> decide

/-- All premises of the allocator+link proof, including nonempty recycled
storage and a nonempty old stack, are instantiated jointly. -/
theorem reused_push_values_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    ∃ σ' k,
      (∀ {Λ'} (rest : Gabbro.Grammatik.Block FD FV false (Ty.index 4 :: [Payload, Payload]) [] Λ'),
        execBlock O passes R (Block.pushAllocated recycle LL LG rfl fdarf rfl (fgdarf _) rest) w0 initialEnv =
          (execBlock O passes R rest σ' (.cons k initialEnv)).schrumpf) ∧
      k.n = 1 ∧ LG.st σ' = 1 ∧ Represents LL LG σ' [seven, zero, zero] ∧ FA.FreiOk σ' := by
  apply push_values O passes R recycle LL LG rfl fdarf rfl (fgdarf _) w0 initialEnv seven [zero, zero] 1
    reused_contents
  exact reused_allocated O passes R FA (.there .here) rfl fdarf rfl (fgdarf _) failure w0 initialEnv
    freiOk_w0 (by decide)

/-- A complete stack cycle, checked by composition of the actual G execution
prefix theorems. The saved payload becomes an ordinary caller local. -/
theorem roundTrip_correct (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f)
    (allocator : Allocator FA FV false [Payload, Payload] []) (σ : World FD)
    (values : List (Wert FD Payload)) (slot : Int) (hr : Represents LL LG σ values)
    (ha : Allocated O passes R FA allocator σ initialEnv seven slot) :
    ∃ (σ' : World FD) (k : Wert FD (Ty.index 4)), execBlock O passes R (roundTrip allocator) σ initialEnv =
        .ok σ' (.cons seven (.cons seven .nil)) ∧
      Represents LL LG σ' values ∧ FA.FreiOk σ' ∧ ¬ FA.Lebt σ' k.n := by
  obtain ⟨σ1, k1, hpush, _, _, hr1, hf1⟩ :=
    push_values O passes R allocator LL LG rfl fdarf rfl (fgdarf _) σ initialEnv seven values slot hr ha
  have hstart : execBlock O passes R
      (Block.tryPush .tru failure allocator LL LG rfl fdarf rfl (fgdarf _) .nil) σ initialEnv = .ok σ1 initialEnv := by
    exact (allocationAttempt_available O passes R (.tru) failure
      (Block.pushAllocated allocator LL LG rfl fdarf rfl (fgdarf _) .nil) σ initialEnv rfl).trans (hpush .nil)
  let receive : Gabbro.Grammatik.Block FD FV false
      (Payload :: Ty.index 4 :: [Payload, Payload]) [] [] :=
    .cons (.assignVar (.there (.there .here)) (.var .here)) .nil
  obtain ⟨σ2, k2, hpop, _, hr2, hf2, hdead, _⟩ :=
    popAndRelease_values O passes R LL LG rfl (fgdarf _) rfl fdarf rfl (fgdarf _) failure
      receive σ1 initialEnv seven values hr1 hf1
  refine ⟨σ2, k2, ?_, hr2, hf2, hdead⟩
  have houter : execStmt O passes R
      (.ite .tru (Block.tryPush .tru failure allocator LL LG rfl fdarf rfl (fgdarf _) .nil) .nil)
      σ initialEnv = .ok σ1 initialEnv := by
    simpa only [execStmt, Expr.orte, World.lese, World.merke, List.map_nil,
      List.nil_append, eval, wahr?, ite_true] using hstart
  unfold roundTrip
  rw [execBlock, houter]
  dsimp only
  exact hpop.trans (by rfl)

theorem fresh_round_trip_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    ∃ (σ' : World FD) (k : Wert FD (Ty.index 4)), execBlock O passes R (roundTrip fresh) initialWorld initialEnv =
        .ok σ' (.cons seven (.cons seven .nil)) ∧
      Represents LL LG σ' [] ∧ FA.FreiOk σ' ∧ ¬ FA.Lebt σ' k.n := by
  apply roundTrip_correct O passes R fresh initialWorld [] 0 empty_contents
  exact fresh_allocated O passes R FA (.there .here) rfl fdarf rfl (fgdarf _) failure initialWorld initialEnv
    initial_free (by decide)

theorem reused_round_trip_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    ∃ (σ' : World FD) (k : Wert FD (Ty.index 4)), execBlock O passes R (roundTrip recycle) w0 initialEnv =
        .ok σ' (.cons seven (.cons seven .nil)) ∧
      Represents LL LG σ' [zero, zero] ∧ FA.FreiOk σ' ∧ ¬ FA.Lebt σ' k.n := by
  apply roundTrip_correct O passes R recycle w0 [zero, zero] 1 reused_contents
  exact reused_allocated O passes R FA (.there .here) rfl fdarf rfl (fgdarf _) failure w0 initialEnv
    freiOk_w0 (by decide)

/-- A whole finite G program, with normal local binding and no preloaded frames. -/
def body : Endblock FD FV false [] [] :=
  .bind (Expr.widen (by decide) (by decide) (.lit 7))
    (.bind (Expr.widen (by decide) (by decide) (.lit 0))
      (.cons (.ite .tru (roundTrip fresh) .nil) (.ret .empty (List.Perm.refl []))))

def program : Programm FD where
  invariante := fun i => i.elim
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => body

theorem program_exec_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    ∃ σ', execEnd O passes R body initialWorld .nil = .zurueck σ' () ∧
      Represents LL LG σ' [] ∧ FA.FreiOk σ' := by
  obtain ⟨σ', k, he, hr, hf, _⟩ := fresh_round_trip_zeuge O passes R
  refine ⟨σ', ?_, hr, hf⟩
  simp only [body, execEnd, execStmt, eval, Expr.orte, wahr?, ite_true,
    World.lese, World.merke, List.map_nil, List.nil_append, Zahl.weiter]
  erw [he]
  rfl

theorem program_termination_zeuge : klasse program [()] (fun _ => false) () = .endet := by decide

theorem program_accepted_zeuge :
    Akzeptiert program ⟨fun L => L.elim, fun L => L.elim⟩ [()] []
      [.inl (), .inr 0, .inr 1, .inr 2, .inr 3] [()] = true := by decide +kernel

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack.Witnesses
