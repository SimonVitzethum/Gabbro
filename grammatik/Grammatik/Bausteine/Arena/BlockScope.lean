module

public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Kern.Syntax.Satz.T2.Teil1b
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.ArenaForm

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- The cursor at entry delimits this block's allocations from those
    already live outside the block. Restoration is one ordinary store. -/
def restoreScope (arena : ArenaForm D) (held : List (Res D)) (entry : World D)
    (exit : Ausgang V l Γ) : Ausgang V l Γ :=
  exit.mapWelt fun world => world.schreibGlob arena.zaehl held (entry.globs arena.zaehl)

/-- Normal completion, leave, next, value return and reason return all
    restore the checkpoint. Stopped outcomes have no continuing world. -/
theorem restoreScope_world (arena : ArenaForm D) (held : List (Res D))
    (entry : World D) (exit : Ausgang V l Γ) :
    (arena.restoreScope held entry exit).welt =
      exit.welt.map (fun world => world.schreibGlob arena.zaehl held (entry.globs arena.zaehl)) := by
  cases exit <;> rfl

/-- The concrete cleanup instruction selects the saved, typed cursor from
    the environment. It needs the ordinary arena write and guard premises. -/
def restoreScopeStmt (arena : ArenaForm D) {held : List (Res D)}
    (writable : V.gschreibt arena.zaehl = true) (guard : gdarf D arena.zaehl held) :
    Stmt D V l (D.gtyp arena.zaehl :: Γ) held held :=
  .assignGlob arena.zaehl (.var .here) writable guard

theorem restoreScopeStmt_exec (arena : ArenaForm D) {held : List (Res D)}
    (writable : V.gschreibt arena.zaehl = true) (guard : gdarf D arena.zaehl held)
    (oracle : Orakel D) (passes : Nat)
    (call : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (entry world : World D) (locals : Env D Γ) :
    execStmt oracle passes call (arena.restoreScopeStmt (l := l) (Γ := Γ) writable guard)
        world (.cons (entry.globs arena.zaehl) locals) =
      .ok (world.schreibGlob arena.zaehl held (entry.globs arena.zaehl))
        (.cons (entry.globs arena.zaehl) locals) := by
  cases world
  rfl

/-- Restoring a checkpoint neither clears nor copies payload slots.
    The sole recorded write is to the cursor. -/
theorem restoreScope_storage (arena : ArenaForm D) (held : List (Res D))
    (entry : World D) (exit : Ausgang V l Γ) {world : World D} (out : exit.welt = some world) :
    ∃ restored, (arena.restoreScope held entry exit).welt = some restored ∧
      arena.stand restored = arena.stand entry ∧ restored.slots = world.slots ∧
      (∀ other, other ≠ arena.zaehl → restored.globs other = world.globs other) ∧
      restored.spur = .gzugriff arena.zaehl true held world.haelt :: world.spur := by
  refine ⟨world.schreibGlob arena.zaehl held (entry.globs arena.zaehl), ?_, ?_, rfl, ?_, rfl⟩
  · rw [restoreScope_world, out]
    rfl
  · exact arena.stand_schreibGlob world held (entry.globs arena.zaehl)
  · intro other different
    simp only [World.schreibGlob, World.storeGlob, World.merke, dif_neg different]

/-- The discarded suffix cannot be inside the restored allocation prefix.
    Source admission must still prove that its handles do not escape. -/
theorem restoreScope_excludes_suffix (arena : ArenaForm D) (held : List (Res D))
    (entry : World D) (exit : Ausgang V l Γ) {world restored : World D}
    (out : exit.welt = some world) (closed : (arena.restoreScope held entry exit).welt = some restored)
    (index : Int) (allocatedHere : arena.stand entry ≤ index) :
    ¬ index < arena.stand restored := by
  obtain ⟨after, same, checkpoint, _⟩ := arena.restoreScope_storage held entry exit out
  have equal : after = restored := Option.some.inj (same.symm.trans closed)
  rw [← equal, checkpoint]
  omega

/-- Ordinary fallthrough inhabits the cleanup premises for every entry
    context and every body world. -/
theorem restoreScope_erfuellbar (arena : ArenaForm D) (held : List (Res D))
    (entry world : World D) (locals : Env D Γ) :
    ∃ exit : Ausgang V l Γ, exit.welt = some world ∧
      (arena.restoreScope held entry exit).welt =
        some (world.schreibGlob arena.zaehl held (entry.globs arena.zaehl)) :=
  ⟨.ok world locals, rfl, rfl⟩

end Gabbro.Grammatik.ArenaForm
