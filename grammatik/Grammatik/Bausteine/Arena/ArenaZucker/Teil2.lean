module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Bausteine.Arena.Arena
public import Grammatik.Bausteine.Arena.ArenaZucker.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
namespace ArenaZeuge

theorem zeuge_bump (O : Orakel ZD) (passes : Nat)
    (R : ∀ f : ZD.Fn, World ZD → Env ZD (ZD.params f) → RufAusgang f) :
    ∃ σ' : World ZD,
      execStmt (V := ZV) (l := false) O passes R
          (Stmt.assignGlob Log.zaehl (Block.arenaBump Log) rfl zeuge_gdarf)
          (welt 1 (by decide) (by decide))
          (.cons ⟨2, by decide, by decide⟩ .nil)
        = .ok σ' (.cons ⟨2, by decide, by decide⟩ .nil) ∧
      Log.stand σ' = 3 := by
  obtain ⟨σ', h1, h2⟩ :=
    arenaBump_stand (V := ZV) (l := false) O passes R Log rfl zeuge_gdarf
      (welt 1 (by decide) (by decide)) ⟨2, by decide, by decide⟩ .nil
  exact ⟨σ', h1, by rw [h2]; decide⟩

/-- `arena Log capacity 2 .. 4` on the model side. -/
def kapLog : Arena.Kap := ⟨2, 4⟩

/-- The model arena of generation 0, empty. -/
def arenaLeer : Arena.Arena kapLog 0 := ⟨0, by decide⟩

/-- **The bridge, run:** on the empty witness arena the syntax runs its body exactly while
    `Arena.alloc` returns `some`. -/
theorem zeuge_modell :
    (Log.stand (welt 0 (by decide) (by decide)) < ZD.count Log.tab)
      ↔ Arena.alloc arenaLeer ≠ none :=
  arenaAlloc_gdw_modell Log (welt 0 (by decide) (by decide)) kapLog (by decide)
    arenaLeer (by decide)

end ArenaZeuge

#print axioms eval_umTyp
#print axioms arenaReset_stand
#print axioms arenaBump_stand
#print axioms arenaAlloc_unter_schranke
#print axioms arenaAlloc_an_schranke
#print axioms arenaAlloc_gdw_modell
#print axioms arenaAlloc_bump_modell
#print axioms ArenaZeuge.zeuge_reset
#print axioms ArenaZeuge.zeuge_bump
#print axioms ArenaZeuge.zeuge_modell
#print axioms ArenaZeuge.zeuge_alloc_leer
#print axioms ArenaZeuge.zeuge_alloc_voll
#print axioms ArenaZeuge.zeuge_leer_unter
#print axioms ArenaZeuge.zeuge_voll_an

end Gabbro.Grammatik

/-! CUTS -- what this file does NOT claim.

  * **The generation is not here.** `Arena.lean` carries it as a type index (`Marke g`,
    `ArenaIdx g n`) and a stale index does not typecheck there. In the SYNTAX the
    generation is checker state: `N211` refuses a use of an index bound before a `reset`.
    This file's `reset` is one store, and nothing here forbids reading an older index --
    that refusal is the Rust checker's and is not mirrored in Lean.
  * **The reservation `lo` is not here**, on purpose. It is a static count (`N212`), and
    its only model-side consequence -- the `else` branch cannot run while the counter is
    under the bound -- IS proved (`arenaAlloc_unter_schranke`).
  * **The exporter does not produce these terms.** `gabbro lean-g` refuses an arena
    declaration (`LG001`), so no arena program closes a chain yet. Booked as `TODO.md`
    O14; the form existing is the precondition for that work, not a substitute for it.
  * **`Arena.lookup` returns the slot POSITION, not a stored value** (`Arena.lean`'s own
    cuts), so the bridge in section 5 is about the counter and the index, not about
    content.
-/
