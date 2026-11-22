module
public import Bruecke.Kette.Bild
@[expose] public section

/-!
# The premises of `nutzerA_aus_compiled` hold jointly, with a carried function

An instance in which the form occurs: a unit of one function `main` that returns `42`, with no
lock and no foreign body. Its unit checks are decided, its Body reading is computed, and its
duty `meetsU` is proved: the duties the generator states are provable, not vacuous. The two
run facts of the theorem (`c.unit = u`, `ohneAltGlobalB c.expanded`) are facts of a Stage 0 run
and are not instantiated here.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The one function: `impl fn main() -> u8 { return 42; }`. -/
def mainErfuellbar : UFn :=
  { name := "main", params := [], kinds := [], res := some (0, 255), held := [], puts := [],
    gives := [], body := [], ret := .val (.lit 42) }

/-- The unit of that function: no table, no lock, no foreign body, no static. -/
def einheitErfuellbar : UProg :=
  { tabs := [], locks := [], fns := [mainErfuellbar], axs := [], guests := [], annahmen := [],
    whys := [], sums := [], gestartet := [], roots := [], hands := [], globs := [], regs := [],
    invs := [], zustaende := [], regiert := [], ptrs := [], ptrKeys := [], exportGate := Except.ok (),
    records := [], checks := [], marken := [], spaces := ["normal"], eigner := [], markOrders := [] }

/-- **The premises hold jointly**: the unit's duties, with its function carried and its duty
    proved, no lock, no foreign body. -/
theorem nutzerA_aus_compiled_erfuellbar :
    ∃ u : UProg, PflichtenEinheit u ∧ u.locks = [] ∧ u.axs = [] := by
  refine ⟨einheitErfuellbar, ⟨⟨by with_unfolding_all decide, by with_unfolding_all decide,
    by with_unfolding_all decide⟩, fun _ => 0, ?_⟩, rfl, rfl⟩
  intro f hf
  have hf' : f = mainErfuellbar := by
    simpa only [einheitErfuellbar, List.mem_singleton] using hf
  subst hf'
  refine ⟨by with_unfolding_all decide, by with_unfolding_all decide, by with_unfolding_all decide,
    [.ret (some (.lit (.int 42)))], by with_unfolding_all rfl, ?_⟩
  intro ρ s hwf _
  refine ⟨s, rfl, ?_⟩
  simp only [postU, ensList, mainErfuellbar, resultClause, Gabbro.Body.finalValue, Gabbro.Body.exec,
    Gabbro.Body.step, Gabbro.Body.eval, chain, Option.toList, List.append_nil, Option.map_some,
    Option.getD_some]
  exact ⟨hwf, 42, rfl, by decide, by decide⟩

#print axioms nutzerA_aus_compiled_erfuellbar

end Gabbro.Bruecke
