module
public import Bruecke.Kette.Quelle
public import Bruecke.Anweisung.Zweig.SchattenZeuge
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.String.Length
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.Repr
import all Init.Data.String.Decode
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
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
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
@[expose] public section

namespace Gabbro.Bruecke.SchattenKetteZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open SchattenZeuge

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def source : String :=
  "module shadowing { impl fn shadow() -> u32 in 0 .. 1 { " ++
  "let mut x : u32 in 0 .. 1 = 1; " ++
  "if true { let x : u32 in 0 .. 0 = 0; } return x; } }"

def program : Programm (declOf unit) :=
  ((lowerAllg unit).toOption.get lowered_some_zeuge).1

def functions : List (declOf unit).Fn :=
  ((lowerAllg unit).toOption.get lowered_some_zeuge).2

theorem lowered : lowerAllg unit = .ok (program, functions) :=
  except_ok_get lowered_some_zeuge

/-- The source anchor includes parsing, elaboration and the actual canonical lowering. -/
theorem translated : uebersetzeAllg source = .ok ⟨unit, program, functions⟩ := by
  kernel_rfl

/-- O43 is discharged on the actual lowered contract, including the live self-signature.
    Neither contract component is assumed to be trivial. -/
theorem interfaces : SchnittstellenPflicht unit := by
  intro P fs hlow c n hf
  have hc : c = ⟨0, (by decide)⟩ := by
    apply Fin.ext
    have hb : c.val < 1 := c.isLt
    show c.val = 0
    omega
  subst c
  have hn : n = 0 := by
    have hb := passtAt_lt unit ⟨0, (by decide)⟩ n hf
    have hl : (sigFns unit).length = 1 := by kernel_rfl
    rw [hl] at hb
    omega
  subst n
  have hp : program = P := congrArg Prod.fst (Except.ok.inj (lowered.symm.trans hlow))
  subst P
  constructor
  · intro s0 ρ _
    kernel_change (true = true)
    rfl
  · intro s0 s1 ρ v _ _
    kernel_change (true = true)
    rfl

theorem duties : ∀ c : Fin unit.fns.length, ∃ bs,
    zuBodyZ unit (fnAt unit c) = some bs ∧ meetsU unit (wfU unit) (fnAt unit c) bs := by
  intro c
  have hc : c = ⟨0, (by decide)⟩ := by
    apply Fin.ext
    have hb : c.val < 1 := c.isLt
    show c.val = 0
    omega
  subst c
  exact ⟨body, translation_zeuge, routine_meets_zeuge⟩

/-- An integer type by itself is insufficient: index and missing kinds remain protected. -/
theorem kind_admission_zeuge :
    bindFrischB { routine with params := [("x", .int 0 1)], kinds := [.int] } = true ∧
      bindFrischB { routine with params := [("x", .int 0 1)], kinds := [.index 0] } = false ∧
      bindFrischB { routine with params := [("x", .int 0 1)], kinds := [] } = false := by
  decide +kernel

theorem all_duties : PflichtenAlle source :=
  ⟨unit, uOf_eq translated, (by decide +kernel), (by decide +kernel),
    (by decide +kernel), (by decide +kernel), (by decide +kernel), interfaces, duties⟩

theorem carried_duties : PflichtenTeilG source (u := unit) (fun _ => True) := by
  refine ⟨uOf_eq translated, (by decide +kernel),
    getragenG_of_bools (by decide +kernel) (by decide +kernel) (by decide +kernel),
    (by decide +kernel), fun P fs hlow c _ => interfaces P fs hlow c,
    fun c _ => duties c, ?_⟩
  intro c hc
  exact (hc True.intro).elim

/-- All three premises of the final source-chain theorem hold together on the shadowing
    function: source duties, open-start duties and successful translation. -/
theorem nutzer_aus_quelleG_schatten_zeuge :
    PflichtenTeilG source (u := unit) (fun _ => True) ∧
      (∀ hn : nullB unit = true, OffeneStartPflicht unit (fun _ => True) program hn) ∧
      uebersetzeAllg source = .ok ⟨unit, program, functions⟩ ∧
      ∃ hn : nullB unit = true, Zielsatz.NutzerPflicht (einheitAllg unit program hn) := by
  have hStart : ∀ hn : nullB unit = true,
      OffeneStartPflicht unit (fun _ => True) program hn :=
    fun _ _ _ hc => (hc True.intro).elim
  exact ⟨carried_duties, hStart, translated,
    nutzer_aus_quelleG carried_duties hStart translated⟩

#print axioms nutzer_aus_quelleG_schatten_zeuge

end Gabbro.Bruecke.SchattenKetteZeuge
