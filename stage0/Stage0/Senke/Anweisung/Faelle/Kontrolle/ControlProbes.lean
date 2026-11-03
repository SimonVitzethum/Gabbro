/- Nonempty control-flow fixtures, including check forms unavailable in the source reader. -/
module
public import Stage0.Senke.Welt.Anordnung
public import Stage0.IRBild
public import Grammatik.Parser.Cover.Differenz
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


namespace Gabbro.Stage0.Senke.ControlProbe
set_option maxRecDepth 100000

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR

/-- One ordinary function with a bounded integer result. -/
def u : UProg := {
  tabs := [], locks := []
  axs := [{ name := "write", params := [.int 0 100, .int 0 100, .int 0 100], kinds := [.int, .int, .int], res := some (.int 0 4096), gruende := 2 }]
  fns := [{ name := "main", params := [], kinds := [], res := some (0, 100), held := [], puts := [], gives := [], body := [], ret := .val (.lit 0) }]
}
abbrev D := declOf u
abbrev entry : D.Fn := ⟨0, by decide⟩

def retN {Γ : Ctx} (n : Int) (hl : 0 ≤ n) (hh : n ≤ 100) :
    Endblock D (vertragVon D entry) false Γ [] :=
  .ret (.val (.widen hl hh (.lit n))) (.refl [])

def checkBlock (b : Bool) : Block D (vertragVon D entry) false [] [] [] :=
  .check (if b then .tru else .fls) (retN 41 (by decide) (by decide))
    (.cons (.ret (.val (.widen (by decide) (by decide) (.lit 7))) (.refl [])) .nil)

def checkBody (b : Bool) : Endblock D (vertragVon D entry) false [] [] :=
  .cons (.ite .tru (checkBlock b) .nil) (retN 99 (by decide) (by decide))

def narrowEnd (n : Int) : Endblock D (vertragVon D entry) false [] [] :=
  .narrow (.lit n) 3 7 (retN 41 (by decide) (by decide))
    (.ret (.val (.widen (by decide) (by decide) (.var .here))) (.refl []))

def narrowBlock (n : Int) : Block D (vertragVon D entry) false [] [] [] :=
  .narrow (.lit n) 3 7 (retN 41 (by decide) (by decide))
    (.cons (.ret (.val (.widen (by decide) (by decide) (.var .here))) (.refl [])) .nil)

/-- A value resumes the enclosing block; a listed errno returns from the function. -/
def gateBlock (fd : Int) (hl : 0 ≤ fd) (hh : fd ≤ 100) :
    Block D (vertragVon D entry) false [] [] [] :=
  .bindAxiomElse ⟨0, by decide⟩
    (.cons (.widen hl hh (.lit fd))
      (.cons (.widen (by decide) (by decide) (.lit 0))
        (.cons (.widen (by decide) (by decide) (.lit 0)) .nil)))
    rfl (by decide) (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
    (retN 9 (by decide) (by decide)) (.bind (.add (.var .here) (.lit 3)) .nil)

def programOf (body : Endblock D (vertragVon D entry) false [] []) : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact body

def initial : World D where
  slots t := Fin.elim0 t
  globs g := Fin.elim0 g
  spur := []

def gateBinding : TorB :=
  ⟨1, [some 0, some 1, some 2, none, none, none], [(-9, 0), (-4, 1)]⟩

def imageOf (body : Endblock D (vertragVon D entry) false [] []) : Except String (List Runner.B) := do
  let b ← bild 1 (programOf body) (layU u (fun _ => some gateBinding)) [entry] Fin.val (fun _ => "main") entry .nil [] 1024 0
  pure b.bytes

def blockImageOf (body : Block D (vertragVon D entry) false [] [] []) : Except String (List Runner.B) :=
  imageOf (.cons (.ite .tru body .nil) (retN 99 (by decide) (by decide)))

/-- The true and false fixtures each lower as complete nonempty programs. -/
theorem blockCheck_case_zeuge :
    (imageOf (checkBody true)).isOk = true ∧ (imageOf (checkBody false)).isOk = true := by
  decide +kernel

/-- All four range directions instantiate the end-block lowering. -/
theorem endNarrow_case_zeuge :
    [2, 3, 7, 8].all (fun n => (imageOf (narrowEnd n)).isOk) = true := by
  decide +kernel

/-- The same four directions instantiate the ordinary block lowering. -/
theorem blockNarrow_case_zeuge :
    [2, 3, 7, 8].all (fun n => (blockImageOf (narrowBlock n)).isOk) = true := by
  decide +kernel

/-- Both hardware branches have ordinary complete image witnesses. -/
theorem blockAxiomElse_case_zeuge :
    (blockImageOf (gateBlock 1 (by decide) (by decide))).isOk = true ∧
    (blockImageOf (gateBlock 99 (by decide) (by decide))).isOk = true := by
  decide +kernel

/-- Both terminating and ordinary blocks accept signed-word boundaries that
    cannot be encoded in one instruction immediate. The continuation is nonempty. -/
def wideNarrowEnd : Endblock D (vertragVon D entry) false [] [] :=
  .narrow (.lit 7) (-2^63) (2^63-1) (retN 41 (by decide) (by decide))
    (retN 7 (by decide) (by decide))

theorem wideNarrow_case_zeuge :
    (imageOf wideNarrowEnd).isOk = true ∧
    (blockImageOf (.narrow (.lit 7) (-4294967296) 4294967296
      (retN 41 (by decide) (by decide)) .nil)).isOk = true := by
  decide +kernel

/-- A source value beyond the signed word takes the ordinary error branch;
    its representable multiword encoding no longer refuses compilation. -/
theorem wide_source_narrow_zeuge :
    (imageOf (narrowEnd (2^63))).isOk = true ∧
    (blockImageOf (narrowBlock (-(2^80)))).isOk = true := by
  decide +kernel

end Gabbro.Stage0.Senke.ControlProbe

namespace Gabbro.Stage0.Senke

/-- Both materialization branches occur on jointly representable word counts. -/
theorem travCountC_zeuge :
    travCountSize 10 = 1 ∧ travCountSize 4294967296 = 17 ∧
    (travCountC 6 10).length = 1 ∧
    (travCountC 6 4294967296).length = 17 := by
  decide +kernel

end Gabbro.Stage0.Senke

namespace Gabbro.Stage0.Senke.WideTraverseProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR

/-- The canonical model permits a fieldless table; source export currently refuses it. -/
def u : UProg := { ControlProbe.u with
  tabs := [{name := "logical", count := 4294967296, cols := []}] }
abbrev D := declOf u
abbrev entry : D.Fn := ⟨0, by decide⟩
abbrev table : D.Tab := ⟨0, by decide⟩

def body : Endblock D (vertragVon D entry) false [] [] :=
  .cons (.traverse table .tru (.cons (.leave rfl) .nil))
    (.ret (.val (.widen (by decide) (by decide) (.lit 17))) (.refl []))

def program : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact body

/-- Zero storage does not replace the declared traversal count with zero. -/
theorem fieldless_table_layout_zeuge :
    D.count table = 4294967296 ∧ tabSz u table = 0 ∧ IsEmpty (D.Feld table) := by
  exact ⟨rfl, (fieldless_table_layout u table rfl).2⟩

local instance : DecidableEq D.Fn :=
  inferInstanceAs (DecidableEq (Fin u.fns.length))

/-- The canonical checker accepts this exact large-count, fieldless program.
    Source export can preserve it without introducing a replacement source rule. -/
theorem traverse_wide_checker_zeuge :
    Gabbro.Grammatik.Zielsatz.AkzeptiertX program
      (Gabbro.Grammatik.Parser.Cover.Differenz.sperrFamilie u)
      [entry] [] [Sum.inl table] [] = true := by
  decide +kernel

/-- A real image witness for the generic wide traversal case. This does not
    claim the missing empty-table source exporter has been implemented. -/
theorem traverse_wide_image_zeuge :
    (bild 1 program (layU u (fun _ => none)) [entry] Fin.val
      (fun _ => "main") entry .nil [] 1024 0).isOk = true := by
  decide +kernel

end Gabbro.Stage0.Senke.WideTraverseProbe

namespace Gabbro.Stage0.Senke.WideTraverseProbe

/-- The real source uses a wide declared count and returns from its first iteration.
    Truncating the count to zero would reach the distinct return value 17 instead. -/
def source : String :=
  "module ir_probe { table t count 4294967296 { slot { } } impl fn main() -> u64 in 0 .. 100 effects { reads t.slots } { traverse i over slots of t by unvisited touches reads t.slots { return 23; } return 17; } }"

def sourceCount : Option Int := do
  let compiled ← (Gabbro.Stage0.compile source).toOption
  let table ← compiled.unit.tabs[0]?
  pure table.count

/-- Canonical source, exact original count and actual IR image are jointly inhabited. -/
theorem traverse_wide_source_zeuge :
    sourceCount = some 4294967296 ∧
    (Gabbro.Stage0.irBild source 1024).isOk = true := by
  decide +kernel

end Gabbro.Stage0.Senke.WideTraverseProbe
