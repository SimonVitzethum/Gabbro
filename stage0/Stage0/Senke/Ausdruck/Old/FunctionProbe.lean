/- Whole-function witnesses: increment a global, overwrite a slot, and preserve the entry parameter. -/
module
public import Stage0.Senke.Ausdruck.Old.RuntimeProbe
public import Stage0.Senke.Welt.Anordnung
@[expose] public section

namespace Gabbro.Stage0.Senke.OldFunctionProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def unit : UProg := {
  tabs := [{name := "Cells", count := 4, cols := [("value", (0, 10))]}]
  locks := []
  globs := [{name := "G", ty := .wert (.int 0 10), init := 0, var := true}]
  fns := [{name := "increment", params := [("index", .index 4)], kinds := [.wert],
    res := some (0, 10), held := [], puts := ["Cells"], gputs := ["G"],
    gives := [], body := [], ret := .empty}] }
abbrev D := declOf unit
abbrev tab : D.Tab := ⟨0, by decide⟩
abbrev field : D.Feld tab := ⟨0, by decide⟩
abbrev global : D.Glob := ⟨0, by decide⟩
abbrev function : D.Fn := ⟨0, by decide⟩

theorem global_access {Λ : List (Res D)} : gdarf D global Λ := by
  intro w hw
  change w ∈ [] at hw
  cases hw

theorem table_access {Λ : List (Res D)} : darf D tab Λ := by
  intro w hw
  change w ∈ [] at hw
  cases hw

def post : Expr D [.int 0 10, .index 4] [] .bool :=
  .and (.eq (.var .here) (.add (.oldG global global_access) (.lit 1)))
    (.eq (.var .here) (.add (.oldS tab field (.var (.there .here)) table_access) (.lit 1)))

/-- The explicit narrowing fallback is unreachable under G < 10; no type or
    contract guarantee is weakened to make the increment fit its declared range. -/
def body : Endblock D (vertragVon D function) false [.index 4] [] :=
  .cons (.assignGlob global
      (.eng (.add (.glob global global_access) (.lit 1)) 0 10
        (.widen (by decide) (by decide) (.lit 0))) (by decide) global_access)
    (.cons (.assignSlot tab field (.var .here) (.glob global global_access) (by decide) table_access)
      (.cons (.assignVar .here (.widen (by decide) (by decide) (.lit 2)))
        (.ret (.val (.glob global global_access)) (.refl []))))

def program : Programm D where
  invariante i := Fin.elim0 i
  requires _ := .lt (.glob global global_access) (.lit 10)
  ensures f := by
    obtain ⟨f, hf⟩ := f
    have zero : f = 0 := by change f < 1 at hf; omega
    subst f
    exact post
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have zero : f = 0 := by change f < 1 at hf; omega
    subst f
    exact body

def oracle : Orakel D where
  wirkt a := Fin.elim0 a
  regLies r := Fin.elim0 r
  regSchreib r := Fin.elim0 r
  sichtbar _ _ := true

def initial : World D where
  slots t k f := by
    obtain ⟨t, ht⟩ := t
    have zero : t = 0 := by change t < 1 at ht; omega
    subst t
    obtain ⟨f, hf⟩ := f
    have zero : f = 0 := by change f < 1 at hf; omega
    subst f
    exact if k = 2 then ⟨7, by decide, by decide⟩ else ⟨0, by decide, by decide⟩
  globs g := by
    obtain ⟨g, hg⟩ := g
    have zero : g = 0 := by change g < 1 at hg; omega
    subst g
    exact ⟨0, by decide, by decide⟩
  spur := []

def params : Env D (D.params function) := .cons ⟨1, by decide, by decide⟩ .nil

def image : Except String (Bild D) :=
  bild 1 program (layU unit (fun _ => none)) [function] Fin.val (fun _ => "increment")
    function params [] 1024

/-- The real function compiler emits snapshots for G and all four field cells. -/
theorem increment_oldG_zeuge :
    image.isOk = true ∧ (functionFrame program function).snapshotWords = 5 ∧
    oldCells (program.ensures function) =
      [.glob global, .elem tab field 0, .elem tab field 1, .elem tab field 2, .elem tab field 3] := by
  exact ⟨by decide +kernel, rfl, rfl⟩

/-- The canonical model returns 1 after both writes. The body changes index to 2,
    whose entry slot is 7; ensures must continue to use its original index 1. -/
theorem increment_oldS_zeuge :
    (match rufAt program oracle 1 1 function initial params with
    | .ok final value => value.n = 1 ∧ (final.globs global).n = 1 ∧
        (final.slots tab 1 field).n = 1 ∧ (final.slots tab 2 field).n = 7
    | _ => False) ∧
    wahr? (eval initial post initial (.cons ⟨1, by decide, by decide⟩ params)) = true ∧
    wahr? (eval initial post initial
      (.cons ⟨1, by decide, by decide⟩ (.cons ⟨2, by decide, by decide⟩ .nil))) = false := by
  decide +kernel

def current : World D := {initial with globs := fun g => by
  obtain ⟨g, hg⟩ := g
  have zero : g = 0 := by change g < 1 at hg; omega
  subst g
  exact ⟨2, by decide, by decide⟩ }

def currentIndex : Expr D [] [] (.index 4) :=
  .eng (.glob global global_access) 0 3 (.widen (by decide) (by decide) (.lit 0))

def indexedOld : Expr D [] [] (.int 0 10) := .oldS tab field currentIndex table_access

/-- The index follows G = 2 at exit, selecting entry cell 2 = 7, rather than
    following entry G = 0. This catches snapshotting the index value itself. -/
theorem current_index_oldS_zeuge :
    (eval initial indexedOld current .nil).n = 7 ∧
    (eval initial indexedOld initial .nil).n = 0 ∧
    (lowEns (layU unit (fun _ => none) 8192) ⟨[], none, 0, 4, 0⟩ indexedOld 8).isSome = true := by
  decide +kernel

end Gabbro.Stage0.Senke.OldFunctionProbe
