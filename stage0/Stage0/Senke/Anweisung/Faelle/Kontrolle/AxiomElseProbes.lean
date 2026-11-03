/- One axiom, one reason, and distinct success/error continuations. -/
module
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.ControlProbes
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.AxiomElse
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

namespace Gabbro.Stage0.Senke.AxiomElseProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Every fixture has exactly one foreign call site and one reason. -/
def u (result : Option Ty) : UProg := { ControlProbe.u with
  axs := [{name := "gate", params := [], kinds := [], res := result, gruende := 1}] }
abbrev D (result : Option Ty) := declOf (u result)
abbrev entry (result : Option Ty) : (D result).Fn := ⟨0, by decide⟩
abbrev gate (result : Option Ty) : (D result).Ax := ⟨0, by decide⟩

def retN (result : Option Ty) {Γ : Ctx} (n : Int) (hl : 0 ≤ n) (hh : n ≤ 100) :
    Endblock (D result) (vertragVon (D result) (entry result)) false Γ [] :=
  .ret (.val (.widen hl hh (.lit n))) (.refl [])

/-- The handler reads its bound reason before returning a distinct result. -/
def handler (result : Option Ty) {Γ : Ctx} :
    Endblock (D result) (vertragVon (D result) (entry result)) false (.why 1 :: Γ) [] :=
  .cons (.onWhy (.var .here)
    (.cons (.cons (.ret (.val (.widen (by decide) (by decide) (.lit 9))) (.refl [])) .nil) .nil))
    (retN result 99 (by decide) (by decide))

def statement (result : Option Ty) {Γ : Ctx} :
    Stmt (D result) (vertragVon (D result) (entry result)) false Γ [] [] :=
  .axiomCallElse result (gate result) .nil rfl
    { hw := fun t => Fin.elim0 t
      hg := fun g => Fin.elim0 g
      hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
      hh := fun l => Fin.elim0 l }
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (by decide) (handler result)

/-- Success must preserve an existing local; no discarded result shadows it. -/
def body (result : Option Ty) :
    Endblock (D result) (vertragVon (D result) (entry result)) false [] [] :=
  .bind (.lit 23) (.cons (statement result)
    (.ret (.val (.widen (by decide) (by decide) (.var .here))) (.refl [])))

/-- The same statement also continues through `Block.cons` inside an `ite`. -/
def nestedBody (result : Option Ty) :
    Endblock (D result) (vertragVon (D result) (entry result)) false [] [] :=
  .bind (.lit 23) (.cons (.ite .tru (.cons (statement result) .nil) .nil)
    (.ret (.val (.widen (by decide) (by decide) (.var .here))) (.refl [])))

def program (result : Option Ty) (nested : Bool) : Programm (D result) where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact if nested then nestedBody result else body result

def binding : TorB := ⟨1, [none, none, none, none, none, none], [(-9, 0)]⟩

def image (result : Option Ty) (nested : Bool) : Except String (List Runner.B) := do
  let b ← bild 1 (program result nested) (layU (u result) (fun _ => some binding))
    [entry result] Fin.val (fun _ => "main") (entry result) .nil [] 1024 0
  pure b.bytes

def initial (result : Option Ty) : World (D result) where
  slots t := Fin.elim0 t
  globs g := Fin.elim0 g
  spur := []

/-- The oracle uses exactly the packing supplied by the gate's errno binding. -/
def oracle (result : Option Ty) (reason : Bool) : Orakel (D result) where
  wirkt _ σ _ := (σ, rohW binding 1 (if reason then BitVec.ofInt 64 (-9) else 7))
  regLies r := Fin.elim0 r
  regSchreib r := Fin.elim0 r
  sichtbar _ _ := true

def calls (result : Option Ty) (f : (D result).Fn) (_ : World (D result))
    (_ : Env (D result) ((D result).params f)) : RufAusgang f := .logik .schleife

/-- This observes canonical machine-G semantics, not an additional execution backend. -/
def observed (result : Option Ty) (nested reason : Bool) : Int :=
  match execEnd (oracle result reason) 1 (calls result)
      (if nested then nestedBody result else body result) (initial result) .nil with
  | .zurueck _ v => v.n
  | _ => -1

/-- Both value-discarding and VOID statements lower in complete, nonempty images,
    through ordinary blocks as well as the function's end block. -/
theorem stmtAxiomElse_case_zeuge :
    (image (some (.int 0 10)) false).isOk = true ∧
    (image (some (.int 0 10)) true).isOk = true ∧
    (image none false).isOk = true ∧ (image none true).isOk = true ∧
    (image (some .bool) false).isOk = true ∧ (image (some .bool) true).isOk = true := by
  decide +kernel

/-- Each compiled fixture has both live outcomes: success keeps local 23, and the
    bound reason reaches return 9 instead of the success or handler fallthrough. -/
theorem stmtAxiomElse_paths_zeuge :
    observed (some (.int 0 10)) false false = 23 ∧
    observed (some (.int 0 10)) false true = 9 ∧
    observed (some (.int 0 10)) true false = 23 ∧
    observed (some (.int 0 10)) true true = 9 ∧
    observed none false false = 23 ∧ observed none false true = 9 ∧
    observed none true false = 23 ∧ observed none true true = 9 ∧
    observed (some .bool) false false = 23 ∧ observed (some .bool) false true = 9 ∧
    observed (some .bool) true false = 23 ∧ observed (some .bool) true true = 9 := by
  decide +kernel

/-- Refusals describe unsupported profiles, rather than refusing the entire
    statement constructor now that integer and VOID profiles are connected. -/
def lowered (result : Option Ty) (selected : Option TorB) : Option (List II × Nat) :=
  lowS 1 (fun _ => 0) (layU (u result) (fun _ => selected) 0)
    (functionFrame (program result false) (entry result)) ([], 0) [] (0, 0)
    (statement result (Γ := []))

/-- In particular, a reason outside the declared channel remains an error even
    though the same statement lowers with its valid one-reason binding. -/
theorem stmtAxiomElse_refused_zeuge :
    (lowered (some (.int 0 10)) (some binding)).isSome = true ∧
    (lowered none (some binding)).isSome = true ∧
    lowered (some (.int 0 10)) none = none ∧
    lowered none (some { binding with fehler := [(-9, 1)] }) = none ∧
    lowered (some (.int (-10) 10)) (some binding) = none ∧
    (lowered (some .bool) (some binding)).isSome = true := by
  decide +kernel

end Gabbro.Stage0.Senke.AxiomElseProbe
