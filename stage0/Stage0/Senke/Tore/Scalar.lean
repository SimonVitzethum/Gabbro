/- Joint scalar-register and internal-pointer-marker witnesses for foreign argument lowering. -/
module
public import Stage0.Senke.Anweisung.Bindung.TorLauf
public import Runner.Prog.IRAsm
public import Grammatik.Parser.Elab.UebersetzeAllg
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


namespace Gabbro.Stage0.Senke.ForeignScalarProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR Runner.Mem
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def unit : UProg := {
  tabs := [{name := "Bytes", count := 4, cols := [("byte", (0, 255))]}]
  locks := []
  fns := [] }
abbrev D := declOf unit

def layout : Lay D where
  col _ _ := 2048
  ga g := nomatch g
  lo := 2048
  hi := 2080
  tor _ := none
  byte _ := none

def world : World D where
  slots t _ f := by
    obtain ⟨t, ht⟩ := t
    have : t = 0 := by change t < 1 at ht; omega
    subst t
    obtain ⟨f, hf⟩ := f
    have : f = 0 := by change f < 1 at hf; omega
    subst f
    exact ⟨0, by decide, by decide⟩
  globs g := nomatch g
  spur := []

def environment : Env D [.ptr (.table 0 (true, false))] := .cons () .nil

def arguments : Args D [.ptr (.table 0 (true, false))] [] [.ptr (.table 0 (true, false)), .int 42 42, .bool] :=
  .cons (.var .here) (.cons (.lit 42) (.cons .tru .nil))

def code : List II := [ci 1 9 42 0, ci 1 10 1 0]

def memory : Runner.Mem where
  b a := if a.toNat = 1088 then 99 else ((code.flatMap (fun i => Runner.Prog.insB i.o i.a i.b i.c))[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem frame : FrameOK memory 1024 32 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem world_at : WeltAt memory layout world := by
  refine ⟨?_, (fun g => nomatch g), fun _ _ _ => rfl⟩
  intro t f k hk
  obtain ⟨t, ht⟩ := t
  have : t = 0 := by change t < 1 at ht; omega
  subst t
  obtain ⟨f, hf⟩ := f
  have : f = 0 := by change f < 1 at hf; omega
  subst f
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by change (k : Int) < 4 at hk; omega
  rcases this with rfl | rfl | rfl | rfl <;>
    apply ValueAt.of_enc (by rfl) (w := 0)
  all_goals first | decide +kernel +revert | rfl

theorem environment_at : EnvAt layout memory 1024 environment := by
  intro τ x
  cases x with
  | here =>
    apply ValueAt.of_enc (by rfl) (w := 0)
    · decide +kernel
    · rfl
  | there x => nomatch x

theorem pre [Kern] : PreS layout memory 0 1024 32 8 code environment := by
  refine ⟨by decide, by decide, frame, ?_, by unfold CodeFar; decide +kernel,
    environment_at, trivial, wstab_true _ _⟩
  intro k hk
  have : k = 0 ∨ k = 1 := by change k < 2 at hk; omega
  rcases this with rfl | rfl <;> constructor <;> decide +kernel +revert

end Gabbro.Stage0.Senke.ForeignScalarProbe
