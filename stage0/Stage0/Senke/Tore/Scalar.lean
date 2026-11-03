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
  rcases this with rfl | rfl | rfl | rfl <;> exact ⟨0, by decide +kernel +revert, rfl⟩

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

/-- The initial request pointer word is 99, while the canonical environment marker is zero.
    Scalar values are still copied and checked in the same concrete memory. -/
theorem lowR_ok_zeuge [Kern] :
    lowR layout arguments 8 = some (code, 11) ∧
    EnvAt layout memory 1024 environment ∧
    memory.rd64 (slot 1024 (BitVec.ofNat 64 8)) = some 99 ∧
    ¬ Enc layout (.ptr (.table 0 (true, false))) () 99 ∧
    ∃ m', Star ⟨0, 1024⟩ memory ⟨32, 1024⟩ m' ∧
      Agree 1024 8 32 memory m' ∧
      ArgsW layout (fun j => rdW m' 1024 (8 + j)) (evalArgs world arguments world environment) := by
  have emitted : lowR layout arguments 8 = some (code, 11) := by decide +kernel
  have lay : LayIn layout := by
    refine ⟨?_, (fun g => nomatch g), by decide⟩
    intro t f k hk
    obtain ⟨t, ht⟩ := t
    have : t = 0 := by change t < 1 at ht; omega
    subst t
    change (k : Int) < 4 at hk
    change 2048 ≤ 2048 + 8 * k ∧ 2048 + 8 * k + 8 ≤ 2080
    omega
  obtain ⟨m', steps, changed, values⟩ := lowR_ok (same := rfl) world world (fun _ h => h) lay
    arguments 8 code 11 emitted (by decide) (by decide) memory 0 environment
    (PreS.welt pre (Nat.le_refl _) world_at lay (by decide))
  refine ⟨emitted, environment_at, by decide +kernel, (by change ¬ (99 : Runner.W) = 0; decide +kernel), m', ?_, changed, values⟩
  rw [show (0 : Runner.W) + BitVec.ofNat 64 (16 * code.length) = (32 : Runner.W) by decide +kernel] at steps
  exact steps

theorem wide_foreign_values_refused_zeuge :
    wortTy (.int 0 (2 ^ 64)) = false ∧
    chkC (some (.int 0 (2 ^ 64))) 8 = none ∧
    lowR layout (.cons (.lit (2 ^ 64)) .nil : Args D [] [] [.int (2 ^ 64) (2 ^ 64)]) 8 = none := by
  decide +kernel

theorem scalar_register_domain_zeuge :
    wortTy (.int 0 (2 ^ 64 - 1)) = true ∧
    (chkC (some (.int (-2 ^ 63) (2 ^ 63 - 1))) 8).isSome = true ∧
    (chkC (some .bool) 8).isSome = true := by decide +kernel

end Gabbro.Stage0.Senke.ForeignScalarProbe
