/- Joint source/start/image witnesses. These are fixtures for the lead's integration checks. -/
module
public import Stage0.IRBild
meta import Stage0.IRBild
@[expose] public section

namespace Gabbro.Stage0.Senke.StartupProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

def text : String :=
  "module startup { impl fn worker(i : u32 in 0 .. 9, b : bool) effects { pure } { } impl fn main() -> u32 in 0 .. 9 effects { pure } { return 3; } concurrent { worker(7, true), worker(2, false) }; }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 64 := candidate.toOption.get candidate_present

/-- The exact same function has two source identities, typed environments and initialized
    frames. Neither a names-only set nor one environment per function can satisfy this fixture. -/
theorem source_frames_zeuge :
    output.starts.length = 2 ∧ output.image.roots.map Fin.val = [0, 0] ∧
    output.image.rootArgs = [[1, 7], [0, 2]] ∧
    output.startPlan.concurrent.map (fun source => source.sourceArgs) =
      [[.lit 7, .tru], [.lit 2, .fls]] := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  rfl

theorem source_identity_zeuge :
    output.startPlan.concurrent.map (fun source => (source.path, source.sourceArgs)) =
      StartArgument.sourceIdentities (uMembers (pre108 output.compiled.source.prepared.elaborierbar)) :=
  output.starts_source

theorem image_start_zeuge [Runner.IR.Kern] [CloneOK] : output.Correct := output.correct

def wideText : String :=
  "module startup { impl fn worker(i : u128 in 0 .. 18446744073709551617) effects { pure } { } impl fn main() effects { pure } { } concurrent { worker(18446744073709551617), worker(2) }; }"

def wideCandidate : Except String (Emitted wideText 64) := emit wideText 64

theorem wide_candidate_present : wideCandidate.toOption.isSome = true := by decide +kernel

def wideOutput : Emitted wideText 64 := wideCandidate.toOption.get wide_candidate_present

/-- The highest argument limb reaches each separate initialized frame; the shared width
    determines both the argument span and the scratch boundary. -/
theorem complete_words_zeuge :
    wideOutput.image.rootArgs = [[1, 1], [2, 0]] ∧ wideOutput.starts.length = 2 := by
  decide +kernel

theorem wide_image_start_zeuge [Runner.IR.Kern] [CloneOK] : wideOutput.Correct := wideOutput.correct

def namedSpaceText : String :=
  "module startup { table T count 2 owner sharedData { slot { v : u32 in 0 .. 9, } } impl fn worker(p : ptr<sharedData, r> T, i : u32 in 0 .. 9) effects { pure } { } impl fn main() effects { pure } { } concurrent { worker(&T, 7), worker(&T, 2) }; }"

def namedSpaceCandidate : Except String (Emitted namedSpaceText 64) := emit namedSpaceText 64

theorem named_space_candidate_present : namedSpaceCandidate.toOption.isSome = true := by decide +kernel

def namedSpaceOutput : Emitted namedSpaceText 64 :=
  namedSpaceCandidate.toOption.get named_space_candidate_present

/-- Nonzero nominal spaces retain the zero-marker ABI; the distinct source arguments
    still initialize two separate occurrences of the same typed function. -/
theorem named_space_frames_zeuge :
    namedSpaceOutput.compiled.unit.spaces = ["normal", "sharedData"] ∧
    namedSpaceOutput.image.roots.map Fin.val = [0, 0] ∧
    namedSpaceOutput.image.rootArgs = [[7, 0], [2, 0]] ∧
    namedSpaceOutput.startPlan.concurrent.map (fun source => source.sourceArgs) =
      [[.fnref "T", .lit 7], [.fnref "T", .lit 2]] := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  rfl

theorem named_space_image_start_zeuge [Runner.IR.Kern] [CloneOK] :
    namedSpaceOutput.Correct := namedSpaceOutput.correct

/-- Stack positions are occurrence identities, even when the function identity repeats. -/
theorem separate_frames_zeuge :
    output.image.fp0 + 8 * output.image.Ks + 8 * output.image.Ks ≤
      output.image.fp0 + 8 * output.image.Ks * 2 := by
  simpa only [Nat.mul_one] using startStackBytes_disjoint output.image.fp0 output.image.Ks 1 2 (by decide)

def layoutUnit : UProg := {
  tabs := [], locks := [], fns := [{
    name := "worker", params := [("i", .int 0 9), ("b", .bool)], kinds := [.int, .bool],
    res := none, held := [], puts := [], gives := [], body := [], ret := .empty }] }

abbrev D := declOf layoutUnit
def worker : D.Fn := ⟨0, by decide⟩

/-- A nonempty parameter span and a root stack force K > Ks. The world starts after
    both stacks, so swapping Ks and K cannot accidentally pass the image guard. -/
def layout : Lay D where
  col t := Fin.elim0 t
  ga g := Fin.elim0 g
  lo := codeBase + 8 * 128
  hi := codeBase + 8 * 128
  tor a := Fin.elim0 a
  byte t := Fin.elim0 t
  sye := codeBase + 8 * 128

theorem image_guard_unequal_zeuge :
    BildGut D worker [worker] [0] [([], 1)] codeBase 64 128 layout [] ∧
    ¬ BildGut D worker [worker] [0] [([], 1)] codeBase 128 64 layout [] := by
  decide +kernel

/-- Ordinary unsupported startup arguments retain the canonical refusal. -/
theorem out_of_range_zeuge :
    (emit "module startup { impl fn worker(i : u32 in 0 .. 9) { } impl fn main() { } concurrent { worker(10) }; }" 64).isOk = false := by
  decide +kernel

#print axioms source_identity_zeuge
#print axioms image_start_zeuge
#print axioms image_guard_unequal_zeuge
end Gabbro.Stage0.Senke.StartupProbe
