module
public import Stage0.SourceWitness
@[expose] public section

namespace Gabbro.Stage0.ResetWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

/-- Exercise the source frontend, canonical range expansion and complete IR emitter. -/
def text : String :=
  "module reset_probe { static mut A : [u8; 4] = 0; impl fn main() -> u64 in 0 .. 100 effects { writes A } { reset A at 1 count 2; return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 64 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

/-- The canonical range check must reject a range extending past the array. -/
def outside : String :=
  "module reset_probe { static mut A : [u8; 4] = 0; impl fn main() -> u64 in 0 .. 100 effects { writes A } { reset A at 3 count 2; return 23; } }"

theorem outside_refused : (emit outside 64).toOption.isSome = false := by decide +kernel

end Gabbro.Stage0.ResetWitness
