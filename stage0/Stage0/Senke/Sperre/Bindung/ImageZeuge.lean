/- Joint source-to-image witnesses for both checked wait bindings. Evaluation of
   these complete programs belongs to this witness module, off the compiler path. -/
module
public import Stage0.Senke.Sperre.Bindung.Zeuge
import all Init.Data.Int.Repr
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

namespace Gabbro.Stage0.Senke.WaitBindingWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR
set_option maxRecDepth 100000

/-- The same nonempty scoped-lock program under either admitted source profile. -/
def sourceText (environment : String) : String :=
  "profile { environment " ++ environment ++ "; }; " ++
  "module wait_profile { lock L protects { } rank 0; impl fn main() -> u64 in 0 .. 100 effects { locks L } { locks L { } return 23; } }"

def image (environment : String) : Except String (Emitted (sourceText environment) 1024) :=
  emit (sourceText environment) 1024

/-- Both complete production pipelines succeed, including checking, lowering,
    root selection, relocation and initialized-image certification. -/
theorem image_binding_present_zeuge :
    (image "freestanding").toOption.isSome = true ∧
    (image "linux").toOption.isSome = true := by
  decide +kernel

def freestandingImage : Emitted (sourceText "freestanding") 1024 :=
  (image "freestanding").toOption.get image_binding_present_zeuge.1

def linuxImage : Emitted (sourceText "linux") 1024 :=
  (image "linux").toOption.get image_binding_present_zeuge.2

/-- Actual source-selected images contain a lock and have equal code size.
    Linux has four more syscall instructions: one wait and three scoped release
    paths. Startup syscalls occur equally in both images. -/
theorem image_binding_zeuge :
    Profil.imageEnvironment {} freestandingImage.compiled.source.prepared.bindung = .freestanding ∧
    Profil.imageEnvironment {} linuxImage.compiled.source.prepared.bindung = .linux ∧
    0 < freestandingImage.compiled.unit.locks.length ∧
    0 < linuxImage.compiled.unit.locks.length ∧
    freestandingImage.image.code.length = linuxImage.image.code.length ∧
    (linuxImage.image.code.filter fun i => i.o == 23).length =
      (freestandingImage.image.code.filter fun i => i.o == 23).length + 4 := by
  decide +kernel

/-- Inspect the actual emitted function body after the common startup prefix.
    The nonempty freestanding body is syscall-free; Linux contains the wait
    and all three release syscalls in that same source function. -/
theorem image_lock_body_zeuge :
    0 < (freestandingImage.image.code.drop (headLen freestandingImage.image.roots.length)).length ∧
    ((freestandingImage.image.code.drop (headLen freestandingImage.image.roots.length)).all
      fun i => i.o != 23) = true ∧
    ((linuxImage.image.code.drop (headLen linuxImage.image.roots.length)).filter
      fun i => i.o == 23).length = 4 := by
  decide +kernel

/-- The generic production-image binding theorem has jointly satisfiable
    premises for both environments and an actual scoped-lock source program. -/
theorem Emitted_lockWait_zeuge :
    freestandingImage.image.Y.lockWait = .spin ∧ linuxImage.image.Y.lockWait = .futex := by
  constructor
  · rw [freestandingImage.lockWait, image_binding_zeuge.1]
    rfl
  · rw [linuxImage.lockWait, image_binding_zeuge.2.1]
    rfl

def freestandingLock : (declOf freestandingImage.compiled.unit).Lock :=
  ⟨0, image_binding_zeuge.2.2.1⟩

def linuxLock : (declOf linuxImage.compiled.unit).Lock :=
  ⟨0, image_binding_zeuge.2.2.2.1⟩

/-- Instantiate the generic no-syscall theorem at the real emitted lock address;
    the corresponding Linux image retains its wait and wake syscall sites. -/
theorem Emitted_lock_spin_no_syscall_zeuge :
    ((nimmT freestandingImage.image.Y (freestandingImage.image.Y.lk freestandingLock) 4 ++
      gibT freestandingImage.image.Y (freestandingImage.image.Y.lk freestandingLock) 4).all
        fun i => i.o != 23) = true ∧
    (nimmT linuxImage.image.Y (linuxImage.image.Y.lk linuxLock) 4)[26]? =
      some (ci 23 21 14 0) ∧
    (gibT linuxImage.image.Y (linuxImage.image.Y.lk linuxLock) 4)[15]? =
      some (ci 23 21 14 0) := by
  refine ⟨freestandingImage.lock_spin_no_syscall image_binding_zeuge.1 _ 4, ?_, ?_⟩
  · exact (ticket_futex_syscalls _ _ _ Emitted_lockWait_zeuge.2).1
  · exact (ticket_futex_syscalls _ _ _ Emitted_lockWait_zeuge.2).2.1

end Gabbro.Stage0.Senke.WaitBindingWitness
