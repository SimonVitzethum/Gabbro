module

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

/-- The space indexes inert address data. Arithmetic and executable operands
    have separate rules; this index never carries authority. -/
inductive AddressSpace where
  | physical
  | virtual
  | port
  | guestPhysical
  | ioVirtual
  deriving DecidableEq, Repr

def AddressSpace.name : AddressSpace → String
  | .physical => "physical"
  | .virtual => "virtual"
  | .port => "port"
  | .guestPhysical => "guest_physical"
  | .ioVirtual => "io_virtual"

end Gabbro.Core.Ast.LowLevel
