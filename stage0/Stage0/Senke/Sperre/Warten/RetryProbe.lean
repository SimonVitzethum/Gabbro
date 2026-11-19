/- Real encoded memory witnesses for the CAS miss and the acquired branch. -/
module
public import Stage0.Senke.Sperre.Warten.Fixture
@[expose] public section

namespace Gabbro.Stage0.Senke.WartenProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
set_option maxRecDepth 100000
variable [Kern]

/-- A stale expected ticket zero and its successor one, while next is one.
    These are actual frame bytes, not an abstract slot function premise. -/
def missMemory : Mem :=
  write (write (write (memory false) (slot 4096 5) 8 8192)
    (slot 4096 6) 8 0) (slot 4096 7) 8 1

end Gabbro.Stage0.Senke.WartenProbe
